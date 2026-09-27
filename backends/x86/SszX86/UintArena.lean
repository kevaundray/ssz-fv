import SszX86.UintArenaMemory

namespace SszX86.UintCodec.Arena

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Resource outcomes at the two actual native frontiers. Failure stops before
the scratch-error stores. Success stops before the first packing-loop CMP. -/
def Post (s : MachineData) (base : Int64) (count : Nat)
    (address capacity used : BitVec 64) (st : MachineState) : Prop :=
  Frame s st.1 ∧
  ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
      (SszNative.Arena.wordsForBytes count) = none ∧
      st.2 = base + 2918 ∧ st.1.dmem = s.dmem) ∨
    ∃ r, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
      (SszNative.Arena.wordsForBytes count) = some r ∧
      r.pointer = address.toNat + SszNative.Arena.start address.toNat used.toNat ∧
      r.used = SszNative.Arena.finish address.toNat used.toNat
        (SszNative.Arena.wordsForBytes count) ∧
      st.2 = base + 5647 ∧ ∃ flags, st.1 = packingState s count address used flags)

private theorem word_eq_nat (a : BitVec 64) (n : Nat) (h : a.toNat = n) :
    a = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Complete Large preparation and reservation. The input may have any natural
width, and the arena triple need not satisfy `Arena.Valid`: every checked
addition and the final capacity guard is represented by the exact pure model.

Only the three arena header words need be mapped. The source/output/stack are
not accessed by this prefix. The source's nonwrapping range and length bound
are stated explicitly for composition with the byte-trim and packing proofs.
The executable is external to `MachineData`, so the same `CodeAt e base` is
available unchanged to either continuation. -/
theorem reservation_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : Nat) (address capacity used : BitVec 64)
    (header : Header s address capacity used)
    (hcount : 9 ≤ count) (hlen : count ≤ s.regs.r14.toBitVec.toNat)
    (hinput : s.regs.r14.toBitVec.toNat < 2^63)
    (_hsource : s.regs.rdx.toBitVec.toNat + s.regs.r14.toBitVec.toNat ≤ 2^64)
    (ht : s.regs.r10.toBitVec = BitVec.ofNat 64 (count - 1))
    (_hn : s.regs.rbp.toBitVec = BitVec.ofNat 64 count) :
    Eventually (step e) (Post s base count address capacity used) (s, base + 2896) := by
  have count_bound : count < 2^63 := by omega
  have positive := words_positive count (by omega)
  have hbytes := prepare_bytes s count hcount count_bound ht
  have hwords := prepare_words s count hcount count_bound ht
  have failure (h : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat
      (SszNative.Arena.wordsForBytes count)) :
      SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
        (SszNative.Arena.wordsForBytes count) = none :=
    (SszNative.Arena.reserve_eq_none_iff_checks _ _ _ _ positive).2 h
  apply preparation_cps e base hc
  intro f0
  rw [hbytes]
  by_cases hl : 8 * SszNative.Arena.wordsForBytes count < 2^63
  · rw [ite_eq_left hl]
    apply address_cps e base hc (prepared s f0) address used
    · simpa only [prepared] using header.address_load
    · simpa only [prepared] using header.used_load
    intro f1
    by_cases ha : address.toNat + used.toNat < 2^64
    · have ha' : used.toNat + address.toNat < 2^64 := by omega
      rw [ite_eq_left ha']
      have hadd : (used + address).toNat = address.toNat + used.toNat := by
        rw [add_nat used address ha']
        omega
      apply rounding_cps e base hc
      intro f2
      simp only [addressed, hadd]
      by_cases hr : address.toNat + used.toNat + 7 < 2^64
      · rw [ite_eq_left hr]
        have hp : (paddingWord (used + address)).toNat =
            SszNative.Arena.padding (address.toNat + used.toNat) := by
          rw [padding_nat _ (by rw [hadd]; exact hr), hadd]
        apply alignment_cps e base hc
        intro f3
        simp only [flagged, hp]
        by_cases hs : SszNative.Arena.start address.toNat used.toNat < 2^64
        · have hs' : SszNative.Arena.padding (address.toNat + used.toNat) + used.toNat < 2^64 := by
            simpa [SszNative.Arena.start, Nat.add_comm] using hs
          rw [ite_eq_left hs']
          have hstart : (paddingWord (used + address) + used).toNat =
              SszNative.Arena.start address.toNat used.toNat := by
            rw [add_nat _ _ (by rw [hp]; exact hs'), hp]
            simp [SszNative.Arena.start, Nat.add_comm]
          have hstartEq := word_eq_nat _ _ hstart
          apply end_cps e base hc
          intro f4
          simp only [alignedState, prepared, hbytes, hstart]
          by_cases he : SszNative.Arena.finish address.toNat used.toNat
              (SszNative.Arena.wordsForBytes count) < 2^64
          · have he' : 8 * SszNative.Arena.wordsForBytes count +
                SszNative.Arena.start address.toNat used.toNat < 2^64 := by
              simpa [SszNative.Arena.finish, Nat.add_comm] using he
            rw [ite_eq_left he']
            have hend : (8#64 + (s.regs.r10.toBitVec >>> 3) * 8#64 +
                (paddingWord (used + address) + used)).toNat =
                SszNative.Arena.finish address.toNat used.toNat
                  (SszNative.Arena.wordsForBytes count) := by
              rw [add_nat _ _ (by rw [hbytes, hstart]; exact he'), hbytes, hstart]
              simp [SszNative.Arena.finish, Nat.add_comm]
            have hendEq := word_eq_nat _ _ hend
            apply capacity_cps e base hc (capacity := capacity)
            · exact header.capacity_load
            intro f5
            simp only [ended, flagged, hend]
            by_cases hf : SszNative.Arena.finish address.toNat used.toNat
                (SszNative.Arena.wordsForBytes count) ≤ capacity.toNat
            · rw [ite_eq_left hf]
              apply commit_cps e base hc
              · exact ⟨(used.toNat : Int), header.used_load⟩
              intro f6
              have checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat
                  (SszNative.Arena.wordsForBytes count) := ⟨hl, ha, hr, hs, he, hf⟩
              have success := (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _ positive
                ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
                  SszNative.Arena.finish address.toNat used.toNat
                    (SszNative.Arena.wordsForBytes count)⟩).2 ⟨checks, rfl⟩
              have hptrBound : address.toNat + SszNative.Arena.start address.toNat used.toNat < 2^64 := by
                rw [SszNative.Arena.start_pointer]
                have hb := (SszNative.Arena.aligned_bounds (address.toNat + used.toNat)).2
                omega
              have hptr : (address + (paddingWord (used + address) + used)).toNat =
                  address.toNat + SszNative.Arena.start address.toNat used.toNat := by
                rw [add_nat _ _ (by rw [hstart]; exact hptrBound), hstart]
              have hptrEq := word_eq_nat _ _ hptr
              have hplus : (s.regs.r10.toBitVec >>> 3) + 1#64 =
                  BitVec.ofNat 64 (SszNative.Arena.wordsForBytes count) := by
                rw [hwords, ← BitVec.ofNat_add]
                congr 1
                omega
              have image : committed
                  (flagged (ended (alignedState
                    (flagged (addressed (prepared s f0) address used f1) f2) f3) f4) f5) f6 =
                  packingState s count address used f6 := by
                simp only [committed, packingState, cursorMemory, flagged, ended,
                  alignedState, addressed, prepared]
                simp only [hendEq]
                simp only [hptrEq]
                simp only [hplus]
                simp only [hstartEq, hwords]
              apply Eventually.done
              dsimp only [flagged, ended, alignedState, addressed, prepared] at image
              rw [image]
              exact ⟨packing_frame _ _ _ _ _, Or.inr ⟨_, success, rfl, rfl, rfl, f6, rfl⟩⟩
            · rw [ite_eq_right hf]
              apply Eventually.done
              refine ⟨?_, Or.inl ⟨failure (fun ch => hf ch.2.2.2.2.2), rfl, rfl⟩⟩
              simp [Frame]
          · have he' : ¬ 8 * SszNative.Arena.wordsForBytes count +
                SszNative.Arena.start address.toNat used.toNat < 2^64 := by
              simpa [SszNative.Arena.finish, Nat.add_comm] using he
            rw [ite_eq_right he']
            apply Eventually.done
            refine ⟨?_, Or.inl ⟨failure (fun ch => he ch.2.2.2.2.1), rfl, rfl⟩⟩
            simp [Frame, ended]
        · have hs' : ¬ SszNative.Arena.padding (address.toNat + used.toNat) + used.toNat < 2^64 := by
            simpa [SszNative.Arena.start, Nat.add_comm] using hs
          rw [ite_eq_right hs']
          apply Eventually.done
          refine ⟨?_, Or.inl ⟨failure (fun ch => hs ch.2.2.2.1), rfl, rfl⟩⟩
          simp [Frame, alignedState, prepared]
      · rw [ite_eq_right hr]
        apply Eventually.done
        refine ⟨?_, Or.inl ⟨failure (fun ch => hr ch.2.2.1), rfl, rfl⟩⟩
        simp [Frame, flagged, prepared]
    · have ha' : ¬ used.toNat + address.toNat < 2^64 := by omega
      rw [ite_eq_right ha']
      apply Eventually.done
      refine ⟨?_, Or.inl ⟨failure (fun ch => ha ch.2.1), rfl, rfl⟩⟩
      simp [Frame, addressed, prepared]
  · rw [ite_eq_right hl]
    apply Eventually.done
    refine ⟨?_, Or.inl ⟨failure (fun ch => hl ch.1), rfl, rfl⟩⟩
    simp [Frame, prepared]

/-- CPS composition exposes both reserve outcomes; no successful-reserve
assumption is hidden in the native theorem. -/
theorem reservation_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : Nat) (address capacity used : BitVec 64)
    (header : Header s address capacity used)
    (hcount : 9 ≤ count) (hlen : count ≤ s.regs.r14.toBitVec.toNat)
    (hinput : s.regs.r14.toBitVec.toNat < 2^63)
    (hsource : s.regs.rdx.toBitVec.toNat + s.regs.r14.toBitVec.toNat ≤ 2^64)
    (ht : s.regs.r10.toBitVec = BitVec.ofNat 64 (count - 1))
    (hn : s.regs.rbp.toBitVec = BitVec.ofNat 64 count)
    (P : MachineState → Prop)
    (hp : ∀ st, Post s base count address capacity used st → Eventually (step e) P st) :
    Eventually (step e) P (s, base + 2896) := by
  exact eventually_trans (step e) (Post s base count address capacity used) P _
    (reservation_runs e base hc s count address capacity used header hcount hlen hinput hsource ht hn) hp

private theorem exits_ne (base : Int64) : base + 2918 ≠ base + 5647 := by
  intro he
  have h := congrArg (fun p : Int64 => p - base) he
  simp only [Int64.add_comm base 2918, Int64.add_comm base 5647, Int64.add_sub_cancel] at h
  exact (show (2918 : Int64) ≠ 5647 by decide) h

/-- Both directions of resource adequacy, for every endpoint produced by the
native all-effects proof. In particular failure is not an existentially chosen
undefined-flag outcome. -/
theorem outcomes (s : MachineData) (base : Int64) (count : Nat)
    (address capacity used : BitVec 64) (st : MachineState)
    (h : Post s base count address capacity used st) :
    (st.2 = base + 2918 ↔ SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
      (SszNative.Arena.wordsForBytes count) = none) ∧
    (st.2 = base + 5647 ↔ ∃ r, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
      (SszNative.Arena.wordsForBytes count) = some r) := by
  rcases h.2 with ⟨hn, hp, _⟩ | ⟨r, hs, _, _, hp, _⟩
  · constructor
    · exact ⟨fun _ => hn, fun _ => hp⟩
    · constructor
      · intro he
        exact False.elim (exits_ne base (hp.symm.trans he))
      · rintro ⟨r, he⟩
        rw [hn] at he
        contradiction
  · constructor
    · constructor
      · intro he
        exact False.elim (exits_ne base (he.symm.trans hp))
      · intro he
        rw [hs] at he
        contradiction
    · exact ⟨fun _ => ⟨r, hs⟩, fun _ => hp⟩

end SszX86.UintCodec.Arena
