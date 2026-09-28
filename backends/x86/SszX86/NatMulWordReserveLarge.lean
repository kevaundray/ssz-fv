import SszX86.NatMulWordReserveGuard

namespace SszX86.NatMulWord.LargeReservation
open SszX86.NatMulWord
open SszX86.Delimited


structure Header (s : MachineData) (address capacity used : BitVec 64) : Prop where
  address_load : Mem.loadInt s.dmem s.regs.r8.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 8#64) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16#64) 8 = some (used.toNat : Int)

def Frame (s t : MachineData) : Prop :=
  t.zmms = s.zmms ∧
  ∀ reg, reg ≠ .r14 → reg ≠ .r12 → reg ≠ .rdx → reg ≠ .r10 →
    reg ≠ .rax → reg ≠ .r13 → reg ≠ .rbp → t.regs.get64 reg = s.regs.get64 reg

def reservedState (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  let start := SszNative.Arena.start address.toNat used.toNat
  let pointer := BitVec.ofNat 64 (address.toNat + start)
  let finish := BitVec.ofNat 64 (start + 8 * (s.regs.r15.toNat + 1))
  {s with
    regs := {s.regs with
      r14 := UInt64.ofBitVec address
      r12 := 2305843009213693950
      rdx := UInt64.ofBitVec used
      r10 := UInt64.ofBitVec (used + address)
      rax := UInt64.ofBitVec finish
      r13 := UInt64.ofNat start
      rbp := UInt64.ofBitVec pointer}
    status := flags}

def Post (s : MachineData) (base : Int64) (address capacity used : BitVec 64)
    (t : MachineState) : Prop :=
  Frame s t.1 ∧
  ((SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
        (s.regs.r15.toNat + 1) = none ∧
      t.2 = base + 617 ∧ t.1.dmem = s.dmem) ∨
    ∃ r, SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
        (s.regs.r15.toNat + 1) = some r ∧
      t.2 = base + 310 ∧ ∃ flags, t.1 = reservedState s address used flags)

macro "natmulword_large_reservation_frame" : tactic => `(tactic|
  (refine ⟨rfl, ?_⟩
   intro reg h1 h2 h3 h4 h5 h6 h7
   cases reg <;>
     simp_all [flagged, ended, alignedState, addressed,
       lengthState, Reg64s.get64]))

private theorem word_eq (value : BitVec 64) (n : Nat) (h : value.toNat = n) :
    value = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Exact positive-length reserve, with all unsigned guards, from the completed
maximum/count-overflow cut. Inputs, output pointer, arena pointer, and RSP survive. -/
theorem runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address capacity used : BitVec 64)
    (header : Header s address capacity used) :
    Eventually (step e) (Post s base address capacity used) (s, base + 195) := by
  have failure (h : ¬ SszNative.Arena.Checks address.toNat capacity.toNat used.toNat
      (s.regs.r15.toNat + 1)) :
      SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
        (s.regs.r15.toNat + 1) = none :=
    (SszNative.Arena.reserve_eq_none_iff_checks _ _ _ _ (by omega)).2 h
  apply length_cps e base hc
  intro scratch10 scratchBX f0
  by_cases length : 8 * (s.regs.r15.toNat + 1) < 2^63
  · rw [ite_eq_left length]
    have bytes : (s.regs.r15.toBitVec * 8#64 + 8#64).toNat =
        8 * (s.regs.r15.toNat + 1) := by
      have overflow : 8 * (s.regs.r15.toNat + 1) < 2^64 := by omega
      have expr : (s.regs.r15.toBitVec * 8#64 + 8#64).toNat =
          (8 * (s.regs.r15.toNat + 1)) % 2^64 := by
        simp [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod, Nat.mul_mod,
          Nat.mul_add, Nat.mul_comm]
      rw [expr, Nat.mod_eq_of_lt overflow]
    have bytesWord := word_eq _ _ bytes
    apply address_cps e base hc (lengthState s scratch10 scratchBX f0)
      address used header.address_load header.used_load
    intro f1
    by_cases ha : address.toNat + used.toNat < 2^64
    · have ha' : used.toNat + address.toNat < 2^64 := by omega
      rw [ite_eq_left ha']
      have sum : (used + address).toNat = address.toNat + used.toNat := by
        rw [UintCodec.Arena.add_nat used address ha']
        omega
      apply rounding_cps e base hc
      intro f2
      simp only [flagged, addressed, lengthState, sum]
      by_cases rounding : address.toNat + used.toNat + 7 < 2^64
      · rw [ite_eq_left rounding]
        have pad : (paddingWord (used + address)).toNat =
            SszNative.Arena.padding (address.toNat + used.toNat) := by
          rw [UintCodec.Arena.padding_nat _ (by rw [sum]; exact rounding), sum]
        apply alignment_cps e base hc
        intro f3
        simp only [pad]
        by_cases hs : SszNative.Arena.start address.toNat used.toNat < 2^64
        · have hs' : SszNative.Arena.padding (address.toNat + used.toNat) + used.toNat < 2^64 := by
            simpa [SszNative.Arena.start, Nat.add_comm] using hs
          rw [ite_eq_left hs']
          have start : (paddingWord (used + address) + used).toNat =
              SszNative.Arena.start address.toNat used.toNat := by
            rw [UintCodec.Arena.add_nat _ _ (by rw [pad]; exact hs'), pad]
            simp [SszNative.Arena.start, Nat.add_comm]
          have startWord := word_eq _ _ start
          apply end_cps e base hc
          intro f4
          simp only [ended, alignedState, bytes, start]
          by_cases finish : SszNative.Arena.start address.toNat used.toNat +
              8 * (s.regs.r15.toNat + 1) < 2^64
          · have finish' : 8 * (s.regs.r15.toNat + 1) +
                SszNative.Arena.start address.toNat used.toNat < 2^64 := by omega
            rw [ite_eq_left finish']
            have endNat : ((s.regs.r15.toBitVec * 8#64 + 8#64) +
                (paddingWord (used + address) + used)).toNat =
                SszNative.Arena.start address.toNat used.toNat +
                  8 * (s.regs.r15.toNat + 1) := by
              rw [UintCodec.Arena.add_nat _ _ (by rw [bytes, start]; exact finish'), bytes, start]
              omega
            have endWord := word_eq _ _ endNat
            apply capacity_cps e base hc (capacity := capacity)
            · exact header.capacity_load
            intro f5
            simp only [flagged, endNat]
            by_cases fits : SszNative.Arena.start address.toNat used.toNat +
                8 * (s.regs.r15.toNat + 1) ≤ capacity.toNat
            · rw [ite_eq_left fits]
              have checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat
                  (s.regs.r15.toNat + 1) := ⟨length, ha, rounding, hs, finish, fits⟩
              have successful := (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega)
                ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
                  SszNative.Arena.start address.toNat used.toNat +
                    8 * (s.regs.r15.toNat + 1)⟩).2 ⟨checks, rfl⟩
              have alignedNat : (((used + address) + 7#64) &&& ~~~7#64).toNat =
                  address.toNat + SszNative.Arena.start address.toNat used.toNat := by
                have rounded := SszNative.Arena.mask_rounding (used + address)
                  (by rw [sum]; exact rounding)
                change ((used + address + 7#64) &&& ~~~7#64).toNat =
                  SszNative.Arena.aligned (used + address).toNat at rounded
                simpa only [sum, SszNative.Arena.start_pointer] using rounded
              have alignedWord := word_eq _ _ alignedNat
              have endWord' :
                  s.regs.r15.toBitVec * 8#64 + 8#64 +
                    BitVec.ofNat 64 (SszNative.Arena.start address.toNat used.toNat) =
                    BitVec.ofNat 64 (SszNative.Arena.start address.toNat used.toNat +
                      8 * (s.regs.r15.toNat + 1)) := by
                simpa only [startWord] using endWord
              apply Eventually.done
              refine ⟨?_, Or.inr ⟨_, successful, rfl, f5, ?_⟩⟩
              · natmulword_large_reservation_frame
              · simp only [reservedState,
                  endWord', alignedWord, startWord, UInt64.ofBitVec_ofNat, uint64_literal]
            · rw [ite_eq_right fits]
              apply Eventually.done
              refine ⟨?_, Or.inl ⟨failure (fun h => fits h.2.2.2.2.2), rfl, rfl⟩⟩
              natmulword_large_reservation_frame
          · have finish' : ¬ 8 * (s.regs.r15.toNat + 1) +
                SszNative.Arena.start address.toNat used.toNat < 2^64 := by omega
            rw [ite_eq_right finish']
            apply Eventually.done
            refine ⟨?_, Or.inl ⟨failure (fun h => finish h.2.2.2.2.1), rfl, rfl⟩⟩
            natmulword_large_reservation_frame
        · have hs' : ¬ SszNative.Arena.padding (address.toNat + used.toNat) + used.toNat < 2^64 := by
            simpa [SszNative.Arena.start, Nat.add_comm] using hs
          rw [ite_eq_right hs']
          apply Eventually.done
          refine ⟨?_, Or.inl ⟨failure (fun h => hs h.2.2.2.1), rfl, rfl⟩⟩
          natmulword_large_reservation_frame
      · rw [ite_eq_right rounding]
        apply Eventually.done
        refine ⟨?_, Or.inl ⟨failure (fun h => rounding h.2.2.1), rfl, rfl⟩⟩
        natmulword_large_reservation_frame
    · have ha' : ¬ used.toNat + address.toNat < 2^64 := by omega
      rw [ite_eq_right ha']
      apply Eventually.done
      refine ⟨?_, Or.inl ⟨failure (fun h => ha h.2.1), rfl, rfl⟩⟩
      natmulword_large_reservation_frame
  · rw [ite_eq_right length]
    apply Eventually.done
    refine ⟨?_, Or.inl ⟨failure (fun h => length h.1), rfl, rfl⟩⟩
    natmulword_large_reservation_frame

end SszX86.NatMulWord.LargeReservation
