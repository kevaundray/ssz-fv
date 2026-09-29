import SszX86.CodecPlanSingletonExec

namespace SszX86.CodecPlanSingleton
open SszX86.UintCodec

/-- The reservation prefix is read-only until the PC53 commit. -/
def GuardFrame (s t : MachineData) : Prop :=
  t.dmem = s.dmem ∧ t.zmms = s.zmms ∧
  ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 →
    t.regs.get64 r = s.regs.get64 r

def ready (s : MachineData) (address used : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec address,
    rcx := UInt64.ofNat (SszNative.Arena.start address.toNat used.toNat),
    r8 := UInt64.ofNat (SszNative.Arena.start address.toNat used.toNat + 40),
    r9 := UInt64.ofBitVec (used + address)}, status := flags}

def Reserved (s : MachineData) (base : Int64) (address capacity used : BitVec 64)
    (t : MachineState) : Prop :=
  GuardFrame s t.1 ∧
  ((SszNative.TypedArena.reserve ⟨40, 3⟩ address.toNat capacity.toNat used.toNat 1 = none ∧
      t.2 = base + 122) ∨
    ∃ r, SszNative.TypedArena.reserve ⟨40, 3⟩ address.toNat capacity.toNat used.toNat 1 = some r ∧
      r.pointer = address.toNat + SszNative.Arena.start address.toNat used.toNat ∧
      r.used = SszNative.Arena.start address.toNat used.toNat + 40 ∧
      t.2 = base + 53 ∧ ∃ flags, t.1 = ready s address used flags)

macro "codec_plan_guard_frame" : tactic => `(tactic|
  (refine ⟨rfl, rfl, ?_⟩
   intro r h1 h2 h3 h4
   cases r <;> simp_all [flagged, addressed, aligned, ended, ready, Reg64s.get64]))

private theorem word_eq (v : BitVec 64) (n : Nat) (h : v.toNat = n) :
    v = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- All five native reservation refusals implement the checked typed model.
No successful allocation, branch outcome, or continuation is an entry premise. -/
theorem reserve_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address capacity used : BitVec 64)
    (header : Header s address capacity used) :
    Eventually (step e) (Reserved s base address capacity used) (s, base) := by
  have bridge : SszNative.TypedArena.reserve ⟨40, 3⟩
      address.toNat capacity.toNat used.toNat 1 =
      SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 5 := by
    simpa using SszNative.TypedArena.reserve_forty address.toNat capacity.toNat used.toNat 1
  have failure (h : ¬SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 5) :
      SszNative.TypedArena.reserve ⟨40, 3⟩ address.toNat capacity.toNat used.toNat 1 = none := by
    rw [bridge]
    exact (SszNative.Arena.reserve_eq_none_iff_checks _ _ _ _ (by decide)).2 h
  apply address_cps e base hc s address used header.address_load header.used_load
  intro f0
  by_cases addressOk : address.toNat + used.toNat < 2^64
  · have addressOk' : used.toNat + address.toNat < 2^64 := by omega
    rw [ite_eq_left addressOk']
    have sum : (used + address).toNat = address.toNat + used.toNat := by
      rw [UintCodec.Arena.add_nat used address addressOk']
      omega
    apply rounding_cps e base hc
    intro f1
    simp only [addressed, sum, UInt64.toNat_ofBitVec]
    by_cases roundedOk : address.toNat + used.toNat + 7 < 2^64
    · rw [ite_eq_left roundedOk]
      have pad : (paddingWord (used + address)).toNat =
          SszNative.Arena.padding (address.toNat + used.toNat) := by
        rw [UintCodec.Arena.padding_nat _ (by rw [sum]; exact roundedOk), sum]
      apply alignment_cps e base hc
      intro f2
      simp only [flagged, addressed, pad, UInt64.toNat_ofBitVec]
      by_cases startOk : SszNative.Arena.start address.toNat used.toNat < 2^64
      · have startOk' : SszNative.Arena.padding (address.toNat + used.toNat) + used.toNat < 2^64 := by
          simpa [SszNative.Arena.start, Nat.add_comm] using startOk
        rw [ite_eq_left startOk']
        have startNat : (paddingWord (used + address) + used).toNat =
            SszNative.Arena.start address.toNat used.toNat := by
          rw [UintCodec.Arena.add_nat _ _ (by rw [pad]; exact startOk'), pad]
          simp [SszNative.Arena.start, Nat.add_comm]
        have startWord := word_eq _ _ startNat
        apply end_guard_cps e base hc
        intro f3
        simp only [flagged, aligned, addressed, startNat, UInt64.toNat_ofBitVec]
        by_cases endOk : SszNative.Arena.start address.toNat used.toNat + 40 < 2^64
        · rw [ite_eq_left endOk]
          have endNat : (paddingWord (used + address) + used + 40#64).toNat =
              SszNative.Arena.start address.toNat used.toNat + 40 := by
            rw [UintCodec.Arena.add_nat _ _ (by rw [startNat]; exact endOk), startNat]
            rfl
          have endWord := word_eq _ _ endNat
          apply capacity_cps e base hc (capacity := capacity)
          · exact header.capacity_load
          intro f4
          simp only [flagged, aligned, addressed, endNat]
          by_cases fits : SszNative.Arena.start address.toNat used.toNat + 40 ≤ capacity.toNat
          · rw [ite_eq_left fits]
            have checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat 5 :=
              ⟨by decide, addressOk, roundedOk, startOk, endOk, fits⟩
            have success : SszNative.TypedArena.reserve ⟨40, 3⟩
                address.toNat capacity.toNat used.toNat 1 =
                some ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
                  SszNative.Arena.start address.toNat used.toNat + 40⟩ := by
              rw [bridge]
              exact (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _ (by decide) _).2 ⟨checks, rfl⟩
            apply Eventually.done
            refine ⟨?_, Or.inr ⟨_, success, rfl, rfl, rfl, f4, ?_⟩⟩
            · codec_plan_guard_frame
            · simp only [flagged, ended, aligned, addressed, ready, startWord, endWord]
          · rw [ite_eq_right fits]
            apply Eventually.done
            refine ⟨?_, Or.inl ⟨failure (by intro checks; exact fits checks.2.2.2.2.2), rfl⟩⟩
            codec_plan_guard_frame
        · rw [ite_eq_right endOk]
          apply Eventually.done
          refine ⟨?_, Or.inl ⟨failure (by intro checks; exact endOk checks.2.2.2.2.1), rfl⟩⟩
          codec_plan_guard_frame
      · have noStart : ¬SszNative.Arena.padding (address.toNat + used.toNat) + used.toNat < 2^64 := by
          simpa [SszNative.Arena.start, Nat.add_comm] using startOk
        rw [ite_eq_right noStart]
        apply Eventually.done
        refine ⟨?_, Or.inl ⟨failure (by intro checks; exact startOk checks.2.2.2.1), rfl⟩⟩
        codec_plan_guard_frame
    · rw [ite_eq_right roundedOk]
      apply Eventually.done
      refine ⟨?_, Or.inl ⟨failure (by intro checks; exact roundedOk checks.2.2.1), rfl⟩⟩
      codec_plan_guard_frame
  · have noAddress : ¬used.toNat + address.toNat < 2^64 := by omega
    rw [ite_eq_right noAddress]
    apply Eventually.done
    refine ⟨?_, Or.inl ⟨failure (by intro checks; exact addressOk checks.2.1), rfl⟩⟩
    codec_plan_guard_frame

end SszX86.CodecPlanSingleton
