import SszX86.NatDivisionReserveLargeExec

namespace SszX86.NatDivision.Reservation.Large
open SszX86.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def lengthState (s : MachineData) (scratchDI scratch9 : UInt64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rcx := 2305843009213693950
      rdi := scratchDI
      r9 := scratch9
      r10 := UInt64.ofBitVec (s.regs.rax.toBitVec * 8#64)}
    status := flags}

private theorem length_iff (n : UInt64) :
    (n.toNat ≤ 2305843009213693951 ∧
      (n.toBitVec * 8#64).toNat < 2^63) ↔
      8 * n.toNat < 2^63 := by
  have bytes_eq : (n.toBitVec * 8#64).toNat = (8 * n.toNat) % 2^64 := by
    simp [BitVec.toNat_mul, Nat.mul_comm]
  rw [bytes_eq]
  constructor
  · rintro ⟨bound, sign⟩
    have noOverflow : 8 * n.toNat < 2^64 := by omega
    rwa [Nat.mod_eq_of_lt noOverflow] at sign
  · intro bound
    exact ⟨by omega, by rw [Nat.mod_eq_of_lt (by omega)]; exact bound⟩

/-- Unsigned multiplication overflow and the isize guard concern the allocation
length, not capacity. Undefined TEST and OR flags are universally quantified. -/
theorem length_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ scratchDI scratch9 flags, Eventually (step e) P
      (lengthState s scratchDI scratch9 flags,
        if 8 * s.regs.rax.toNat < 2^63 then base + 548 else base + 205)) :
    Eventually (step e) P (s, base + 160) := by
  have target := hc.targets ("natDivision_u548", 548) (by decide)
  have eq : s.regs.rax.toBitVec = 2305843009213693951#64 ↔
      s.regs.rax.toNat = 2305843009213693951 := by
    rw [← BitVec.toNat_inj]
    rfl
  have cond : (2305843009213693951 ≤ s.regs.rax.toNat ∧
      s.regs.rax.toBitVec ≠ 2305843009213693951#64) ↔
      ¬ s.regs.rax.toNat ≤ 2305843009213693951 := by
    simp only [ne_eq, eq]
    omega
  have byteNat : (s.regs.rax.toBitVec * 8#64).toNat =
      (s.regs.rax.toNat * 8) % 18446744073709551616 := by simp
  have seta : (!decide (s.regs.rax.toNat < 2305843009213693951) &&
      !decide (s.regs.rax.toBitVec = 2305843009213693951#64)) =
      !decide (s.regs.rax.toNat ≤ 2305843009213693951) := by
    simp only [eq]
    by_cases lt : s.regs.rax.toNat < 2305843009213693951
    · have le : s.regs.rax.toNat ≤ 2305843009213693951 := by omega
      simp [lt, le]
    · by_cases same : s.regs.rax.toNat = 2305843009213693951
      · simp [same]
      · have le : ¬ s.regs.rax.toNat ≤ 2305843009213693951 := by omega
        simp [lt, same, le]
  simp only [← length_iff] at hp
  natdiv_step 40 using hc
  natdiv_step 41 using hc
  natdiv_step 42 using hc
  natdiv_step 43 using hc
  natdiv_step 44 using hc
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natdiv_step 45 using hc
  constructor <;> natdiv_step 46 using hc
  all_goals
    natdiv_step 47 using hc
    constructor <;> natdiv_step 48 using hc
  all_goals
    by_cases hm : s.regs.rax.toNat ≤ 2305843009213693951 <;>
      by_cases hs : (s.regs.rax.toBitVec * 8#64).toNat < 2^63
    all_goals
      have sign : decide (9223372036854775808 ≤
          (s.regs.rax.toNat * 8) % 18446744073709551616) =
          !decide ((s.regs.rax.toBitVec * 8#64).toNat < 2^63) := by
        rw [byteNat]
        by_cases h : (s.regs.rax.toNat * 8) % 18446744073709551616 < 2^63
        · have hn : ¬ 9223372036854775808 ≤
              (s.regs.rax.toNat * 8) % 18446744073709551616 := by omega
          simp only [h, hn, decide_true, decide_false, Bool.not_true]
        · have hn : 9223372036854775808 ≤
              (s.regs.rax.toNat * 8) % 18446744073709551616 := by omega
          simp only [h, hn, decide_true, decide_false, Bool.not_false]
      simp only [hs, decide_true, decide_false, Bool.not_true, Bool.not_false] at sign
      simp only [hm, decide_true, decide_false, Bool.not_true, Bool.not_false] at seta
      simp only [hm, hs, and_true, and_false, ite_true, ite_false] at hp
      simpa [lengthState, StatusFlags.from_result, BitVec.msb_eq_decide,
        cond, seta, sign, hm, hs, target, Effects.All, BitVec.replaceLow, BitVec.drop,
        BitVec.take, NatCompare.byte_append, NatCompare.byte_extract] using hp _ _ _

/-- The common large failure frontier restores the saved output pointer and
executes the real relative jump to the shared ScratchExhausted stores. -/
theorem failure_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (output : BitVec 64)
    (hl : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (output.toNat : Int))
    (P : MachineState → Prop)
    (hp : Eventually (step e) P
      ({s with regs := {s.regs with rbx := UInt64.ofBitVec output}}, base + 379)) :
    Eventually (step e) P (s, base + 205) := by
  natdiv_step 49 using hc
  natdiv_load hl
  natdiv_step 50 using hc
  simpa using hp

end SszX86.NatDivision.Reservation.Large
