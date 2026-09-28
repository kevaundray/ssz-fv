import SszX86.NatMulWordReserveLargeExec

namespace SszX86.NatMulWord.LargeReservation
open SszX86.NatMulWord

def lengthState (s : MachineData) (scratch10 scratchBX : UInt64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r12 := 2305843009213693950
      rdx := scratch10
      r10 := scratchBX
      rax := UInt64.ofBitVec (s.regs.r15.toBitVec * 8#64 + 8#64)}
    status := flags}

private theorem length_iff (n : UInt64) :
    (n.toNat ≤ 2305843009213693950 ∧
      (n.toBitVec * 8#64 + 8#64).toNat < 2^63) ↔
      8 * (n.toNat + 1) < 2^63 := by
  have hn := n.toBitVec.isLt
  have wordNat : (n.toBitVec * 8#64 + 8#64).toNat =
      (8 * (n.toNat + 1)) % 2^64 := by
    simp [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod, Nat.mul_mod,
      Nat.mul_add, Nat.mul_comm]
  rw [wordNat]
  constructor
  · rintro ⟨bound, sign⟩
    have noOverflow : 8 * (n.toNat + 1) < 2^64 := by omega
    rwa [Nat.mod_eq_of_lt noOverflow] at sign
  · intro bound
    exact ⟨by omega, by rw [Nat.mod_eq_of_lt (by omega)]; exact bound⟩

/-- Scaled LEA and ADD form the byte count. SETA checks multiplication overflow;
TEST/SETL checks isize, and OR combines them without any signed capacity bound. -/
theorem length_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ scratch10 scratchBX flags, Eventually (step e) P
      (lengthState s scratch10 scratchBX flags,
        if 8 * (s.regs.r15.toNat + 1) < 2^63 then base + 239 else base + 617)) :
    Eventually (step e) P (s, base + 195) := by
  have target := hc.targets ("natMulWord_u617", 617) (by decide)
  have eq : s.regs.r15.toBitVec = 2305843009213693950#64 ↔
      s.regs.r15.toNat = 2305843009213693950 := by
    rw [← BitVec.toNat_inj]
    rfl
  have mulCond :
      (!decide (s.regs.r15.toNat < 2305843009213693950) &&
        !decide (s.regs.r15.toBitVec = 2305843009213693950#64)) =
      decide (¬ s.regs.r15.toNat ≤ 2305843009213693950) := by
    apply Bool.eq_iff_iff.mpr
    simp [eq] <;> omega
  have byteNat : (s.regs.r15.toBitVec * 8#64 + 8#64).toNat =
      (8 + s.regs.r15.toNat * 8) % 18446744073709551616 := by
    simp [Nat.add_comm]
  simp only [← length_iff, byteNat] at hp
  natmulword_step 1:20 using hc
  natmulword_step 1:21 using hc
  natmulword_step 1:22 using hc
  natmulword_step 1:23 using hc
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natmulword_step 1:24 using hc
  natmulword_step 1:25 using hc
  constructor <;> natmulword_step 1:26 using hc
  all_goals
    natmulword_step 1:27 using hc
    constructor <;> natmulword_step 1:28 using hc
  all_goals
    by_cases hm : s.regs.r15.toNat ≤ 2305843009213693950 <;>
      by_cases hs : (8 + s.regs.r15.toNat * 8) % 18446744073709551616 < 9223372036854775808
    all_goals
      have sign : (9223372036854775808 ≤
          (8 + s.regs.r15.toNat * 8) % 18446744073709551616) ↔
          ¬ (8 + s.regs.r15.toNat * 8) % 18446744073709551616 < 9223372036854775808 := by omega
      simpa [lengthState, StatusFlags.from_result, BitVec.msb_eq_decide,
        mulCond, sign, hm, hs, target, Effects.All, BitVec.replaceLow, BitVec.drop,
        BitVec.take, NatCompare.byte_append, NatCompare.byte_extract,
        UInt64.add_comm] using hp _ _ _

end SszX86.NatMulWord.LargeReservation
