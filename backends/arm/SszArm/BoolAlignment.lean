import SszArm.BoolExec

namespace SszArm.BoolCodec

/-- Stack lowering keeps the architectural alignment without native-SAT lemmas. -/
theorem aligned_sub16 (x : BitVec 64) (h : Aligned x 4) : Aligned (x - 16#64) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at *
  bv_omega

theorem aligned_sub32 (x : BitVec 64) (h : Aligned x 4) : Aligned (x - 32#64) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at *
  bv_omega

theorem aligned_add16 (x : BitVec 64) (h : Aligned x 4) : Aligned (x + 16#64) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at *
  bv_omega

theorem aligned_add32 (x : BitVec 64) (h : Aligned x 4) : Aligned (x + 32#64) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at *
  bv_omega

theorem stack_aligned (s : ArmState) (h : CheckSPAlignment s) : Aligned (r (.GPR 31) s) 4 := by
  simpa only [CheckSPAlignment, state_simp_rules, bitvec_rules, minimal_theory] using h

end SszArm.BoolCodec
