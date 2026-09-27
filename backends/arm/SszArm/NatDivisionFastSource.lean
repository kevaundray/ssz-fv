import SszArm.NatDivisionFastFrame
import SszArm.NatDivisionSource

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem fast_low (site : FastSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR 22#5) (fastResult site s base) = r (.GPR 0#5) (fastPrepared site s base) := by
  rw [fastResult, fast_finish_register]
  change r (.GPR 22#5) (callResult site.call (fastPrepared site s base) base) = _
  rw [call_gpr _ _ _ 22#5 (by decide) (by decide)]
  cases site <;> simp [fastPrepared, FastSite.setup, block, Op.effect, put, next, state_simp_rules]

theorem fast_pc_result (site : FastSite) (s : ArmState) (base : BitVec 64) :
    read_pc (fastResult site s base) =
      if r (.GPR 1#5) (fastResult site s base) = 0#64 then base + 644#64 else base + 684#64 := by
  have keep := fast_finish_register site (fastDivided site s base) base 1#5
  change r (.GPR 1#5) (fastResult site s base) = r (.GPR 1#5) (fastDivided site s base) at keep
  rw [keep]
  exact fast_pc site s base

/-- Arithmetic for every fast BL site, including borrowed Large inputs with
arbitrarily many redundant high zeros. Setup observes the original two words. -/
theorem fast_arithmetic (site : FastSite) (s : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) (count : operand.wordCount ≤ 2)
    (domain : 2 ≤ (r (.GPR 20#5) s).toNat)
    (input : Udivti3.numerator (fastPrepared site s base) = operand.value) :
    Udivti3.numerator (fastResult site s base) = operand.value / (r (.GPR 20#5) s).toNat ∧
      r (.GPR 22#5) (fastResult site s base) -
        r (.GPR 0#5) (fastResult site s base) * r (.GPR 20#5) (fastResult site s base) =
        SszNative.NatDivision.wideRemainder operand (r (.GPR 20#5) s) := by
  have quotient := fast_quotient site s base (by omega)
  rw [input] at quotient
  refine ⟨quotient, ?_⟩
  rw [fast_low, fast_gpr site s base 20#5 (by decide) (by decide) (by decide)]
  apply wide_remainder_low operand (r (.GPR 20#5) s)
    (r (.GPR 0#5) (fastPrepared site s base)) (r (.GPR 1#5) (fastPrepared site s base))
    (r (.GPR 0#5) (fastResult site s base)) (r (.GPR 1#5) (fastResult site s base)) count
  · intro zero
    rw [zero] at domain
    contradiction
  · exact input
  · exact quotient

/-- The bounded source view is exactly the original first two physical words. -/
theorem operand_wide_join (operand : SszNative.NatOperand) (count : operand.wordCount ≤ 2) :
    Udivti3.join (operand.words[0]?.getD 0#64) (operand.words[1]?.getD 0#64) = operand.value := by
  have bound := SszNative.NatDivision.value_lt_128 operand count
  change Udivti3.join (operand.words[0]?.getD 0#64) (operand.words[1]?.getD 0#64) =
    SszNative.Limbs.value operand.words
  cases words : operand.words with
  | nil => simp [Udivti3.join, SszNative.Limbs.value]
  | cons low rest =>
    cases rest with
    | nil => simp [Udivti3.join, SszNative.Limbs.value]
    | cons high rest =>
      have zero : SszNative.Limbs.value rest = 0 := by
        change SszNative.Limbs.value operand.words < 2^128 at bound
        rw [words] at bound
        simp only [SszNative.Limbs.value] at bound
        omega
      change Udivti3.join low high = SszNative.Limbs.value (low :: high :: rest)
      simp only [Udivti3.join, Udivti3.radix, SszNative.Limbs.value, zero,
        Nat.mul_zero, Nat.add_zero]
      omega

end SszArm.NatDivision
