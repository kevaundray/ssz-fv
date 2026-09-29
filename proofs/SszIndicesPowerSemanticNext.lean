import SszIndicesPowerSemanticDepth
import SszIndicesArithmetic
import SszNatShiftSemantics

set_option autoImplicit false

namespace SszNative.Indices

/-- Every successful source next-power operation returns the pinned nextPow2.
The arena may fail independently; no future success or resource bound is assumed. -/
theorem nextPow2_value (count : NatOperand) (base capacity used : Nat)
    (result : NatOperand)
    (success : (nextPow2 count base capacity used).result = .ok result) :
    result.value = Ssz.nextPow2 count.value := by
  unfold nextPow2 at success
  split at success
  next small =>
    have smallValue : count.value ≤ 1 :=
      (one_word_le_iff count 1 (by decide)).mp small
    have bound : Ssz.depthFor count.value ≤ 0 :=
      Ssz.depthFor_le_of_le_two_pow (by simpa using smallValue)
    have depthZero : Ssz.depthFor count.value = 0 := by omega
    simp only [unchanged, Except.ok.injEq] at success
    subst result
    change 1 = 2 ^ Ssz.depthFor count.value
    rw [depthZero]
  next large =>
    split at success
    next power =>
      simp only [unchanged, Except.ok.injEq] at success
      subst result
      obtain ⟨exponent, equal⟩ := (powerOfTwo_iff count).mp power
      simp only [Ssz.nextPow2, equal, Ssz.depthFor_pow]
    next notPower =>
      have depth : bitLength count = Ssz.depthFor count.value := by
        simpa only [notPower, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
          using powerDepth_refines count
      have shifted :
          (NatShift.shl (.small 1) (bitLength count) base capacity used).result = .ok result := by
        change Except.mapError Error.arithmetic
          (NatShift.shl (.small 1) (bitLength count) base capacity used).result =
            .ok result at success
        cases outcome : (NatShift.shl (.small 1) (bitLength count) base capacity used).result with
        | error reason =>
            have impossible :=
              (congrArg (Except.mapError Error.arithmetic) outcome).symm.trans success
            cases impossible
        | ok value =>
            simpa only [Except.mapError, Except.ok.injEq] using
              (congrArg (Except.mapError Error.arithmetic) outcome).symm.trans success
      have value := NatShift.shl_value (.small 1) (bitLength count) base capacity used result shifted
      simpa [NatOperand.value, NatOperand.words, Limbs.value, Nat.shiftLeft_eq,
        Ssz.nextPow2, depth] using value

end SszNative.Indices
