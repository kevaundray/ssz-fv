import SszArm.NatDivisionCalls
import SszNatDivision

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Extracting the low word from the runtime's mathematical two-word view. -/
theorem join_low (lo hi : BitVec 64) :
    BitVec.ofNat 64 (Udivti3.join lo hi) = lo := by
  apply BitVec.eq_of_toNat_eq
  simp [Udivti3.join, Udivti3.radix, BitVec.toNat_ofNat, Nat.add_mod, lo.isLt]

/-- The compiler computes the remainder with low-word MUL/SUB even for a
wide quotient. This identity justifies that truncation, rather than assuming
that the complete numerator or its product fits one word. -/
theorem remainder_low (lo hi divisor quotientLow quotientHigh : BitVec 64)
    (hq : Udivti3.join quotientLow quotientHigh =
      Udivti3.join lo hi / divisor.toNat) :
    lo - quotientLow * divisor =
      BitVec.ofNat 64 (Udivti3.join lo hi % divisor.toNat) := by
  have conservation : divisor.toNat * Udivti3.join quotientLow quotientHigh +
      Udivti3.join lo hi % divisor.toNat = Udivti3.join lo hi := by
    rw [hq]
    exact Nat.div_add_mod _ _
  have lowConservation : divisor * quotientLow +
      BitVec.ofNat 64 (Udivti3.join lo hi % divisor.toNat) = lo := by
    have h := congrArg (BitVec.ofNat 64) conservation
    simpa only [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, join_low] using h
  calc
    lo - quotientLow * divisor =
        (divisor * quotientLow + BitVec.ofNat 64 (Udivti3.join lo hi % divisor.toNat)) -
          quotientLow * divisor :=
      congrArg (fun value => value - quotientLow * divisor) lowConservation.symm
    _ = _ := by rw [BitVec.mul_comm quotientLow divisor]; bv_omega

/-- A bounded quotient has a zero high word and an exact low word. -/
theorem quotient_words (lo hi : BitVec 64) (quotient : Nat)
    (eq : Udivti3.join lo hi = quotient) (bound : quotient < 2^64) :
    lo.toNat = quotient ∧ hi = 0#64 := by
  have lh := lo.isLt
  have hh := hi.isLt
  have zero : hi.toNat = 0 := by
    simp only [Udivti3.join, Udivti3.radix] at eq
    omega
  have high : hi = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simpa using zero
  refine ⟨?_, high⟩
  simpa only [Udivti3.join, zero, Nat.mul_zero, Nat.zero_add] using eq

/-- The real runtime call returns exactly the next long-division quotient word;
its high word is zero by the incoming remainder invariant. -/
theorem call_limb_quotient (site : CallSite) (s : ArmState) (base : BitVec 64)
    (divisor word : BitVec 64) (remainder : Nat)
    (low : r (.GPR 0#5) s = word)
    (high : (r (.GPR 1#5) s).toNat = remainder)
    (divisorLow : r (.GPR 2#5) s = divisor)
    (divisorHigh : r (.GPR 3#5) s = 0#64)
    (remainderBound : remainder < divisor.toNat) :
    r (.GPR 0#5) (callResult site s base) =
      (SszNative.LimbDivision.step divisor remainder word).1 ∧
    r (.GPR 1#5) (callResult site s base) = 0#64 := by
  have numerator : Udivti3.numerator s =
      SszNative.LimbDivision.current remainder word := by
    change Udivti3.join (r (.GPR 0#5) s) (r (.GPR 1#5) s) =
      SszNative.LimbDivision.current remainder word
    rw [Udivti3.join_eq, low, high]
    rfl
  have denominator : Udivti3.divisor s = divisor.toNat := by
    simp [Udivti3.divisor, Udivti3.join, divisorLow, divisorHigh]
  have quotient := call_quotient site s base (by rw [denominator]; omega)
  rw [numerator, denominator] at quotient
  obtain ⟨ql, qh⟩ := quotient_words _ _ _ quotient
    (SszNative.LimbDivision.quotient_lt divisor word remainder remainderBound)
  refine ⟨?_, qh⟩
  apply BitVec.eq_of_toNat_eq
  exact ql.trans (SszNative.LimbDivision.step_quotient divisor word remainder remainderBound).symm

/-- MUL/SUB after the call gives the exact untruncated next remainder. -/
theorem call_limb_remainder (site : CallSite) (s : ArmState) (base : BitVec 64)
    (divisor word : BitVec 64) (remainder : Nat)
    (low : r (.GPR 0#5) s = word)
    (high : (r (.GPR 1#5) s).toNat = remainder)
    (divisorLow : r (.GPR 2#5) s = divisor)
    (divisorHigh : r (.GPR 3#5) s = 0#64)
    (remainderBound : remainder < divisor.toNat) :
    (word - r (.GPR 0#5) (callResult site s base) * divisor).toNat =
      (SszNative.LimbDivision.step divisor remainder word).2 := by
  have denominator : Udivti3.divisor s = divisor.toNat := by
    simp [Udivti3.divisor, Udivti3.join, divisorLow, divisorHigh]
  have quotient := call_quotient site s base (by rw [denominator]; omega)
  change Udivti3.join (r (.GPR 0#5) (callResult site s base))
      (r (.GPR 1#5) (callResult site s base)) =
    Udivti3.join (r (.GPR 0#5) s) (r (.GPR 1#5) s) / Udivti3.divisor s at quotient
  rw [denominator, low] at quotient
  have identity := remainder_low word (r (.GPR 1#5) s) divisor _ _ quotient
  rw [identity, BitVec.toNat_ofNat]
  have numerator : Udivti3.join word (r (.GPR 1#5) s) =
      SszNative.LimbDivision.current remainder word := by
    simp only [Udivti3.join_eq, high, SszNative.LimbDivision.current, Udivti3.radix]
  rw [numerator]
  have bound : SszNative.LimbDivision.current remainder word % divisor.toNat < 2^64 :=
    Nat.lt_trans (Nat.mod_lt _ (by omega)) divisor.isLt
  rw [Nat.mod_eq_of_lt bound]
  rfl

end SszArm.NatDivision
