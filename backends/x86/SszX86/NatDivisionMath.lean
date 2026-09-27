import SszX86.NatDivisionCore
import SszX86.Udivti3Math

namespace SszX86.NatDivision

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The compiler recovers the remainder using only the low product. The
high quotient limb is deliberately unrestricted on the two-word path. -/
theorem remainder_from_quotient (lo hi divisor qlo qhi : BitVec 64)
    (hq : Udivti3.value qlo qhi = Udivti3.value lo hi / divisor.toNat) :
    lo - qlo * divisor = BitVec.ofNat 64 (Udivti3.value lo hi % divisor.toNat) := by
  have conserve := Nat.div_add_mod' (Udivti3.value lo hi) divisor.toNat
  rw [← hq] at conserve
  have cast := congrArg (BitVec.ofNat 64) conserve
  simp only [Udivti3.value, Udivti3.radix, BitVec.ofNat_add, BitVec.ofNat_mul,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] at cast
  have zero : BitVec.ofNat 64 (2^64) = 0#64 := by decide
  simp only [zero, BitVec.mul_zero, BitVec.zero_add] at cast
  apply BitVec.sub_eq_iff_eq_add.mpr
  exact cast.symm.trans (BitVec.add_comm _ _)

/-- The reverse loop's incoming remainder makes the complete divider quotient
one word, not merely an arbitrary low-word truncation. -/
theorem loop_quotient (limb remainder divisor qlo qhi : BitVec 64)
    (hr : remainder.toNat < divisor.toNat)
    (hq : Udivti3.value qlo qhi = Udivti3.value limb remainder / divisor.toNat) :
    qhi = 0#64 ∧ qlo = (SszNative.LimbDivision.step divisor remainder.toNat limb).1 := by
  have hv : Udivti3.value limb remainder =
      SszNative.LimbDivision.current remainder.toNat limb := rfl
  have bound := SszNative.LimbDivision.quotient_lt divisor limb remainder.toNat hr
  have high_zero : qhi.toNat = 0 := by
    rw [hv] at hq
    simp only [Udivti3.value, Udivti3.radix] at hq
    have hl := qlo.isLt
    omega
  have hh : qhi = 0#64 := BitVec.eq_of_toNat_eq (by simpa using high_zero)
  refine ⟨hh, BitVec.eq_of_toNat_eq ?_⟩
  rw [SszNative.LimbDivision.step_quotient divisor limb remainder.toNat hr]
  simpa only [hh, Udivti3.value, Udivti3.radix, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.zero_mul, Nat.zero_add, SszNative.LimbDivision.current] using hq

/-- Exact low-word remainder recurrence after the actual `mulq`/`subq`. -/
theorem loop_remainder (limb remainder divisor qlo qhi : BitVec 64)
    (hq : Udivti3.value qlo qhi = Udivti3.value limb remainder / divisor.toNat) :
    limb - qlo * divisor =
      BitVec.ofNat 64 (SszNative.LimbDivision.step divisor remainder.toNat limb).2 := by
  exact remainder_from_quotient limb remainder divisor qlo qhi hq

end SszX86.NatDivision
