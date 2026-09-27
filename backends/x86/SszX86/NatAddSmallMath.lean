import SszX86.NatAddCore

namespace SszX86.NatAdd
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem wide_low (a b : BitVec 64) :
    (LimbAdd.wideSum a b 0).setWidth 64 = a+b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, LimbAdd.wideSum_toNat a b 0 (by omega),
    Nat.add_zero, BitVec.toNat_add]

theorem wide_high (a b : BitVec 64) :
    ((LimbAdd.wideSum a b 0) >>> 64).setWidth 64 =
      BitVec.ofNat 64 (decide (2^64 ≤ a.toNat+b.toNat)).toNat := by
  have left := a.isLt
  have right := b.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    LimbAdd.wideSum_toNat a b 0 (by omega), Nat.add_zero, BitVec.toNat_ofNat]
  by_cases carry : 2^64 ≤ a.toNat+b.toNat <;> simp [carry] <;> omega

theorem fromWords_carry (pointer low : BitVec 64) :
    NatOperand.fromWords pointer [low, 1#64] = .large pointer [low, 1#64] := by
  simp [NatOperand.fromWords, Limbs.trim]

theorem normalized_small (limb : BitVec 64) :
    (NatOperand.small limb).normalized = .small limb := by
  by_cases zero : limb = 0#64 <;>
    simp [NatOperand.normalized, NatOperand.fromWords, NatOperand.words, Limbs.trim, zero]

/-- The physical extent bounds every significant count without requiring a
canonical input or a signed capacity bound. -/
theorem operand_count_bound (m : DataMem) (operand : NatOperand)
    (stored : operand.At (UintCodec.widthLoad m)) : operand.wordCount + 2 < 2^64 := by
  cases operand with
  | small limb =>
    simp only [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig]
    split <;> omega
  | large pointer words =>
    have extent := stored.2.2.1
    have length := Limbs.sigWords_le_length words
    change Limbs.sigWords words+2 < 2^64
    omega

end SszX86.NatAdd
