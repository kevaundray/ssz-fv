import SszX86.EmitModel
import SszX86.BitVectorConstructMath

namespace SszX86.Emit.Bits
open SszNative.Serialize (Desc Value Packed)
open SszNative (NatOperand)
open BitVector (constructLow constructHigh constructQuotient)

def IsList : Desc → Prop
  | .bitList _ | .progressiveBitList _ => True
  | _ => False

def IsBits : Desc → Prop
  | .bitVector _ | .bitList _ | .progressiveBitList _ => True
  | _ => False

theorem list_size {desc : Desc} {bits : Packed} {size : Nat}
    (kind : IsList desc)
    (expected : SszNative.Serialize.expectedSize desc (.bits bits) = .ok size) :
    size = bits.count.toNat / 8 + 1 := by
  cases desc with
  | bitList limit =>
    simp only [SszNative.Serialize.expectedSize] at expected
    split at expected <;> simp_all
  | progressiveBitList limit =>
    cases limit with
    | none => simpa only [SszNative.Serialize.expectedSize, Except.ok.injEq] using expected.symm
    | some cap =>
      simp only [SszNative.Serialize.expectedSize] at expected
      split at expected <;> simp_all
  | _ => cases kind

theorem vector_size {length : NatOperand} {bits : Packed} {size : Nat}
    (expected : SszNative.Serialize.expectedSize (.bitVector length) (.bits bits) = .ok size) :
    size = bits.bytes.size := by
  simp only [SszNative.Serialize.expectedSize] at expected
  split at expected <;> simp_all

theorem full_le_size {desc : Desc} {bits : Packed} {size : Nat}
    (kind : IsBits desc)
    (expected : SszNative.Serialize.expectedSize desc (.bits bits) = .ok size) :
    bits.count.toNat / 8 ≤ size := by
  cases desc with
  | bitVector length => have h := vector_size expected; have hs := bits.sized; omega
  | bitList limit => have h := list_size (desc := .bitList limit) trivial expected; omega
  | progressiveBitList limit =>
    have h := list_size (desc := .progressiveBitList limit) trivial expected; omega
  | _ => cases kind

/-- The physical backing, not a logical descriptor bound, justifies SHLD's
64-bit quotient. Counts above 2^64 remain admissible. -/
theorem quotient_nat (bits : Packed) (physical : bits.bytes.size < 2^64) :
    (constructQuotient bits.count).toNat = bits.count.toNat / 8 := by
  apply BitVector.construct_quotient_nat
  have sized := bits.sized
  omega

theorem remainder_nat (bits : Packed) :
    (constructLow bits.count &&& 7#64).toNat = bits.count.toNat % 8 := by
  simp only [constructLow, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  change (bits.count.toNat % 2^64 &&& (2^3 - 1)) = bits.count.toNat % 8
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem remainder32_nat (bits : Packed) :
    ((constructLow bits.count).setWidth 32 &&& 7#32).toNat = bits.count.toNat % 8 := by
  simp only [constructLow, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  change (bits.count.toNat % 2^64 % 2^32 &&& (2^3 - 1)) = bits.count.toNat % 8
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem backing_guards (bits : Packed) :
    bits.count.toNat / 8 ≤ bits.bytes.size ∧
    (bits.count.toNat % 8 = 0 → bits.bytes.size = bits.count.toNat / 8) ∧
    (bits.count.toNat % 8 ≠ 0 → bits.bytes.size = bits.count.toNat / 8 + 1) := by
  have sized := bits.sized
  omega

theorem list_guards {desc : Desc} {bits : Packed} {capacity size : Nat}
    (kind : IsList desc) (valid : ValidCall desc (.bits bits) capacity size) :
    bits.count.toNat / 8 < capacity ∧ bits.count.toNat / 8 + 1 < 2^64 := by
  have sizeEq := list_size kind valid.success
  have fitting := valid.fits
  have representable := valid.representable
  omega

theorem vector_tail_guard {length : NatOperand} {bits : Packed} {capacity size : Nat}
    (valid : ValidCall (.bitVector length) (.bits bits) capacity size)
    (nonaligned : bits.count.toNat % 8 ≠ 0) : bits.count.toNat / 8 < capacity := by
  have sizeEq := vector_size valid.success
  have backing := (backing_guards bits).2.2 nonaligned
  have fitting := valid.fits
  omega

/-- Exact low-byte NOT/SHL/AND used at both masking sites. -/
def maskByte (byte : BitVec 8) (remainder : Nat) : BitVec 8 :=
  byte &&& ~~~(255#8 <<< remainder)

def delimiterByte (byte : BitVec 8) (remainder : Nat) : BitVec 8 :=
  maskByte byte remainder ||| (1#8 <<< remainder)

theorem maskByte_eq (byte : UInt8) (remainder : Nat) (small : remainder < 8) :
    maskByte byte.toBitVec remainder =
      (byte &&& UInt8.ofNat (2 ^ remainder - 1)).toBitVec := by
  have choices : remainder = 0 ∨ remainder = 1 ∨ remainder = 2 ∨ remainder = 3 ∨
      remainder = 4 ∨ remainder = 5 ∨ remainder = 6 ∨ remainder = 7 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := {decide := true}) [maskByte]

theorem delimiterByte_eq (byte : UInt8) (remainder : Nat) (small : remainder < 8) :
    delimiterByte byte.toBitVec remainder =
      ((byte &&& UInt8.ofNat (2 ^ remainder - 1)) |||
        (1 <<< UInt8.ofNat remainder)).toBitVec := by
  rw [delimiterByte, maskByte_eq byte remainder small]
  have choices : remainder = 0 ∨ remainder = 1 ∨ remainder = 2 ∨ remainder = 3 ∨
      remainder = 4 ∨ remainder = 5 ∨ remainder = 6 ∨ remainder = 7 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true})

@[simp] theorem delimiterByte_zero (byte : BitVec 8) : delimiterByte byte 0 = 1#8 := by
  simp [delimiterByte, maskByte]

end SszX86.Emit.Bits
