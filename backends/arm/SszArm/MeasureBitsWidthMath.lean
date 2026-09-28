import SszArm.MeasureContract
import SszArm.BitVectorValueArithmetic

namespace SszArm.Measure.Bits

def quotientLow (low high : BitVec 64) : BitVec 64 :=
  (low >>> (3 : Nat)) ||| (high <<< (61 : Nat))

def encodedLow (low high : BitVec 64) : BitVec 64 := quotientLow low high + 1#64

def encodedHigh (low high : BitVec 64) : BitVec 64 :=
  if 2^64 ≤ (quotientLow low high).toNat + 1
  then (high >>> (3 : Nat)) + 1#64 else high >>> (3 : Nat)

theorem quotientLow_nat (low high : BitVec 64) :
    (quotientLow low high).toNat = 2^61 * (high.toNat % 8) + low.toNat / 8 := by
  have lowBound := low.isLt
  have quotientBound : low.toNat / 8 < 2^61 := by omega
  have shifted : (high <<< (61 : Nat)).toNat = (high.toNat % 8) <<< 61 := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  simp only [quotientLow, BitVec.toNat_or, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, shifted]
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt quotientBound (high.toNat % 8),
    Nat.shiftLeft_eq]
  omega

/-- The lowering retains the full quotient and carry. There is no usize
assumption on the count or encoded width in this arithmetic statement. -/
theorem encoded_pair (low high : BitVec 64) :
    (encodedHigh low high ++ encodedLow low high).toNat = (high ++ low).toNat / 8 + 1 := by
  have highBound := high.isLt
  have lowBound := low.isLt
  have quotient := quotientLow_nat low high
  have quotientBound := (quotientLow low high).isLt
  have highQuotient : (high >>> (3 : Nat)).toNat = high.toNat / 8 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [NatToU128.append_toNat, NatToU128.append_toNat]
  simp only [encodedHigh, encodedLow, BitVec.toNat_add, BitVec.toNat_ofNat,
    highQuotient]
  split <;> simp only [BitVec.toNat_add, BitVec.toNat_ofNat, highQuotient] <;> omega

theorem encoded_pair_eq (count : BitVec 128) :
    encodedHigh (count.setWidth 64) ((count >>> (64 : Nat)).setWidth 64) ++
      encodedLow (count.setWidth 64) ((count >>> (64 : Nat)).setWidth 64) =
      BitVec.ofNat 128 (count.toNat / 8 + 1) := by
  have countWords : ((count >>> (64 : Nat)).setWidth 64 ++ count.setWidth 64) = count := by
    apply BitVec.eq_of_toNat_eq
    rw [NatToU128.append_toNat]
    have bound := count.isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [encoded_pair, countWords, BitVec.toNat_ofNat]
  have bound := count.isLt
  omega

/-- Physical backing constrains an observed count; it never constrains a logical
schema cap. The encoded width may still equal 2^64 and require its own allocation. -/
theorem physical_width_bound (bits : SszNative.Serialize.Packed)
    (physical : bits.bytes.size < 2^64) : bits.count.toNat / 8 + 1 ≤ 2^64 := by
  have sized := bits.sized
  omega

end SszArm.Measure.Bits
