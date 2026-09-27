import SszByteView
import SszPacking

set_option autoImplicit false

namespace SszNative.BitView

/-- Native Bits borrows packed bytes; bits above its logical length are ignored. -/
def ResultAt (load : Nat → Nat → Option Nat) (out : Nat) : Except Ssz.Err Ssz.Value → Prop
  | .ok (.bits bits) =>
    load out 8 = some 0 ∧ load (out + 16) 1 = some 3 ∧ bits.size < 2 ^ 128 ∧
      load (out + 48) 8 = some (bits.size % 2 ^ 64) ∧
      load (out + 56) 8 = some (bits.size / 2 ^ 64) ∧
      ∃ source packed, load (out + 32) 8 = some source ∧
        load (out + 40) 8 = some packed.size ∧ packed.size = (bits.size + 7) / 8 ∧
        ByteView.BytesAt load source packed ∧ Ssz.unpackBits packed bits.size = bits
  | .error (.scope expected actual) => UintCodec.errorAt load out 3 expected actual
  | .error (.overLimit expected actual) => UintCodec.errorAt load out 2 expected actual
  | .error .paddingBits => UintCodec.errorAt load out 15 0 0
  | .error .emptyEncoding => UintCodec.errorAt load out 16 0 0
  | .error .noDelimiter => UintCodec.errorAt load out 17 0 0
  | .error .trailingZeros => UintCodec.errorAt load out 18 0 0
  | _ => False

def vectorOutcome (length : Nat) (data : Ssz.Bytes) : Except Ssz.Err Ssz.Value :=
  if data.size = (length + 7) / 8 then
    if length % 8 ≠ 0 ∧ 0 < data.size then
      if data[data.size - 1]! >>> UInt8.ofNat (length % 8) ≠ 0 then
        .error .paddingBits
      else .ok (.bits (Ssz.unpackBits data length))
    else .ok (.bits (Ssz.unpackBits data length))
  else .error (.scope ((length + 7) / 8) data.size)

def delimitedCount (data : Ssz.Bytes) : Nat :=
  8 * (data.size - 1) + Ssz.highestBit data[data.size - 1]!

/-- Logical outcome, before accounting for the native count's scratch allocation. -/
def delimitedOutcome (limit : Option Nat) (data : Ssz.Bytes) : Except Ssz.Err Ssz.Value :=
  if data.size = 0 then .error .emptyEncoding
  else if data[data.size - 1]! = 0 then
    if data.all (· == 0) then .error .noDelimiter else .error .trailingZeros
  else
    let count := delimitedCount data
    match limit with
    | none => .ok (.bits (Ssz.unpackBits data count))
    | some cap =>
      if count ≤ cap then .ok (.bits (Ssz.unpackBits data count))
      else .error (.overLimit cap count)

theorem vector_outcome_eq_deserialize (length : Nat) (data : Ssz.Bytes) :
    vectorOutcome length data = Ssz.deserialize (.bitVector length) data := by
  unfold vectorOutcome
  split
  · rename_i hs
    have checked : (data.size != (length + 7) / 8) = false := by simp [hs]
    simp only [Ssz.deserialize, checked, Bool.false_eq_true, ↓reduceIte]
    by_cases hr : length % 8 = 0 <;> by_cases hp : 0 < data.size <;>
      by_cases hz : data[data.size - 1]! >>> UInt8.ofNat (length % 8) = 0 <;>
      simp [hr, hp, hz] <;> rfl
  · rename_i hs
    simp [Ssz.deserialize, hs]; rfl

private theorem delimited_outcome_eq_unpack (limit : Option Nat) (data : Ssz.Bytes) :
    delimitedOutcome limit data = (Ssz.unpackDelimited limit data).map Ssz.Value.bits := by
  by_cases he : data.size = 0
  · simp [delimitedOutcome, Ssz.unpackDelimited, he]; rfl
  · by_cases hz : data[data.size - 1]! = 0
    · by_cases ha : data.all (· == 0) = true <;>
        simp [delimitedOutcome, Ssz.unpackDelimited, he, hz, ha] <;> rfl
    · cases limit with
      | none => simp [delimitedOutcome, delimitedCount, Ssz.unpackDelimited, he, hz]; rfl
      | some cap =>
        by_cases hc : delimitedCount data ≤ cap
        · dsimp only [delimitedCount] at hc
          simp [delimitedOutcome, delimitedCount, Ssz.unpackDelimited, he, hz, hc,
            Nat.not_lt.mpr hc]; rfl
        · dsimp only [delimitedCount] at hc
          simp [delimitedOutcome, delimitedCount, Ssz.unpackDelimited, he, hz, hc,
            Nat.lt_of_not_ge hc]; rfl

theorem list_outcome_eq_deserialize (limit : Nat) (data : Ssz.Bytes) :
    delimitedOutcome (some limit) data = Ssz.deserialize (.bitList limit) data := by
  rw [delimited_outcome_eq_unpack]
  simp only [Ssz.deserialize]
  cases Ssz.unpackDelimited (some limit) data <;> rfl

theorem progressive_outcome_eq_deserialize (limit : Option Nat) (data : Ssz.Bytes) :
    delimitedOutcome limit data = Ssz.deserialize (.progressiveBitList limit) data := by
  rw [delimited_outcome_eq_unpack]
  simp only [Ssz.deserialize]
  cases Ssz.unpackDelimited limit data <;> rfl

set_option maxRecDepth 4096 in
theorem highestBit_log2 (byte : UInt8) : Ssz.highestBit byte = byte.toNat.log2 := by
  cases byte with
  | ofBitVec byte =>
    cases byte with
    | ofFin byte => revert byte; decide

set_option maxRecDepth 4096 in
theorem highestBit_lt (byte : UInt8) : Ssz.highestBit byte < 8 := by
  cases byte with
  | ofBitVec byte =>
    cases byte with
    | ofFin byte => revert byte; decide

/-- Native division and optional rounding compute the SSZ byte scope. -/
theorem rounded_byte_count (length : Nat) :
    (if length % 8 = 0 then length / 8 else length / 8 + 1) = (length + 7) / 8 := by
  split <;> omega

theorem exact_scope_quotient_small (length size : Nat)
    (scope : size = (length + 7) / 8) (physical : size < 2 ^ 64) :
    length / 8 < 2 ^ 64 ∧ (length % 8 ≠ 0 → length / 8 + 1 < 2 ^ 64) := by omega

/-- Exact byte scope itself rules out the native u128 representation error. -/
theorem vector_count_bound (length size : Nat)
    (scope : size = (length + 7) / 8) (physical : size < 2 ^ 64) :
    length < 2 ^ 67 := by omega

/-- A physical byte slice's delimited length is always representable in u128. -/
theorem delimited_count_bound (data : Ssz.Bytes) (physical : data.size < 2 ^ 64) :
    delimitedCount data < 2 ^ 67 := by
  have := highestBit_lt data[data.size - 1]!
  unfold delimitedCount
  omega

/-- Native from_u128 needs two limbs precisely above this byte-length threshold. -/
theorem delimited_count_large (data : Ssz.Bytes) :
    2 ^ 64 ≤ delimitedCount data ↔ 2 ^ 61 < data.size := by
  have := highestBit_lt data[data.size - 1]!
  unfold delimitedCount
  omega

/-- The borrowed byte count omits exactly a byte-aligned delimiter. -/
theorem delimited_byte_count (data : Ssz.Bytes) (nonempty : 0 < data.size) :
    (delimitedCount data + 7) / 8 =
      if Ssz.highestBit data[data.size - 1]! = 0 then data.size - 1 else data.size := by
  have := highestBit_lt data[data.size - 1]!
  unfold delimitedCount
  split <;> omega

/-- Dropping bytes beyond the logical bit length does not change its value. -/
theorem unpackBits_extract (data : Ssz.Bytes) (count keep : Nat)
    (room : count ≤ 8 * keep) (within : keep ≤ data.size) :
    Ssz.unpackBits (data.extract 0 keep) count = Ssz.unpackBits data count := by
  apply Array.ext
  · simp [Ssz.unpackBits]
  · intro i hi _
    have hi' : i < count := by simpa [Ssz.unpackBits] using hi
    have hk : i / 8 < keep := by omega
    have hd : i / 8 < data.size := by omega
    simp [Ssz.unpackBits, getElem!_pos, Array.size_extract, Nat.min_eq_left within, hk, hd]

theorem delimited_unpack_retained (data : Ssz.Bytes) (nonempty : 0 < data.size) :
    Ssz.unpackBits (data.extract 0 ((delimitedCount data + 7) / 8)) (delimitedCount data) =
      Ssz.unpackBits data (delimitedCount data) := by
  apply unpackBits_extract
  · omega
  · rw [delimited_byte_count data nonempty]
    split <;> omega

end SszNative.BitView
