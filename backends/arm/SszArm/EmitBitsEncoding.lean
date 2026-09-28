import SszArm.EmitBitsMask

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open SszNative.PackedBits (canonicalBytes delimitedBytes)

/-- The output observation is assembled from the copied full-byte prefix and
only the real optional vector tail. Empty vectors require no output observation. -/
theorem canonical_at (load : Nat → Nat → Option Nat) (address : Nat) (bits : Packed)
    (copiedPrefix : ∀ index, index < bits.count.toNat / 8 →
      load (address + index) 1 = some (bits.bytes[index]?.getD 0).toNat)
    (tail : bits.count.toNat % 8 ≠ 0 → load (address + bits.count.toNat / 8) 1 =
      some (bits.bytes[bits.count.toNat / 8]! &&& UInt8.ofNat (2 ^ (bits.count.toNat % 8) - 1)).toNat) :
    SszNative.ByteView.BytesAt load address (canonicalBytes bits.bytes bits.count.toNat) := by
  have full := (backing_guards bits).1
  have prefixSize : (bits.bytes.extract 0 (bits.count.toNat / 8)).size = bits.count.toNat / 8 := by
    simp [Array.size_extract, Nat.min_eq_left full]
  intro index inside
  by_cases aligned : bits.count.toNat % 8 = 0
  · have before : index < bits.count.toNat / 8 := by
      simpa [canonicalBytes, aligned, prefixSize] using inside
    simpa [canonicalBytes, aligned, Array.getElem?_extract, Nat.min_eq_left full, before,
      Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le before full)] using copiedPrefix index before
  · have bound : index < bits.count.toNat / 8 + 1 := by
      simpa [canonicalBytes, aligned, prefixSize] using inside
    by_cases before : index < bits.count.toNat / 8
    · simpa [canonicalBytes, aligned, Array.getElem?_push, prefixSize,
        show index ≠ bits.count.toNat / 8 by omega, Array.getElem?_extract,
        Nat.min_eq_left full, before, Array.getElem_push,
        Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le before full)] using copiedPrefix index before
    · have atTail : index = bits.count.toNat / 8 := by omega
      subst index
      simpa [canonicalBytes, aligned, Array.getElem?_push, Array.getElem_push, prefixSize] using tail aligned

/-- Every list, including zero or byte-aligned counts, has one mandatory final
byte. The prefix never supplies an old output value for that byte. -/
theorem delimited_at (load : Nat → Nat → Option Nat) (address : Nat) (bits : Packed)
    (copiedPrefix : ∀ index, index < bits.count.toNat / 8 →
      load (address + index) 1 = some (bits.bytes[index]?.getD 0).toNat)
    (tail : load (address + bits.count.toNat / 8) 1 =
      some (if bits.count.toNat % 8 = 0 then (1 : UInt8) else
        (bits.bytes[bits.count.toNat / 8]! &&& UInt8.ofNat (2 ^ (bits.count.toNat % 8) - 1)) |||
          (1 <<< UInt8.ofNat (bits.count.toNat % 8))).toNat) :
    SszNative.ByteView.BytesAt load address (delimitedBytes bits.bytes bits.count.toNat) := by
  have full := (backing_guards bits).1
  have prefixSize : (bits.bytes.extract 0 (bits.count.toNat / 8)).size = bits.count.toNat / 8 := by
    simp [Array.size_extract, Nat.min_eq_left full]
  intro index inside
  have bound : index < bits.count.toNat / 8 + 1 := by
    simpa [delimitedBytes, prefixSize] using inside
  by_cases before : index < bits.count.toNat / 8
  · simpa [delimitedBytes, Array.getElem?_push, prefixSize,
      show index ≠ bits.count.toNat / 8 by omega, Array.getElem?_extract,
      Nat.min_eq_left full, before, Array.getElem_push,
      Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le before full)] using copiedPrefix index before
  · have atTail : index = bits.count.toNat / 8 := by omega
    subst index
    simpa [delimitedBytes, Array.getElem?_push, Array.getElem_push, prefixSize] using tail

theorem list_emit (desc : Desc) (bits : Packed) (kind : IsList desc) :
    SszNative.Serialize.emit desc (.bits bits) = delimitedBytes bits.bytes bits.count.toNat := by
  cases desc <;> try cases kind
  all_goals rfl

end SszArm.Emit.Bits
