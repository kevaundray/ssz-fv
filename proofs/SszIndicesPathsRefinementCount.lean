import SszIndicesPathsRefinementArithmetic
import SszIndicesPowerSemanticPaths
import SszIndicesPathsPhysical

set_option autoImplicit false

namespace SszNative.Indices

private theorem sequenceCount_refines (element : Codec.Desc) (count : NatOperand)
    (base capacity used : Nat) (elementPhysical : element.Physical)
    (countPhysical : Physical count) :
    PathRefines NatOperand.value
      (match packingShift (itemLength element) with
      | some shift => ceilShift count shift base capacity used
      | none => bind (arithmetic used (NatMul.run count (itemLength element) base capacity used))
          (fun product used => ceilShift product 5 base capacity used)).result
      (.ok ((count.value * element.erase.itemLength + 31) / 32)) := by
  have widthEq := itemLength_refines element
  have widthPhysical := itemLength_physical element elementPhysical
  cases packed : packingShift (itemLength element) with
  | some shift =>
      have bound := (packingShift_spec (itemLength element) shift packed).1
      have refined := ceilShift_path_refines count shift base capacity used countPhysical (by omega)
      rw [← packed_ceil_identity count.value (itemLength element) shift packed,
        widthEq] at refined
      exact refined
  | none =>
      rw [← widthEq]
      apply PathRefines.bind _ _ NatOperand.value NatOperand.value
        (.ok (count.value * (itemLength element).value))
        (fun product => .ok ((product + 31) / 32))
      · exact PathRefines.arithmetic _ _ _
          (NatMul.run_value count (itemLength element) base capacity used)
      · intro product success
        have multiplied := (arithmetic_success_iff used _ product).mp success
        have physical := mul_physical count (itemLength element) base capacity used
          countPhysical widthPhysical product multiplied
        simpa only [Nat.reducePow, Nat.add_sub_assoc] using
          ceilShift_path_refines product 5 base capacity _ physical (by decide)

/-- Every raw descriptor is covered. Physical field counts, not declaration
validity or logical metadata caps, justify the source usize-to-u128 conversion. -/
theorem chunkCount_refines (shape : Codec.Desc) (base capacity used : Nat)
    (physical : shape.Physical) :
    PathRefines NatOperand.value (chunkCount shape base capacity used).result
      shape.erase.chunkCount := by
  cases shape with
  | primitive primitive =>
      cases primitive with
      | bool | uint _ => exact PathRefines.ok _ _
      | byteVector count | byteList count =>
          have countPhysical := operandSliceSized_physical count physical
          simpa only [chunkCount, Codec.Desc.erase, Serialize.Desc.erase, Ssz.Desc.chunkCount,
            Ssz.bytesPerChunk, Nat.reducePow] using
            ceilShift_path_refines count 5 base capacity used countPhysical (by decide)
      | bitVector count | bitList count =>
          have countPhysical := operandSliceSized_physical count physical
          simpa only [chunkCount, Codec.Desc.erase, Serialize.Desc.erase, Ssz.Desc.chunkCount,
            Ssz.bytesPerChunk, Nat.reducePow, Nat.reduceMul] using
            ceilShift_path_refines count 8 base capacity used countPhysical (by decide)
      | progressiveBitList _ => exact PathRefines.of_eq rfl
  | vector element count | list element count =>
      simpa only [chunkCount, Codec.Desc.erase, Ssz.Desc.chunkCount,
        Ssz.bytesPerChunk, Nat.add_sub_assoc] using
        sequenceCount_refines element count base capacity used physical.1
          (operandSliceSized_physical count physical.2)
  | progressiveList _ _ | progressiveContainer _ _ => exact PathRefines.of_eq rfl
  | compatibleUnion _ => exact PathRefines.ok _ _
  | container fields =>
      apply PathRefines.arithmetic
      intro result success
      rw [NatArithmetic.fromWide_value base capacity used (BitVec.ofNat 128 fields.length)
        result success, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact (Codec.Desc.eraseFields_length fields).symm

end SszNative.Indices
