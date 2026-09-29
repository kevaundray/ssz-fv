import SszX86.CodecIsFixedStack
import SszX86.CodecStack

namespace SszX86.CodecIsFixed
open SszNative

mutual
  /-- One 32-byte allowance per structural level covers the 24-byte activation
  and its caller's eight-byte return slot. Vector iteration needs no extra slot. -/
  theorem stackBytes_depth (desc : SszNative.Codec.Desc) :
      stackBytes desc + 8 ≤ 32 * desc.nesting := by
    cases desc with
    | primitive shape =>
      cases shape <;> simp only [stackBytes, Codec.Desc.nesting, Codec.Desc.erase,
        Serialize.Desc.erase, Ssz.Desc.nesting] <;> decide
    | vector element length =>
      have child := stackBytes_depth element
      simp only [stackBytes, Codec.Desc.nesting, Codec.Desc.erase, Ssz.Desc.nesting]
      change stackBytes element + 8 ≤ 32 * (element.nesting + 1)
      omega
    | container fields =>
      have fieldsBound := fieldsStackBytes_depth fields
      simp only [stackBytes, Codec.Desc.nesting, Codec.Desc.erase, Ssz.Desc.nesting]
      omega
    | progressiveContainer active fields =>
      have fieldsBound := fieldsStackBytes_depth fields
      simp only [stackBytes, Codec.Desc.nesting, Codec.Desc.erase, Ssz.Desc.nesting]
      omega
    | list element limit | progressiveList element limit | compatibleUnion variants =>
      simp only [stackBytes, Codec.Desc.nesting, Codec.Desc.erase, Ssz.Desc.nesting]
      omega

  theorem fieldsStackBytes_depth (fields : List (String × SszNative.Codec.Desc)) :
      fieldsStackBytes fields ≤ 32 * Ssz.Desc.deepestNesting (Codec.Desc.eraseFields fields) := by
    cases fields with
    | nil => exact Nat.le_refl _
    | cons field rest =>
      rcases field with ⟨name, desc⟩
      have child := stackBytes_depth desc
      have remaining := fieldsStackBytes_depth rest
      have left := Nat.le_max_left desc.nesting (Ssz.Desc.deepestNesting (Codec.Desc.eraseFields rest))
      have right := Nat.le_max_right desc.nesting (Ssz.Desc.deepestNesting (Codec.Desc.eraseFields rest))
      have childMax := Nat.mul_le_mul_left 32 left
      have restMax := Nat.mul_le_mul_left 32 right
      simp only [fieldsStackBytes, Codec.Desc.eraseFields, Ssz.Desc.deepestNesting]
      change max (8 + stackBytes desc) (fieldsStackBytes rest) ≤
        32 * max desc.nesting (Ssz.Desc.deepestNesting (Codec.Desc.eraseFields rest))
      omega
end

/-- Callers using the shared recursive codec envelope can derive the exact
classifier demand without introducing a leaf-only stack cap. -/
theorem stackBytes_le_descriptorStackBytes (desc : SszNative.Codec.Desc) (helperBytes : Nat) :
    stackBytes desc ≤ Codec.descriptorStackBytes desc helperBytes := by
  have depth := stackBytes_depth desc
  have layer : 32 ≤ Codec.codecLayerBytes := by decide
  have multiplied := Nat.mul_le_mul_right desc.nesting layer
  unfold Codec.descriptorStackBytes Codec.recursiveStackBytes
  rw [Nat.add_mul]
  rw [Nat.mul_comm Codec.codecLayerBytes desc.nesting] at multiplied
  omega

end SszX86.CodecIsFixed
