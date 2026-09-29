import SszIndicesPathsRefinement
import SszIndicesPowerSemanticPaths
import Ssz.Proofs.Merkle.Merkleize

set_option autoImplicit false

namespace SszNative.Indices

/-- Zero-width declarations are kept: they address chunk zero in a zero-capacity
layout. Every positive raw width, not only valid SSZ widths, satisfies the bound. -/
theorem raw_byte_chunk_bound (ordinal count width : Nat) (inside : ordinal < count) :
    ordinal * width / 32 < max ((count * width + 31) / 32) 1 := by
  by_cases zero : width = 0
  · simp [zero]
  · have offset := Nat.mul_lt_mul_of_pos_right inside (by omega : 0 < width)
    omega

 theorem raw_bit_chunk_bound (ordinal count : Nat) (inside : ordinal < count) :
    ordinal / 256 < max ((count + 255) / 256) 1 := by
  omega

/-- Capacity bounds are semantic consequences of successful raw positioning,
not declaration-validity premises. In particular the zero-width case is kept. -/
theorem chunkPosition_chunkCount_bound (shape : Ssz.Desc) (ordinal : Nat)
    (placed : Ssz.ChunkPosition) (count : Nat)
    (positioned : shape.chunkPosition (.position ordinal) = .ok placed)
    (counted : shape.chunkCount = .ok count) : placed.chunk < max count 1 := by
  have byteCase (capacity width : Nat)
      (success : (if ordinal ≥ capacity then
          Except.error (Ssz.Err.noSuchPosition ordinal)
        else Except.ok (⟨ordinal * width / 32, ordinal * width % 32,
          ordinal * width % 32 + width⟩ : Ssz.ChunkPosition)) = .ok placed)
      (countEq : count = (capacity * width + 31) / 32) :
      placed.chunk < max count 1 := by
    by_cases outside : ordinal ≥ capacity
    · simp [outside] at success
    · simp only [outside, ↓reduceIte, Except.ok.injEq] at success
      rw [← success, countEq]
      exact raw_byte_chunk_bound ordinal capacity width (by omega)
  have bitCase (capacity : Nat)
      (success : (if ordinal ≥ capacity then
          Except.error (Ssz.Err.noSuchPosition ordinal)
        else Except.ok (⟨ordinal / 256, 0, 0⟩ : Ssz.ChunkPosition)) = .ok placed)
      (countEq : count = (capacity + 255) / 256) :
      placed.chunk < max count 1 := by
    by_cases outside : ordinal ≥ capacity
    · simp [outside] at success
    · simp only [outside, ↓reduceIte, Except.ok.injEq] at success
      rw [← success, countEq]
      exact raw_bit_chunk_bound ordinal capacity (by omega)
  cases shape with
  | bool | uint _ | compatibleUnion _ _ =>
      change (Except.error Ssz.Err.notSteppable : Except Ssz.Err Ssz.ChunkPosition) =
        .ok placed at positioned
      cases positioned
  | progressiveBitList _ | progressiveList _ _ | progressiveContainer _ _ _ =>
      cases counted
  | vector element capacity | list element capacity =>
      apply byteCase capacity element.itemLength
      · change (if ordinal ≥ capacity then Except.error (Ssz.Err.noSuchPosition ordinal)
          else Except.ok (⟨ordinal * element.itemLength / 32,
            ordinal * element.itemLength % 32,
            ordinal * element.itemLength % 32 + element.itemLength⟩ : Ssz.ChunkPosition)) =
            .ok placed at positioned
        exact positioned
      · simpa [Ssz.Desc.chunkCount, Ssz.bytesPerChunk, Nat.add_sub_assoc] using
          (Except.ok.inj counted).symm
  | byteVector capacity | byteList capacity =>
      apply byteCase capacity 1
      · change (if ordinal ≥ capacity then Except.error (Ssz.Err.noSuchPosition ordinal)
          else Except.ok (⟨ordinal * 1 / 32, ordinal * 1 % 32,
            ordinal * 1 % 32 + 1⟩ : Ssz.ChunkPosition)) = .ok placed at positioned
        exact positioned
      · simpa [Ssz.Desc.chunkCount, Ssz.bytesPerChunk, Nat.add_sub_assoc] using
          (Except.ok.inj counted).symm
  | bitVector capacity | bitList capacity =>
      apply bitCase capacity
      · change (if ordinal ≥ capacity then Except.error (Ssz.Err.noSuchPosition ordinal)
          else Except.ok (⟨ordinal / 256, 0, 0⟩ : Ssz.ChunkPosition)) = .ok placed at positioned
        exact positioned
      · simpa [Ssz.Desc.chunkCount, Ssz.bytesPerChunk, Nat.add_sub_assoc] using
          (Except.ok.inj counted).symm
  | container names fields =>
      have countEq : count = fields.length := (Except.ok.inj counted).symm
      cases found : fields[ordinal]? with
      | none =>
          simp only [Ssz.Desc.chunkPosition, Ssz.Desc.elementType, found] at positioned
          change (Except.error (Ssz.Err.noSuchField ordinal) :
            Except Ssz.Err Ssz.ChunkPosition) = .ok placed at positioned
          cases positioned
      | some field =>
          have inside : ordinal < fields.length := by
            by_cases bound : ordinal < fields.length
            · exact bound
            · have absent := List.getElem?_eq_none (by omega : fields.length ≤ ordinal)
              rw [absent] at found
              cases found
          simp only [Ssz.Desc.chunkPosition, Ssz.Desc.elementType, found,
            Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at positioned
          rw [← positioned, countEq]
          exact Nat.lt_of_lt_of_le inside (Nat.le_max_left _ _)

/-- The source rebase truncation is harmless exactly because a successful raw
bounded position lies below the power-of-two capacity. -/
theorem rebase_bounded_leaf (chunk count : Nat) (mixed : Bool)
    (inside : chunk < max count 1) :
    Ssz.gindexRebase chunk (Ssz.depthFor count + if mixed then 1 else 0) =
      2 ^ (Ssz.depthFor count + if mixed then 1 else 0) + chunk := by
  have capacity := Ssz.le_two_pow_depthFor count
  have positive := Nat.two_pow_pos (Ssz.depthFor count)
  have below : chunk < 2 ^ Ssz.depthFor count := by omega
  have grows : 2 ^ Ssz.depthFor count ≤
      2 ^ (Ssz.depthFor count + if mixed then 1 else 0) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  simp only [Ssz.gindexRebase, Ssz.gindexBelow,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le below grows)]

 theorem concat_bounded_leaf (chunk count : Nat) (inside : chunk < max count 1) :
    Ssz.gindexConcat 2 (Ssz.nextPow2 count + chunk) =
      .ok (2 ^ (Ssz.depthFor count + 1) + chunk) := by
  have capacity := Ssz.le_two_pow_depthFor count
  have positive := Nat.two_pow_pos (Ssz.depthFor count)
  have below : chunk < 2 ^ Ssz.depthFor count := by omega
  have logarithm : (2 ^ Ssz.depthFor count + chunk).log2 = Ssz.depthFor count := by
    apply (Nat.log2_eq_iff (by omega)).mpr
    constructor
    · omega
    · rw [Nat.pow_succ]
      omega
  rw [Ssz.nextPow2, Ssz.gindexConcat_eq (by decide) (by omega), logarithm,
    Nat.pow_succ]
  congr 1
  omega

end SszNative.Indices
