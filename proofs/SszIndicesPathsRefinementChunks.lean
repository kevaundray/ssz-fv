import SszIndicesPathsRefinementPosition

set_option autoImplicit false

namespace SszNative.Indices

private def sequencePlaced (shape : Ssz.Desc) (position width : Nat) : Ssz.ChunkPosition :=
  match shape with
  | .bitVector _ | .bitList _ | .progressiveBitList _ => ⟨position / 256, 0, 0⟩
  | _ => ⟨position * width / 32, position * width % 32, position * width % 32 + width⟩

private theorem sequencePlaced_refines (shape : Codec.Desc) (position width : NatOperand)
    (base capacity used : Nat) :
    PathRefines ChunkPosition.erase (sequencePosition shape position width base capacity used).result
      (.ok (sequencePlaced shape.erase position.value width.value)) := by
  have refined := sequencePosition_refines shape position width base capacity used
  cases shape with
  | primitive shape => cases shape <;> exact refined
  | _ => exact refined

private theorem checkedPosition_refines (shape : Codec.Desc) (position width : NatOperand)
    (base capacity used : Nat) :
    PathRefines ChunkPosition.erase
      (bind (unchanged used (positionCount shape)) (fun count used =>
        if count.any (fun count => decide (position.value ≥ count.value)) then
          unchanged used (.error (.noSuchPosition position))
        else sequencePosition shape position width base capacity used)).result
      (do
        let count ← shape.erase.positionCount
        match count with
        | some count => if position.value ≥ count then throw (.noSuchPosition position.value)
        | none => pure ()
        return sequencePlaced shape.erase position.value width.value) := by
  apply PathRefines.bind _ _ (Option.map NatOperand.value) ChunkPosition.erase
    shape.erase.positionCount
    (fun count => do
      match count with
      | some count => if position.value ≥ count then throw (.noSuchPosition position.value)
      | none => pure ()
      return sequencePlaced shape.erase position.value width.value)
  · exact PathRefines.of_eq (positionCount_refines shape)
  · intro count returned
    cases count with
    | none => exact sequencePlaced_refines shape position width base capacity used
    | some count =>
        by_cases outside : position.value ≥ count.value
        · apply PathRefines.of_eq
          simp [outside, Option.any, unchanged, eraseResult] <;> rfl
        · simp [outside, Option.any]
          exact sequencePlaced_refines shape position width base capacity used

/-- Raw descriptor refinement, including element-lookup precedence, zero and
oversized widths, and masks whose active count differs from the field count. -/
theorem chunkPosition_refines (shape : Codec.Desc) (step : PathStep)
    (base capacity used : Nat) (physical : shape.Physical) :
    PathRefines ChunkPosition.erase (chunkPosition shape step base capacity used).result
      (shape.erase.chunkPosition step.erase) := by
  have pinned (erased : Ssz.Desc) (erasedStep : Ssz.PathStep) :
      erased.chunkPosition erasedStep =
        (erased.elementType erasedStep >>= fun element =>
          match erased, erasedStep with
          | .progressiveContainer active _ _, .position ordinal => do
              return ⟨← Ssz.layoutPosition active ordinal, 0, element.itemLength⟩
          | .container _ _, .position ordinal => .ok ⟨ordinal, 0, element.itemLength⟩
          | _, .position position => do
              let count ← erased.positionCount
              match count with
              | some count => if position ≥ count then throw (.noSuchPosition position)
              | none => pure ()
              return sequencePlaced erased position element.itemLength
          | _, _ => .error .notSteppable) := by
    cases erased <;> cases erasedStep <;> rfl
  rw [pinned shape.erase step.erase]
  unfold chunkPosition
  simp only [nativeCmp_not_lt_iff]
  apply PathRefines.bind _ _ Codec.Desc.erase ChunkPosition.erase
    (shape.erase.elementType step.erase)
    (fun element =>
      match shape.erase, step.erase with
      | .progressiveContainer active _ _, .position ordinal => do
          return ⟨← Ssz.layoutPosition active ordinal, 0, element.itemLength⟩
      | .container _ _, .position ordinal => .ok ⟨ordinal, 0, element.itemLength⟩
      | _, .position position => do
          let count ← shape.erase.positionCount
          match count with
          | some count => if position ≥ count then throw (.noSuchPosition position)
          | none => pure ()
          return sequencePlaced shape.erase position element.itemLength
      | _, _ => .error .notSteppable)
  · exact PathRefines.of_eq (elementType_refines shape step physical)
  · intro element reached
    have widthEq := itemLength_refines element
    cases shape with
    | progressiveContainer active fields =>
        cases step with
        | position ordinal =>
            apply PathRefines.bind _ _ NatOperand.value ChunkPosition.erase
              (Ssz.layoutPosition active ordinal.value)
              (fun position => .ok ⟨position, 0, element.erase.itemLength⟩)
            · exact PathRefines.of_eq
                (layoutPosition_refines active ordinal base capacity used physical.1)
            · intro position success
              apply PathRefines.of_eq
              simp only [unchanged, Except.map, eraseResult, ChunkPosition.erase,
                small_value, widthEq] <;> rfl
        | _ => exact PathRefines.of_eq rfl
    | container fields =>
        cases step with
        | position ordinal =>
            apply PathRefines.of_eq
            simp only [unchanged, Except.map, eraseResult, ChunkPosition.erase,
              small_value, widthEq] <;> rfl
        | _ => exact PathRefines.of_eq rfl
    | primitive primitive =>
        cases step with
        | position position =>
            have refined := checkedPosition_refines (.primitive primitive) position
              (itemLength element) base capacity used
            cases primitive <;>
              simpa only [widthEq, Codec.Desc.erase, Serialize.Desc.erase,
                PathStep.erase, unchanged] using refined
        | _ => cases primitive <;> exact PathRefines.of_eq rfl
    | vector child count =>
        cases step with
        | position position =>
            simpa only [widthEq, Codec.Desc.erase, PathStep.erase, unchanged] using
              checkedPosition_refines (.vector child count)
              position (itemLength element) base capacity used
        | _ => exact PathRefines.of_eq rfl
    | list child count =>
        cases step with
        | position position =>
            simpa only [widthEq, Codec.Desc.erase, PathStep.erase, unchanged] using
              checkedPosition_refines (.list child count)
              position (itemLength element) base capacity used
        | _ => exact PathRefines.of_eq rfl
    | progressiveList child count =>
        cases step with
        | position position =>
            simpa only [widthEq, Codec.Desc.erase, PathStep.erase, unchanged] using
              checkedPosition_refines (.progressiveList child count)
              position (itemLength element) base capacity used
        | _ => exact PathRefines.of_eq rfl
    | compatibleUnion variants =>
        cases step with
        | position position =>
            simpa only [widthEq, Codec.Desc.erase, PathStep.erase, unchanged] using
              checkedPosition_refines (.compatibleUnion variants)
              position (itemLength element) base capacity used
        | _ => exact PathRefines.of_eq rfl

end SszNative.Indices
