import SszIndicesPathsRefinementChunks
import SszIndicesPathsRefinementCount
import SszIndicesPathsRefinementBounds

set_option autoImplicit false

namespace SszNative.Indices

def eraseResolved (result : NatOperand × Option Codec.Desc) : Nat × Option Ssz.Desc :=
  (result.1.value, result.2.map Codec.Desc.erase)

private theorem finishPosition_refines (shape : Codec.Desc) (ordinal index : NatOperand)
    (used : Nat) (physical : shape.Physical) :
    PathRefines eraseResolved
      (unchanged used ((elementType shape (.position ordinal)).map
        (fun child => (index, some child)))).result
      ((shape.erase.elementType (.position ordinal.value)).map
        (fun child => (index.value, some child))) := by
  exact PathRefines.map _ Codec.Desc.erase _ (fun child => (index, some child))
    (fun child => (index.value, some child)) eraseResolved (fun _ => rfl)
    (PathRefines.of_eq (elementType_refines shape (.position ordinal) physical))

private def boundedRelative (shape : Ssz.Desc) (leaf : Nat) : Except Ssz.Err Nat :=
  match shape with
  | .list _ _ | .byteList _ | .bitList _ => Ssz.gindexConcat 2 leaf
  | _ => .ok leaf

private theorem boundedRelative_rebase (shape : Codec.Desc) (chunk count : Nat)
    (inside : chunk < max count 1) :
    boundedRelative shape.erase (Ssz.nextPow2 count + chunk) =
      .ok (Ssz.gindexRebase chunk (Ssz.depthFor count + if isBoundedList shape then 1 else 0)) := by
  rw [rebase_bounded_leaf chunk count (isBoundedList shape) inside]
  cases shape with
  | primitive shape =>
      cases shape <;>
        simp only [Codec.Desc.erase, Serialize.Desc.erase, boundedRelative, isBoundedList,
          Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Ssz.nextPow2] <;>
        first | rfl | exact concat_bounded_leaf chunk count inside
  | _ =>
      simp only [Codec.Desc.erase, boundedRelative, isBoundedList,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Ssz.nextPow2] <;>
        first | rfl | exact concat_bounded_leaf chunk count inside

private theorem progressivePosition_refines (shape : Codec.Desc) (ordinal : NatOperand)
    (base capacity used : Nat) (physical : shape.Physical) (ordinalPhysical : Physical ordinal) :
    PathRefines eraseResolved
      (bind (chunkPosition shape (.position ordinal) base capacity used) (fun placed used =>
        bind (progressiveChunkIndex placed.chunk base capacity used) (fun index used =>
          unchanged used ((elementType shape (.position ordinal)).map
            (fun child => (index, some child)))))).result
      (do
        let placed ← shape.erase.chunkPosition (.position ordinal.value)
        return (Ssz.progressiveChunkGindex placed.chunk,
          some (← shape.erase.elementType (.position ordinal.value)))) := by
  apply PathRefines.bind _ _ ChunkPosition.erase eraseResolved
    (shape.erase.chunkPosition (.position ordinal.value))
    (fun placed => (shape.erase.elementType (.position ordinal.value)).map
      (fun child => (Ssz.progressiveChunkGindex placed.chunk, some child)))
  · exact chunkPosition_refines shape (.position ordinal) base capacity used physical
  · intro placed positioned
    have placedPhysical := chunkPosition_success_physical shape (.position ordinal)
      base capacity used physical ordinalPhysical placed positioned
    apply PathRefines.bind _ _ NatOperand.value eraseResolved
      (.ok (Ssz.progressiveChunkGindex placed.chunk.value))
      (fun index => (shape.erase.elementType (.position ordinal.value)).map
        (fun child => (index, some child)))
    · exact progressiveChunkIndex_path_refines placed.chunk base capacity _ placedPhysical
    · intro index indexed
      exact finishPosition_refines shape ordinal index _ physical

private theorem boundedPosition_refines (shape : Codec.Desc) (ordinal : NatOperand)
    (base capacity used : Nat) (physical : shape.Physical) (ordinalPhysical : Physical ordinal) :
    PathRefines eraseResolved
      (bind (chunkPosition shape (.position ordinal) base capacity used) (fun placed used =>
        bind (chunkCount shape base capacity used) (fun count used =>
          bind (rebase placed.chunk
            (leafDepth count + if isBoundedList shape then 1 else 0) base capacity used)
            (fun index used => unchanged used ((elementType shape (.position ordinal)).map
              (fun child => (index, some child))))))).result
      (do
        let placed ← shape.erase.chunkPosition (.position ordinal.value)
        let count ← shape.erase.chunkCount
        let index ← boundedRelative shape.erase (Ssz.nextPow2 count + placed.chunk)
        return (index, some (← shape.erase.elementType (.position ordinal.value)))) := by
  apply PathRefines.bind _ _ ChunkPosition.erase eraseResolved
    (shape.erase.chunkPosition (.position ordinal.value))
    (fun placed => do
      let count ← shape.erase.chunkCount
      let index ← boundedRelative shape.erase (Ssz.nextPow2 count + placed.chunk)
      return (index, some (← shape.erase.elementType (.position ordinal.value))))
  · exact chunkPosition_refines shape (.position ordinal) base capacity used physical
  · intro placed positioned
    have placedPhysical := chunkPosition_success_physical shape (.position ordinal)
      base capacity used physical ordinalPhysical placed positioned
    have placedEq := (chunkPosition_refines shape (.position ordinal) base capacity used
      physical).success placed positioned
    apply PathRefines.bind _ _ NatOperand.value eraseResolved shape.erase.chunkCount
      (fun count => do
        let index ← boundedRelative shape.erase (Ssz.nextPow2 count + placed.chunk.value)
        return (index, some (← shape.erase.elementType (.position ordinal.value))))
    · exact chunkCount_refines shape base capacity _ physical
    · intro count counted
      have countEq := (chunkCount_refines shape base capacity _ physical).success count counted
      have inside := chunkPosition_chunkCount_bound shape.erase ordinal.value placed.erase
        count.value placedEq countEq
      rw [boundedRelative_rebase shape placed.chunk.value count.value inside]
      simp only [Bind.bind, Except.bind]
      rw [leafDepth_refines count]
      apply PathRefines.bind _ _ NatOperand.value eraseResolved
        (.ok (Ssz.gindexRebase placed.chunk.value
          (Ssz.depthFor count.value + if isBoundedList shape then 1 else 0)))
        (fun index => (shape.erase.elementType (.position ordinal.value)).map
          (fun child => (index, some child)))
      · exact rebase_path_refines placed.chunk _ base capacity _ placedPhysical
      · intro index indexed
        exact finishPosition_refines shape ordinal index _ physical

/-- `resolvePosition` is the internal positional dispatcher. Its direct basic
case is NotSteppable; `resolveStep` deliberately intercepts that case as NoParts.
This explicit target preserves that source distinction rather than asserting an
incorrect universal equivalence for the unguarded internal helper. -/
theorem resolvePosition_refines (shape : Codec.Desc) (ordinal : NatOperand)
    (base capacity used : Nat) (physical : shape.Physical) (ordinalPhysical : Physical ordinal) :
    PathRefines eraseResolved (resolvePosition shape ordinal base capacity used).result
      (match shape with
      | .primitive .bool | .primitive (.uint _) => .error .notSteppable
      | _ => shape.erase.resolveStep (.position ordinal.value)) := by
  cases shape with
  | compatibleUnion variants =>
      apply PathRefines.of_eq
      have bridge := unionOption_refines variants ordinal
      cases found : unionOption variants ordinal with
      | none =>
          cases selected : (variants.map (fun variant => variant.1.value)).idxOf? ordinal.value <;>
            simp_all [resolvePosition, unchanged, eraseResult, eraseResolved,
              Codec.Desc.erase, Ssz.Desc.resolveStep]
      | some child =>
          cases selected : (variants.map (fun variant => variant.1.value)).idxOf? ordinal.value <;>
            simp_all [resolvePosition, unchanged, eraseResult, eraseResolved,
              Codec.Desc.erase, Ssz.Desc.resolveStep, small_value]
  | progressiveContainer active fields =>
      exact progressivePosition_refines _ ordinal base capacity used physical ordinalPhysical
  | progressiveList element limit =>
      exact progressivePosition_refines _ ordinal base capacity used physical ordinalPhysical
  | primitive primitive =>
      cases primitive with
      | bool | uint _ =>
          exact PathRefines.of_eq rfl
      | progressiveBitList limit =>
          exact progressivePosition_refines _ ordinal base capacity used physical ordinalPhysical
      | _ => exact boundedPosition_refines _ ordinal base capacity used physical ordinalPhysical
  | _ => exact boundedPosition_refines _ ordinal base capacity used physical ordinalPhysical

/-- All raw declarations and all step kinds, with exact semantic error precedence. -/
theorem resolveStep_refines (shape : Codec.Desc) (step : PathStep)
    (base capacity used : Nat) (physical : shape.Physical) (stepPhysical : step.Physical) :
    PathRefines eraseResolved (resolveStep shape step base capacity used).result
      (shape.erase.resolveStep step.erase) := by
  cases shape with
  | primitive primitive =>
      cases primitive with
      | bool | uint _ => exact PathRefines.of_eq rfl
      | _ =>
          cases step with
          | position ordinal =>
              exact resolvePosition_refines _ ordinal base capacity used physical stepPhysical
          | _ =>
              apply PathRefines.of_eq
              simp [resolveStep, Ssz.Desc.resolveStep, Codec.Desc.erase, Serialize.Desc.erase,
                PathStep.erase, mixesIn_refines, unchanged, eraseResult, eraseResolved,
                Ssz.Desc.mixesIn, small_value]
  | _ =>
      cases step with
      | position ordinal =>
          exact resolvePosition_refines _ ordinal base capacity used physical stepPhysical
      | _ =>
          apply PathRefines.of_eq
          simp [resolveStep, Ssz.Desc.resolveStep, Codec.Desc.erase, PathStep.erase,
            mixesIn_refines, unchanged, eraseResult, eraseResolved, Ssz.Desc.mixesIn, small_value]

end SszNative.Indices
