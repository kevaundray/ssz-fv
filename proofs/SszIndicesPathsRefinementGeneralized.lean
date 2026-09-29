import SszIndicesPathsRefinementResolve

set_option autoImplicit false

namespace SszNative.Indices

/-- Source recursion refines pinned paths on every raw physical descriptor.
Relative-index allocation happens before descent, and concat is proved only
on unwind; neither schema validity nor successful future calls are premises. -/
theorem generalizedIndex_refines (shape : Codec.Desc) (path : List PathStep)
    (base capacity used : Nat) (physical : shape.Physical)
    (pathPhysical : ∀ step ∈ path, step.Physical) :
    PathRefines NatOperand.value (generalizedIndex shape path base capacity used).result
      (Ssz.getGeneralizedIndex shape.erase (path.map PathStep.erase)) := by
  induction path generalizing shape used with
  | nil => exact PathRefines.of_eq (generalizedIndex_nil_refines shape base capacity used)
  | cons step rest ih =>
      have stepPhysical := pathPhysical step (by simp)
      have restPhysical : ∀ next ∈ rest, next.Physical :=
        fun next member => pathPhysical next (List.mem_cons_of_mem step member)
      unfold generalizedIndex
      simp only [List.map_cons, Ssz.getGeneralizedIndex, List.isEmpty_map]
      apply PathRefines.bind _ _ eraseResolved NatOperand.value
        (shape.erase.resolveStep step.erase)
        (fun resolved =>
          match resolved.2 with
          | none => if rest.isEmpty then .ok resolved.1 else .error .noPartsMixin
          | some child => Ssz.getGeneralizedIndex child (rest.map PathStep.erase) >>=
              Ssz.gindexConcat resolved.1)
      · exact resolveStep_refines shape step base capacity used physical stepPhysical
      · intro resolved returned
        have resolvedPhysical := resolveStep_success_physical shape step base capacity used
          physical stepPhysical resolved returned
        obtain ⟨index, target⟩ := resolved
        cases target with
        | none =>
            cases rest with
            | nil => exact PathRefines.ok _ _
            | cons next rest => exact PathRefines.of_eq rfl
        | some child =>
            have childPhysical := resolvedPhysical.2 child rfl
            apply PathRefines.bind _ _ NatOperand.value NatOperand.value
              (Ssz.getGeneralizedIndex child.erase (rest.map PathStep.erase))
              (Ssz.gindexConcat index.value)
            · exact ih child _ childPhysical restPhysical
            · intro inner recursed
              have innerPhysical := generalizedIndex_success_physical child rest base capacity _
                childPhysical restPhysical inner recursed
              exact concat_path_refines index inner base capacity _ resolvedPhysical.1 innerPhysical

/-- Successful outputs expose the exact pinned index, not merely its depth. -/
theorem generalizedIndex_success_refines (shape : Codec.Desc) (path : List PathStep)
    (base capacity used : Nat) (physical : shape.Physical)
    (pathPhysical : ∀ step ∈ path, step.Physical) (result : NatOperand)
    (success : (generalizedIndex shape path base capacity used).result = .ok result) :
    Ssz.getGeneralizedIndex shape.erase (path.map PathStep.erase) = .ok result.value :=
  (generalizedIndex_refines shape path base capacity used physical pathPhysical).success result success

/-- Host success includes semantic refusals. This is the resource-success
contract: every original error payload is erased exactly and is checked against
the pinned result, while arithmetic failures remain explicit outer host errors. -/
theorem generalizedIndex_semantic_result (shape : Codec.Desc) (path : List PathStep)
    (base capacity used : Nat) (physical : shape.Physical)
    (pathPhysical : ∀ step ∈ path, step.Physical) (observed : Except Ssz.Err Nat)
    (returned : eraseResult
      ((generalizedIndex shape path base capacity used).result.map NatOperand.value) = .ok observed) :
    observed = Ssz.getGeneralizedIndex shape.erase (path.map PathStep.erase) :=
  generalizedIndex_refines shape path base capacity used physical pathPhysical observed returned

/-- Duplicate selectors use the first physical variant, including invalid basic
children and noncanonical or arbitrarily large matching selector operands. -/
theorem union_duplicate_first_refines (selector ordinal : NatOperand)
    (first second : Codec.Desc) (rest : List (NatOperand × Codec.Desc))
    (same : selector.value = ordinal.value) :
    (Codec.Desc.compatibleUnion ((selector, first) :: (selector, second) :: rest)).erase.resolveStep
      (.position ordinal.value) = .ok (2, some first.erase) := by
  simp [Codec.Desc.erase, Codec.Desc.eraseVariants, Ssz.Desc.resolveStep,
    List.idxOf?_cons, same]

end SszNative.Indices
