import SszProofConstruction
import SszProofTraversalRefinement
import SszProofIndicesRefinement

set_option autoImplicit false

namespace SszNative.Proof

theorem fillHashRoots_refines (desc : Codec.Desc) (value : Codec.Value)
    (reservation : Arena.Reservation) (indices : List NatOperand) (position : Nat)
    (arena : Delimited.ArenaState) (safe : HashLayout.SafeWidths desc)
    (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (indicesPhysical : ∀ index ∈ indices, index.words.length < 2^64) :
    Refines Eq (fillHashRoots desc value reservation indices position arena)
      ((indices.map NatOperand.value).mapM (Ssz.nodeRoot desc.erase value.erase)) := by
  induction indices generalizing position arena with
  | nil => exact .ok [] [] rfl
  | cons index rest ih =>
      simp only [fillHashRoots, List.map_cons, List.mapM_cons]
      apply ResultRefines.bind Eq Eq _ _ _ _
        (nodeRoot_refines desc value index arena safe descPhysical valuePhysical
          (indicesPhysical index (by simp)))
      intro root expected same used
      subst expected
      change Refines Eq
        (bind (fillHashRoots desc value reservation rest (position + 1)
          { arena with used := used }) fun roots cursor => unchanged cursor (.ok (root :: roots))) _
      apply ResultRefines.bind Eq Eq _ _ _ _
        (ih (position + 1) { arena with used := used }
          (fun next member => indicesPhysical next (by simp [member])))
      intro roots expected same used'
      subst expected
      exact .ok _ _ rfl

theorem reserveHashRoots_refines (desc : Codec.Desc) (value : Codec.Value)
    (indices : List NatOperand) (arena : Delimited.ArenaState)
    (safe : HashLayout.SafeWidths desc) (descPhysical : desc.Physical)
    (valuePhysical : value.Physical)
    (indicesPhysical : ∀ index ∈ indices, index.words.length < 2^64) :
    Refines (fun slice values => slice.values = values) (reserveHashRoots desc value indices arena)
      ((indices.map NatOperand.value).mapM (Ssz.nodeRoot desc.erase value.erase)) := by
  unfold reserveHashRoots
  split
  · exact .exhausted .scratchExhausted trivial _
  · rename_i reservation reserved
    have filled := fillHashRoots_refines desc value reservation indices 0
      { arena with used := reservation.used } safe descPhysical valuePhysical indicesPhysical
    have mapped := ResultRefines.map Eq (fun slice values => slice.values = values)
      (fillHashRoots desc value reservation indices 0 { arena with used := reservation.used }).result
      ((indices.map NatOperand.value).mapM (Ssz.nodeRoot desc.erase value.erase))
      (fun roots => (⟨roots, reservation⟩ : HashSlice)) id filled
      (by intro left right same; exact same)
    simpa only [Except.map_id, id_eq] using mapped

/-- Success of the already-executed child is reflected without constraining any
later traversal. This adapter is shared by construction and reconstruction. -/
theorem liftIndices_success {α : Type} (arena : Delimited.ArenaState)
    (outcome : Indices.Outcome α) (value : α)
    (success : (liftIndices arena outcome).result = .ok value) : outcome.result = .ok value := by
  cases result : outcome.result with
  | error reason => simp only [liftIndices, result, Except.mapError] at success; cases success
  | ok actual =>
      simp only [liftIndices, result, Except.mapError, Except.ok.injEq] at success
      subst actual
      exact result

end SszNative.Proof
