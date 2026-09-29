import SszProofMultiPureTree

set_option autoImplicit false

namespace SszNative.Proof

/-- The native stable-compaction ordering, expressed over logical index/value
pairs. Sibling lookups all observe the original level frontier. -/
def stableFoldLevelNodes (depth : Nat) (nodes : List (Nat × Ssz.Bytes)) :
    List (Nat × Ssz.Bytes) → Except Ssz.Err (List (Nat × Ssz.Bytes))
  | [] => .ok []
  | (index, node) :: rest => do
      if Ssz.levelOf index != depth then
        return (index, node) :: (← stableFoldLevelNodes depth nodes rest)
      else if index % 2 == 0 then
        match Ssz.nodeAt nodes (index + 1) with
        | some sibling =>
            return (Ssz.gindexParent index, Ssz.combine node sibling) ::
              (← stableFoldLevelNodes depth nodes rest)
        | none => throw .proofIncomplete
      else if (Ssz.nodeAt nodes (index - 1)).isNone then
        throw .proofIncomplete
      else stableFoldLevelNodes depth nodes rest

def stableFoldLevel (depth : Nat) (nodes : List (Nat × Ssz.Bytes)) :
    Except Ssz.Err (List (Nat × Ssz.Bytes)) := stableFoldLevelNodes depth nodes nodes

private theorem cons_append_perm {α : Type} (a : α) (left right : List α) :
    (a :: (left ++ right)).Perm (left ++ a :: right) := by
  induction left with
  | nil => exact .refl _
  | cons b tail ih => exact (List.Perm.swap _ _ _).trans (.cons b ih)

/-- Relating the differently ordered results includes all error paths, rather
than presupposing reconstruction success or readable supplied claims. -/
def StableLevelRelation : Except Ssz.Err (List (Nat × Ssz.Bytes)) →
    Except Ssz.Err (List (Nat × Ssz.Bytes) × List (Nat × Ssz.Bytes)) → Prop
  | .ok stable, .ok (parents, kept) => stable.Perm (parents ++ kept)
  | .error first, .error second => first = second
  | _, _ => False

theorem stableFoldLevelNodes_relation (depth : Nat) (nodes pending : List (Nat × Ssz.Bytes)) :
    StableLevelRelation (stableFoldLevelNodes depth nodes pending)
      (Ssz.foldLevelNodes depth nodes pending) := by
  induction pending with
  | nil => exact List.Perm.refl []
  | cons pair rest ih =>
      rcases pair with ⟨index, value⟩
      by_cases atDepth : Ssz.levelOf index = depth
      · by_cases even : index % 2 = 0
        · cases sibling : Ssz.nodeAt nodes (index + 1) with
          | none =>
              simp [stableFoldLevelNodes, Ssz.foldLevelNodes, atDepth, even, sibling,
                StableLevelRelation, throw]
              rfl
          | some siblingValue =>
              cases native : stableFoldLevelNodes depth nodes rest with
              | error first =>
                  cases pinned : Ssz.foldLevelNodes depth nodes rest with
                  | error second =>
                      simpa [stableFoldLevelNodes, Ssz.foldLevelNodes, atDepth, even,
                        sibling, native, pinned, StableLevelRelation,
                        Bind.bind, Except.bind] using ih
                  | ok groups => simp [native, pinned, StableLevelRelation] at ih
              | ok stable =>
                  cases pinned : Ssz.foldLevelNodes depth nodes rest with
                  | error second => simp [native, pinned, StableLevelRelation] at ih
                  | ok groups =>
                      rcases groups with ⟨parents, kept⟩
                      have perm : stable.Perm (parents ++ kept) := by
                        simpa [native, pinned, StableLevelRelation] using ih
                      simpa [stableFoldLevelNodes, Ssz.foldLevelNodes, atDepth, even,
                        sibling, native, pinned, StableLevelRelation, Bind.bind,
                        Except.bind, Pure.pure, Except.pure] using
                        List.Perm.cons (Ssz.gindexParent index, Ssz.combine value siblingValue) perm
        · by_cases missing : (Ssz.nodeAt nodes (index - 1)).isNone = true
          · simp [stableFoldLevelNodes, Ssz.foldLevelNodes, atDepth, even, missing,
              StableLevelRelation, throw]
            rfl
          · simpa [stableFoldLevelNodes, Ssz.foldLevelNodes, atDepth, even, missing] using ih
      · cases native : stableFoldLevelNodes depth nodes rest with
        | error first =>
            cases pinned : Ssz.foldLevelNodes depth nodes rest with
            | error second =>
                simpa [stableFoldLevelNodes, Ssz.foldLevelNodes, atDepth, native, pinned,
                  StableLevelRelation, Bind.bind, Except.bind] using ih
            | ok groups => simp [native, pinned, StableLevelRelation] at ih
        | ok stable =>
            cases pinned : Ssz.foldLevelNodes depth nodes rest with
            | error second => simp [native, pinned, StableLevelRelation] at ih
            | ok groups =>
                rcases groups with ⟨parents, kept⟩
                have perm : stable.Perm (parents ++ kept) := by
                  simpa [native, pinned, StableLevelRelation] using ih
                have combined := (List.Perm.cons (index, value) perm).trans
                  (cons_append_perm (index, value) parents kept)
                simpa [stableFoldLevelNodes, Ssz.foldLevelNodes, atDepth, native, pinned,
                  StableLevelRelation, Bind.bind, Except.bind, Pure.pure, Except.pure]
                  using combined

theorem stableFoldLevel_success {depth : Nat} {nodes stable : List (Nat × Ssz.Bytes)}
    (success : stableFoldLevel depth nodes = .ok stable) :
    ∃ pinned, Ssz.foldLevel depth nodes = .ok pinned ∧ stable.Perm pinned := by
  have related := stableFoldLevelNodes_relation depth nodes nodes
  change stableFoldLevelNodes depth nodes nodes = .ok stable at success
  rw [success] at related
  cases folded : Ssz.foldLevelNodes depth nodes nodes with
  | error reason => simp [folded, StableLevelRelation] at related
  | ok groups =>
      rcases groups with ⟨parents, kept⟩
      refine ⟨parents ++ kept, ?_, ?_⟩
      · simp [Ssz.foldLevel, folded, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · simpa [folded, StableLevelRelation] using related

theorem stableFoldLevel_error {depth : Nat} {nodes : List (Nat × Ssz.Bytes)} {reason : Ssz.Err}
    (failure : stableFoldLevel depth nodes = .error reason) :
    Ssz.foldLevel depth nodes = .error reason := by
  have related := stableFoldLevelNodes_relation depth nodes nodes
  change stableFoldLevelNodes depth nodes nodes = .error reason at failure
  rw [failure] at related
  cases folded : Ssz.foldLevelNodes depth nodes nodes with
  | error other =>
      have same : reason = other := by simpa [folded, StableLevelRelation] using related
      simp [Ssz.foldLevel, folded, same, Bind.bind, Except.bind]
  | ok groups => simp [folded, StableLevelRelation] at related

end SszNative.Proof
