import SszProofMultiPureTree

namespace SszNative.Proof

/-- Unique keys make first-match lookup independent of the enumeration order. -/
theorem nodeAt_perm {left right : List (Nat × Ssz.Bytes)}
    (perm : left.Perm right) (unique : (left.map Prod.fst).Nodup) (i : Nat) :
    Ssz.nodeAt left i = Ssz.nodeAt right i := by
  cases found : Ssz.nodeAt right i with
  | some value =>
    exact Pure.nodeAt_of_unique unique (perm.mem_iff.mpr (Pure.nodeAt_member found))
  | none =>
    cases original : Ssz.nodeAt left i with
    | none => rfl
    | some value =>
      obtain ⟨value', located⟩ := Pure.nodeAt_exists
        (perm.mem_iff.mp (Pure.nodeAt_member original))
      rw [found] at located
      contradiction

/-- Lookup existence depends only on the supplied keys, including malformed frontiers. -/
theorem nodeAt_present_iff {nodes : List (Nat × Ssz.Bytes)} {i : Nat} :
    (∃ value, Ssz.nodeAt nodes i = some value) ↔ i ∈ nodes.map Prod.fst := by
  constructor
  · rintro ⟨value, found⟩
    exact List.mem_map.mpr ⟨(i, value), Pure.nodeAt_member found, rfl⟩
  · intro member
    obtain ⟨⟨key, value⟩, member, same⟩ := List.mem_map.mp member
    dsimp at same
    subst key
    exact Pure.nodeAt_exists member

/-- Sibling coverage is a property of the set of keys, not their order or values. -/
theorem siblingsPresent_iff_keys {left right : List (Nat × Ssz.Bytes)}
    (keys : ∀ i, i ∈ left.map Prod.fst ↔ i ∈ right.map Prod.fst) (depth : Nat) :
    Pure.SiblingsPresent depth left left ↔ Pure.SiblingsPresent depth right right := by
  have transfer : ∀ {a b : List (Nat × Ssz.Bytes)},
      (∀ i, i ∈ a.map Prod.fst → i ∈ b.map Prod.fst) →
      (∀ i, i ∈ b.map Prod.fst → i ∈ a.map Prod.fst) →
      Pure.SiblingsPresent depth a a → Pure.SiblingsPresent depth b b := by
    intro a b forward backward covered i value member level
    have named := backward i (List.mem_map.mpr ⟨(i, value), member, rfl⟩)
    obtain ⟨⟨key, stored⟩, original, same⟩ := List.mem_map.mp named
    dsimp at same
    subst key
    obtain ⟨sibling, siblingMember⟩ := covered i stored original level
    have siblingNamed := forward (Ssz.gindexSibling i)
      (List.mem_map.mpr ⟨_, siblingMember, rfl⟩)
    obtain ⟨⟨key, stored⟩, siblingMember, same⟩ := List.mem_map.mp siblingNamed
    dsimp at same
    subst key
    exact ⟨stored, siblingMember⟩
  exact ⟨transfer (fun i => (keys i).mp) (fun i => (keys i).mpr),
    transfer (fun i => (keys i).mpr) (fun i => (keys i).mp)⟩

/-- Successful level folding preserves equality of key sets. -/
theorem foldLevel_keys {left right left' right' : List (Nat × Ssz.Bytes)} {depth : Nat}
    (keys : ∀ i, i ∈ left.map Prod.fst ↔ i ∈ right.map Prod.fst)
    (l : Ssz.foldLevel depth left = .ok left')
    (r : Ssz.foldLevel depth right = .ok right') :
    ∀ i, i ∈ left'.map Prod.fst ↔ i ∈ right'.map Prod.fst := by
  intro i
  rw [Pure.foldLevel_indices l, Pure.foldLevel_indices r]
  constructor
  · rintro ⟨child, member, folded⟩
    exact ⟨child, (keys child).mp member, folded⟩
  · rintro ⟨child, member, folded⟩
    exact ⟨child, (keys child).mpr member, folded⟩

/-- Every failure of the worker is the pinned incomplete-proof error. -/
theorem foldLevelNodes_error {depth : Nat} {nodes pending : List (Nat × Ssz.Bytes)}
    {fault : Ssz.Err} (failed : Ssz.foldLevelNodes depth nodes pending = .error fault) :
    fault = .proofIncomplete := by
  induction pending with
  | nil => simp [Ssz.foldLevelNodes] at failed
  | cons pair rest ih =>
    rcases pair with ⟨index, value⟩
    simp only [Ssz.foldLevelNodes] at failed
    split at failed
    · cases rec : Ssz.foldLevelNodes depth nodes rest with
      | error error =>
        simp [rec, Bind.bind, Except.bind] at failed
        subst fault
        exact ih rec
      | ok groups =>
        cases groups
        simp [rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at failed
    · split at failed
      · cases sibling : Ssz.nodeAt nodes (index + 1) with
        | none =>
            simp only [sibling] at failed
            dsimp only [throw, throwThe, MonadExceptOf.throw] at failed
            exact (Except.error.inj failed).symm
        | some siblingValue =>
          cases rec : Ssz.foldLevelNodes depth nodes rest with
          | error error =>
            simp [sibling, rec, Bind.bind, Except.bind] at failed
            subst fault
            exact ih rec
          | ok groups =>
            cases groups
            simp [sibling, rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at failed
      · split at failed
        · exact Except.error.inj failed.symm
        · exact ih failed

/-- The public level worker introduces no additional error constructors. -/
theorem foldLevel_error {depth : Nat} {nodes : List (Nat × Ssz.Bytes)}
    {fault : Ssz.Err} (failed : Ssz.foldLevel depth nodes = .error fault) :
    fault = .proofIncomplete := by
  unfold Ssz.foldLevel at failed
  cases rec : Ssz.foldLevelNodes depth nodes nodes with
  | error error =>
    simp [rec, Bind.bind, Except.bind] at failed
    subst fault
    exact foldLevelNodes_error rec
  | ok groups =>
    cases groups
    simp [rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at failed

/-- Root reconstruction also has exactly one possible error constructor. -/
theorem foldToRoot_error {depth : Nat} {nodes : List (Nat × Ssz.Bytes)}
    {fault : Ssz.Err} (failed : Ssz.foldToRoot depth nodes = .error fault) :
    fault = .proofIncomplete := by
  induction depth generalizing nodes with
  | zero =>
    simp only [Ssz.foldToRoot] at failed
    cases found : Ssz.nodeAt nodes 1 with
    | none => simpa [found] using failed.symm
    | some value => simp [found] at failed
  | succ depth ih =>
    simp only [Ssz.foldToRoot] at failed
    cases folded : Ssz.foldLevel (depth + 1) nodes with
    | error error =>
      simp [folded, Bind.bind, Except.bind] at failed
      subst fault
      exact foldLevel_error folded
    | ok result =>
      exact ih (by simpa [folded, Bind.bind, Except.bind] using failed)

/-- Success, and therefore failure, is determined by the set of supplied positions. -/
theorem foldToRoot_success_iff_keys {left right : List (Nat × Ssz.Bytes)}
    (keys : ∀ i, i ∈ left.map Prod.fst ↔ i ∈ right.map Prod.fst) (depth : Nat) :
    (∃ root, Ssz.foldToRoot depth left = .ok root) ↔
      (∃ root, Ssz.foldToRoot depth right = .ok root) := by
  induction depth generalizing left right with
  | zero =>
    have present := (nodeAt_present_iff (nodes := left) (i := 1)).trans
      ((keys 1).trans (nodeAt_present_iff (nodes := right) (i := 1)).symm)
    cases l : Ssz.nodeAt left 1 <;> cases r : Ssz.nodeAt right 1 <;>
      simp_all [Ssz.foldToRoot]
  | succ depth ih =>
    have step : (∃ result, Ssz.foldLevel (depth + 1) left = .ok result) ↔
        (∃ result, Ssz.foldLevel (depth + 1) right = .ok result) :=
      Pure.foldLevel_success_iff.trans
        ((siblingsPresent_iff_keys keys (depth + 1)).trans Pure.foldLevel_success_iff.symm)
    cases l : Ssz.foldLevel (depth + 1) left with
    | error error =>
      cases r : Ssz.foldLevel (depth + 1) right with
      | error error' => simp [Ssz.foldToRoot, l, r, Bind.bind, Except.bind]
      | ok result => simp [l, r] at step
    | ok result =>
      cases r : Ssz.foldLevel (depth + 1) right with
      | error error => simp [l, r] at step
      | ok result' =>
        simpa [Ssz.foldToRoot, l, r, Bind.bind, Except.bind] using
          ih (foldLevel_keys keys l r)

/-- The explicit reconstruction tree is invariant under unique-key permutations. -/
theorem proofTree_perm {left right : List (Nat × Ssz.Bytes)}
    (perm : left.Perm right) (unique : (left.map Prod.fst).Nodup) (height index : Nat) :
    Pure.proofTree left height index = Pure.proofTree right height index := by
  induction height generalizing index with
  | zero => simp only [Pure.proofTree, nodeAt_perm perm unique]
  | succ height ih =>
    simp only [Pure.proofTree, nodeAt_perm perm unique]
    cases Ssz.nodeAt right index with
    | some value => rfl
    | none => rw [ih, ih]

/-- Multiproof folding is order independent, including all incomplete-proof failures.
No depth bound, successful-reconstruction premise, or hash injectivity is required. -/
theorem foldToRoot_perm {left right : List (Nat × Ssz.Bytes)}
    (perm : left.Perm right) (unique : (left.map Prod.fst).Nodup)
    (antichain : Pure.ProofAntichain left) (depth : Nat) :
    Ssz.foldToRoot depth left = Ssz.foldToRoot depth right := by
  have keys : ∀ i, i ∈ left.map Prod.fst ↔ i ∈ right.map Prod.fst :=
    fun _ => (perm.map Prod.fst).mem_iff
  have rightUnique := (perm.map Prod.fst).nodup unique
  have rightAntichain : Pure.ProofAntichain right := by
    intro i member j member' step shifted
    exact antichain i ((keys i).mpr member) j ((keys j).mpr member') step shifted
  have success := foldToRoot_success_iff_keys keys depth
  cases l : Ssz.foldToRoot depth left with
  | error error =>
    cases r : Ssz.foldToRoot depth right with
    | error error' => rw [foldToRoot_error l, foldToRoot_error r]
    | ok root => simp [l, r] at success
  | ok root =>
    cases r : Ssz.foldToRoot depth right with
    | error error => simp [l, r] at success
    | ok root' =>
      have leftTree := Pure.foldToRoot_eq_proofTree antichain unique l
      have rightTree := Pure.foldToRoot_eq_proofTree rightAntichain rightUnique r
      rw [leftTree, rightTree, proofTree_perm perm unique]

end SszNative.Proof
