import Ssz.Merkle.Verify
import Ssz.Proofs.Merkle.Gindex

namespace SszNative.Proof.Pure

open Ssz

/-- Agreement of every stored node with a fixed reading of the tree. -/
def NodesAgree (tree : Nat → Bytes) (nodes : List (Nat × Bytes)) : Prop :=
  ∀ index value, (index, value) ∈ nodes → value = tree index

theorem nodeAt_exists {nodes : List (Nat × Bytes)} {index : Nat} {value : Bytes}
    (member : (index, value) ∈ nodes) : ∃ found, nodeAt nodes index = some found := by
  induction nodes with
  | nil => simp at member
  | cons pair rest ih =>
    rcases pair with ⟨at_, stored⟩
    by_cases same : at_ = index
    · subst at_
      exact ⟨stored, by simp [nodeAt]⟩
    · have tail : (index, value) ∈ rest := by simpa [same, Ne.symm same] using member
      obtain ⟨found, located⟩ := ih tail
      exact ⟨found, by simpa [nodeAt, same] using located⟩

theorem nodeAt_member {nodes : List (Nat × Bytes)} {index : Nat} {value : Bytes}
    (found : nodeAt nodes index = some value) : (index, value) ∈ nodes := by
  unfold nodeAt at found
  cases located : nodes.find? (fun pair => pair.1 == index) with
  | none => simp [located] at found
  | some pair =>
    have member := List.mem_of_find?_eq_some located
    have named := List.find?_some located
    simp only [beq_iff_eq] at named
    simp only [located, Option.map_some, Option.some.injEq] at found
    rw [← found, ← named]
    exact member

theorem nodeAt_agrees {tree : Nat → Bytes} {nodes : List (Nat × Bytes)}
    (agree : NodesAgree tree nodes) {index : Nat} {value : Bytes}
    (found : nodeAt nodes index = some value) : value = tree index :=
  agree index value (nodeAt_member found)

theorem nodeAt_of_unique {nodes : List (Nat × Bytes)}
    (unique : (nodes.map Prod.fst).Nodup) {index : Nat} {value : Bytes}
    (member : (index, value) ∈ nodes) : nodeAt nodes index = some value := by
  induction nodes with
  | nil => simp at member
  | cons pair rest ih =>
    rcases pair with ⟨key, node⟩
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with equal | later
    · cases equal
      simp [nodeAt]
    · have unequal : key ≠ index := by
        intro equal
        exact unique.1 (equal ▸ List.mem_map.mpr ⟨(index, value), later, rfl⟩)
      simpa [nodeAt, unequal] using ih unique.2 later

/-- All positions consumed at the active depth have a sibling in the original list. -/
def SiblingsPresent (depth : Nat) (nodes pending : List (Nat × Bytes)) : Prop :=
  ∀ index value, (index, value) ∈ pending → levelOf index = depth →
    ∃ sibling, (gindexSibling index, sibling) ∈ nodes

theorem foldLevelNodes_complete {depth : Nat} {nodes pending : List (Nat × Bytes)}
    (covered : SiblingsPresent depth nodes pending) :
    ∃ parents kept, foldLevelNodes depth nodes pending = .ok (parents, kept) := by
  induction pending with
  | nil => exact ⟨[], [], rfl⟩
  | cons pair rest ih =>
    rcases pair with ⟨index, value⟩
    have tail : SiblingsPresent depth nodes rest :=
      fun i v member level => covered i v (by simp [member]) level
    obtain ⟨ps, ks, rec⟩ := ih tail
    by_cases atDepth : levelOf index = depth
    · obtain ⟨sibling, member⟩ := covered index value (by simp) atDepth
      obtain ⟨found, located⟩ := nodeAt_exists member
      rcases Nat.mod_two_eq_zero_or_one index with even | odd
      · obtain ⟨whole, siblingIndex⟩ := gindexSibling_even even
        have siblingIndex : gindexSibling index = index + 1 := by omega
        rw [siblingIndex] at located
        exact ⟨(gindexParent index, combine value found) :: ps, ks,
          by simp [foldLevelNodes, atDepth, even, located, rec,
            Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
      · obtain ⟨whole, siblingIndex⟩ := gindexSibling_odd odd
        have siblingIndex : gindexSibling index = index - 1 := by omega
        rw [siblingIndex] at located
        exact ⟨ps, ks, by simp [foldLevelNodes, atDepth, odd, located, rec]⟩
    · exact ⟨ps, (index, value) :: ks,
        by simp [foldLevelNodes, atDepth, rec, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

theorem foldLevel_complete {depth : Nat} {nodes : List (Nat × Bytes)}
    (covered : SiblingsPresent depth nodes nodes) :
    ∃ result, foldLevel depth nodes = .ok result := by
  obtain ⟨parents, kept, built⟩ := foldLevelNodes_complete covered
  exact ⟨parents ++ kept,
    by simp [foldLevel, built, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

theorem foldLevelNodes_siblings {depth : Nat} {nodes pending : List (Nat × Bytes)}
    {parents kept : List (Nat × Bytes)}
    (built : foldLevelNodes depth nodes pending = .ok (parents, kept)) :
    SiblingsPresent depth nodes pending := by
  induction pending generalizing parents kept with
  | nil => simp [SiblingsPresent]
  | cons pair rest ih =>
    rcases pair with ⟨index, value⟩
    by_cases atDepth : levelOf index = depth
    · rcases Nat.mod_two_eq_zero_or_one index with even | odd
      · cases sibling : nodeAt nodes (index + 1) with
        | none => simp [foldLevelNodes, atDepth, even, sibling, throw] at built
        | some found =>
          cases rec : foldLevelNodes depth nodes rest with
          | error error =>
            simp [foldLevelNodes, atDepth, even, sibling, rec, Bind.bind, Except.bind] at built
          | ok result =>
            rcases result with ⟨ps, ks⟩
            have tail := ih rec
            intro i v member level
            rcases List.mem_cons.mp member with same | member
            · cases same
              obtain ⟨whole, side⟩ := gindexSibling_even even
              have side : gindexSibling index = index + 1 := by omega
              exact ⟨found, by rw [side]; exact nodeAt_member sibling⟩
            · exact tail i v member level
      · cases sibling : nodeAt nodes (index - 1) with
        | none => simp [foldLevelNodes, atDepth, odd, sibling, throw] at built
        | some found =>
          have rebuilt : foldLevelNodes depth nodes rest = .ok (parents, kept) := by
            simpa [foldLevelNodes, atDepth, odd, sibling] using built
          have tail := ih rebuilt
          intro i v member level
          rcases List.mem_cons.mp member with same | member
          · cases same
            obtain ⟨whole, side⟩ := gindexSibling_odd odd
            have side : gindexSibling index = index - 1 := by omega
            exact ⟨found, by rw [side]; exact nodeAt_member sibling⟩
          · exact tail i v member level
    · cases rec : foldLevelNodes depth nodes rest with
      | error error =>
        simp [foldLevelNodes, atDepth, rec, Bind.bind, Except.bind] at built
      | ok result =>
        rcases result with ⟨ps, ks⟩
        have tail := ih rec
        intro i v member level
        rcases List.mem_cons.mp member with same | member
        · cases same; exact False.elim (atDepth level)
        · exact tail i v member level

theorem foldLevel_success_iff {depth : Nat} {nodes : List (Nat × Bytes)} :
    (∃ result, foldLevel depth nodes = .ok result) ↔ SiblingsPresent depth nodes nodes := by
  constructor
  · rintro ⟨result, built⟩
    unfold foldLevel at built
    cases rec : foldLevelNodes depth nodes nodes with
    | error error => simp [rec, Bind.bind, Except.bind] at built
    | ok groups =>
      rcases groups with ⟨parents, kept⟩
      exact foldLevelNodes_siblings rec
  · exact foldLevel_complete

/-- Retained nodes keep their key; even nodes at the active depth produce their parent. -/
def FoldedIndex (depth child index : Nat) : Prop :=
  (levelOf child ≠ depth ∧ index = child) ∨
    (levelOf child = depth ∧ child % 2 = 0 ∧ index = gindexParent child)

theorem foldLevelNodes_indices {depth : Nat} {nodes pending : List (Nat × Bytes)}
    {parents kept : List (Nat × Bytes)}
    (built : foldLevelNodes depth nodes pending = .ok (parents, kept)) :
    ∀ index, index ∈ (parents ++ kept).map Prod.fst ↔
      ∃ child ∈ pending.map Prod.fst, FoldedIndex depth child index := by
  induction pending generalizing parents kept with
  | nil =>
    simp [foldLevelNodes] at built
    rcases built with ⟨rfl, rfl⟩
    simp
  | cons pair rest ih =>
    rcases pair with ⟨child, value⟩
    by_cases atDepth : levelOf child = depth
    · rcases Nat.mod_two_eq_zero_or_one child with even | odd
      · cases sibling : nodeAt nodes (child + 1) with
        | none => simp [foldLevelNodes, atDepth, even, sibling, throw] at built
        | some found =>
          cases rec : foldLevelNodes depth nodes rest with
          | error error =>
            simp [foldLevelNodes, atDepth, even, sibling, rec, Bind.bind, Except.bind] at built
          | ok result =>
            rcases result with ⟨ps, ks⟩
            simp [foldLevelNodes, atDepth, even, sibling, rec, Bind.bind, Except.bind,
              Pure.pure, Except.pure] at built
            rcases built with ⟨rfl, rfl⟩
            intro index
            simpa [FoldedIndex, atDepth, even, List.map_append, List.mem_append] using
              or_congr (Iff.rfl : (index = gindexParent child) ↔ _) (ih rec index)
      · cases sibling : nodeAt nodes (child - 1) with
        | none => simp [foldLevelNodes, atDepth, odd, sibling, throw] at built
        | some found =>
          have rebuilt : foldLevelNodes depth nodes rest = .ok (parents, kept) := by
            simpa [foldLevelNodes, atDepth, odd, sibling] using built
          intro index
          simpa [FoldedIndex, atDepth, odd] using ih rebuilt index
    · cases rec : foldLevelNodes depth nodes rest with
      | error error => simp [foldLevelNodes, atDepth, rec, Bind.bind, Except.bind] at built
      | ok result =>
        rcases result with ⟨ps, ks⟩
        simp [foldLevelNodes, atDepth, rec, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at built
        rcases built with ⟨rfl, rfl⟩
        intro index
        simpa [FoldedIndex, atDepth, List.map_append, List.mem_append,
          or_comm, or_left_comm, or_assoc] using
          or_congr (Iff.rfl : (index = child) ↔ _) (ih rec index)

theorem foldLevel_indices {depth : Nat} {nodes result : List (Nat × Bytes)}
    (built : foldLevel depth nodes = .ok result) :
    ∀ index, index ∈ result.map Prod.fst ↔
      ∃ child ∈ nodes.map Prod.fst, FoldedIndex depth child index := by
  unfold foldLevel at built
  cases rec : foldLevelNodes depth nodes nodes with
  | error error => simp [rec, Bind.bind, Except.bind] at built
  | ok groups =>
    rcases groups with ⟨parents, kept⟩
    simp [rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
    subst result
    exact foldLevelNodes_indices rec

theorem two_le_of_level_positive {index depth : Nat}
    (level : levelOf index = depth) (positive : 0 < depth) : 2 ≤ index := by
  by_cases large : 2 ≤ index
  · exact large
  · have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with zero | one
    · subst index; change 0 = depth at level; omega
    · subst index; change 0 = depth at level; omega

theorem levelOf_parent {index : Nat} (below : 2 ≤ index) :
    levelOf index = levelOf (index / 2) + 1 := by
  change index.log2 = (index / 2).log2 + 1
  exact (Nat.log2_def index).trans (by simp only [below, ↓reduceIte])

theorem levelOf_sibling {index : Nat} (below : 2 ≤ index) :
    levelOf (gindexSibling index) = levelOf index := by
  have half := gindexSibling_half index
  have other : 2 ≤ gindexSibling index := by omega
  rw [levelOf_parent other, half, ← levelOf_parent below]

end SszNative.Proof.Pure
