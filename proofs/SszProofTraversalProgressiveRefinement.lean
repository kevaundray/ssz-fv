import SszProofTraversal
import SszProofTraversalRangeRefinement

set_option autoImplicit false

namespace SszNative.Proof

/-- Collection preserves the exact range length on success, without requiring
that any future indexed read succeeds. -/
theorem rangeCollect_length (leaf : Nat → Except Ssz.Err Ssz.Bytes)
    (remaining start : Nat) (nodes : List Ssz.Bytes)
    (success : HashLayout.collect leaf remaining start = .ok nodes) :
    nodes.length = remaining := by
  induction remaining generalizing start nodes with
  | zero =>
      have equal : [] = nodes := Except.ok.inj success
      subst nodes
      rfl
  | succ remaining ih =>
      cases first : leaf start with
      | error reason => simp [HashLayout.collect, first] at success
      | ok node =>
          cases rest : HashLayout.collect leaf remaining (start + 1) with
          | error reason => simp [HashLayout.collect, first, rest] at success
          | ok tail =>
              have equal : node :: tail = nodes := by
                simpa [HashLayout.collect, first, rest] using success
              subst nodes
              simpa only [List.length_cons] using congrArg Nat.succ (ih (start + 1) tail rest)

/-- Splitting ordered reads preserves the first error as well as the leaf order. -/
theorem rangeCollect_split (leaf : Nat → Except Ssz.Err Ssz.Bytes)
    (first second start : Nat) :
    HashLayout.collect leaf (first + second) start =
      (HashLayout.collect leaf first start >>= fun left =>
        HashLayout.collect leaf second (start + first) >>= fun right => .ok (left ++ right)) := by
  induction first generalizing start with
  | zero =>
      rw [Nat.zero_add]
      change HashLayout.collect leaf second start =
        (HashLayout.collect leaf second start >>= fun right => .ok right)
      cases HashLayout.collect leaf second start <;> rfl
  | succ first ih =>
      rw [Nat.succ_add]
      simp only [HashLayout.collect, ih]
      have shifted : start + 1 + first = start + (first + 1) := by omega
      rw [shifted]
      cases leaf start with
      | error reason => rfl
      | ok node =>
          cases HashLayout.collect leaf first (start + 1) with
          | error reason => rfl
          | ok initial =>
              cases HashLayout.collect leaf second (start + (first + 1)) <;> rfl

private theorem layoutChunksAt_after (budget : Nat) (view : Ssz.MerkleLayout)
    (start : Nat) (outside : view.leaves.count ≤ start) :
    Ssz.layoutChunksAt budget view start = .ok #[] := by
  cases view with
  | mk leaves limit mixin =>
      cases leaves with
      | packed chunks =>
          have empty : chunks.extract start chunks.size = #[] := by
            apply Array.ext
            · simp only [Array.size_extract, Array.size_empty]
              change chunks.size ≤ start at outside
              omega
            · intro index left right
              simp at right
          simpa only [Ssz.layoutChunksAt, Option.getD_none, Ssz.Leaves.count,
            Pure.pure, Except.pure] using congrArg (Except.ok (ε := Ssz.Err)) empty
      | nested values =>
          have bound : values.length ≤ start := outside
          simp [Ssz.layoutChunksAt, List.drop_eq_nil_of_le bound]

/-- The suffix collector matches the pinned range reader even beyond the last
physical position, where both return an empty sequence without visiting a child. -/
theorem collect_layout_suffix (budget : Nat) (view : Ssz.MerkleLayout) (start : Nat) :
    (HashLayout.collect (HashLayout.specLeaf budget view) (view.leaves.count - start) start).map
      List.toArray = Ssz.layoutChunksAt budget view start := by
  by_cases inside : start ≤ view.leaves.count
  · have collected := collect_layout_range budget view start view.leaves.count inside (Nat.le_refl _)
    simpa only [Ssz.layoutChunksAt, Option.getD_some, Option.getD_none] using collected
  · have outside : view.leaves.count ≤ start := by omega
    rw [Nat.sub_eq_zero_of_le outside, HashLayout.collect, layoutChunksAt_after budget view start outside]
    rfl

private theorem power4 (level : Nat) : 4 ^ level = 2 ^ (2 * level) := by
  rw [Nat.pow_mul]

private theorem capacity_depth (level : Nat) : 2 ^ (4 ^ level).log2 = 4 ^ level := by
  rw [power4, Nat.log2_two_pow]

private theorem progressiveFrom_power (chunks : Array Ssz.Bytes) (level : Nat) :
    Ssz.merkleizeProgressiveFrom chunks (4 ^ level) = Ssz.merkleizeProgressive chunks.toList level := by
  simp [Ssz.merkleizeProgressiveFrom, power4, Nat.log2_two_pow]

/-- Physical conversion changes no active prefix length, even when the logical
capacity itself cannot be converted to a native slice position. -/
theorem progressiveTake_eq_min (remaining capacity : Nat) (physical : remaining < 2 ^ 64) :
    progressiveTake remaining capacity = min capacity remaining := by
  by_cases bounded : capacity < 2 ^ 64
  · simp only [progressiveTake, physicalIndex, bounded, ↓reduceIte]
  · have bound : remaining ≤ capacity := by omega
    simp only [progressiveTake, physicalIndex, bounded, ↓reduceIte,
      Nat.min_self, Nat.min_eq_right bound]

/-- Specification-only observation of one bounded progressive level. -/
def progressiveBlockSpec (leaf : Nat → Except Ssz.Err Ssz.Bytes)
    (remaining start level : Nat) : Except Ssz.Err Ssz.Bytes :=
  HashLayout.collect leaf remaining start >>= fun nodes =>
    Ssz.merkleizeBounded nodes.toArray (some (2 ^ (4 ^ level).log2))

/-- Specification-only observation of the ordered remaining leaves. -/
def progressiveSuffixSpec (leaf : Nat → Except Ssz.Err Ssz.Bytes)
    (remaining start level : Nat) : Except Ssz.Err Ssz.Bytes :=
  HashLayout.collect leaf remaining start >>= fun nodes =>
    .ok (Ssz.merkleizeProgressive nodes level)

private theorem progressiveSuffixSpec_zero (leaf : Nat → Except Ssz.Err Ssz.Bytes)
    (start level : Nat) :
    progressiveSuffixSpec leaf 0 start level = .ok Ssz.zeroChunk := by
  unfold progressiveSuffixSpec
  change Except.ok (Ssz.merkleizeProgressive [] level) = Except.ok Ssz.zeroChunk
  rw [Ssz.merkleizeProgressive]
  rfl

private theorem progressiveFrom_capacity_eq (view : HashLayout.Layout) (start a b : Nat)
    (positiveA : 0 < a) (positiveB : 0 < b) (arena : Delimited.ArenaState)
    (same : a = b) :
    progressiveFrom view start a positiveA arena =
      progressiveFrom view start b positiveB arena := by
  cases same
  rfl

private theorem progressive_partition (left right : List Ssz.Bytes) (remaining level : Nat)
    (nonempty : 0 < remaining)
    (leftLength : left.length = min (4 ^ level) remaining)
    (rightLength : right.length = remaining - min (4 ^ level) remaining) :
    Ssz.merkleizeProgressive (left ++ right) level =
      Ssz.combine (Ssz.subtreeAt left.toArray (Ssz.depthFor (4 ^ level)) 0)
        (Ssz.merkleizeProgressive right (level + 1)) := by
  have total : (left ++ right).length = remaining := by
    simp only [List.length_append, leftLength, rightLength]
    omega
  have occupied : (left ++ right).isEmpty = false := by
    cases all : left ++ right with
    | nil => simp only [all, List.length_nil] at total; omega
    | cons head tail => rfl
  have takeEq : (left ++ right).take (4 ^ level) = left := by
    by_cases full : 4 ^ level ≤ remaining
    · have length : left.length = 4 ^ level := leftLength.trans (Nat.min_eq_left full)
      rw [← length, List.take_left]
    · have empty : right = [] := by
        apply List.length_eq_zero_iff.mp
        rw [rightLength, Nat.min_eq_right (by omega), Nat.sub_self]
      rw [empty, List.append_nil]
      apply List.take_of_length_le
      rw [leftLength]
      exact Nat.min_le_left _ _
  have dropEq : (left ++ right).drop (4 ^ level) = right := by
    by_cases full : 4 ^ level ≤ remaining
    · have length : left.length = 4 ^ level := leftLength.trans (Nat.min_eq_left full)
      rw [← length, List.drop_left]
    · have empty : right = [] := by
        apply List.length_eq_zero_iff.mp
        rw [rightLength, Nat.min_eq_right (by omega), Nat.sub_self]
      rw [empty, List.append_nil]
      apply List.drop_eq_nil_of_le
      rw [leftLength]
      exact Nat.min_le_left _ _
  rw [Ssz.merkleizeProgressive]
  simp only [occupied, Bool.false_eq_true, ↓reduceIte, takeEq, dropEq]

/-- This law moves a bounded finish before later child reads only after proving
that finish cannot fail: the successfully collected prefix fits its capacity. -/
theorem progressiveSuffixSpec_step (leaf : Nat → Except Ssz.Err Ssz.Bytes)
    (remaining start level : Nat) (nonempty : 0 < remaining) :
    progressiveSuffixSpec leaf remaining start level =
      (progressiveBlockSpec leaf (min (4 ^ level) remaining) start level >>= fun left =>
        progressiveSuffixSpec leaf (remaining - min (4 ^ level) remaining)
          (start + min (4 ^ level) remaining) (level + 1) >>= fun right =>
            .ok (Ssz.combine left right)) := by
  let take := min (4 ^ level) remaining
  have sum : take + (remaining - take) = remaining := by
    dsimp only [take]
    omega
  have split := rangeCollect_split leaf take (remaining - take) start
  rw [sum] at split
  unfold progressiveSuffixSpec progressiveBlockSpec
  rw [split]
  cases first : HashLayout.collect leaf take start with
  | error reason => rfl
  | ok left =>
      have length := rangeCollect_length leaf take start left first
      have fits : left.toArray.size ≤ 4 ^ level := by
        simp only [List.size_toArray, length, take]
        exact Nat.min_le_left _ _
      have rooted : Ssz.merkleizeBounded left.toArray (some (2 ^ (4 ^ level).log2)) =
          .ok (Ssz.subtreeAt left.toArray (Ssz.depthFor (4 ^ level)) 0) := by
        rw [capacity_depth]
        simp only [Ssz.merkleizeBounded, Nat.not_lt.mpr fits, ↓reduceIte]
        rfl
      cases second : HashLayout.collect leaf (remaining - take) (start + take) with
      | error reason => simp only [Bind.bind, Except.bind, rooted]
      | ok right =>
          have rightLength := rangeCollect_length leaf (remaining - take) (start + take) right second
          have treeEq := progressive_partition left right remaining level nonempty length rightLength
          simpa only [Bind.bind, Except.bind, rooted] using congrArg (Except.ok (ε := Ssz.Err)) treeEq

private theorem progressiveFrom_refines_collect (desc : Codec.Desc) (value : Codec.Value)
    (layoutArena : Delimited.ArenaState) (view : HashLayout.Layout)
    (expected : Ssz.MerkleLayout) (budget : Nat)
    (safe : HashLayout.SafeWidths desc) (descPhysical : desc.Physical)
    (valuePhysical : value.Physical)
    (laidOut : (HashLayout.layout desc value layoutArena).result = .ok view)
    (layoutEq : Ssz.merkleLayout desc.erase value.erase = .ok expected)
    (related : HashLayout.LayoutRefines view expected) (enough : desc.nesting ≤ budget + 1)
    (remaining start level : Nat) (arena : Delimited.ArenaState)
    (counted : remaining = view.count - start) :
    Refines Eq (progressiveFrom view start (4 ^ level) (Nat.pow_pos (by decide)) arena)
      (progressiveSuffixSpec (HashLayout.specLeaf budget expected) remaining start level) := by
  have countEq := HashLayout.LayoutRefines.count view expected related
  have countBound := HashLayout.layout_count_physical desc value layoutArena view
    descPhysical valuePhysical laidOut
  induction remaining using Nat.strongRecOn generalizing start level arena with
  | ind remaining ih =>
      by_cases nonempty : start < view.count
      · have positive : 0 < remaining := by omega
        let take := min (4 ^ level) remaining
        have takePositive : 0 < take := Nat.lt_min.mpr ⟨Nat.pow_pos (by decide), positive⟩
        have takeBound : take ≤ remaining := Nat.min_le_right _ _
        have stopBound : start + take ≤ view.count := by omega
        have takeEq : progressiveTake (view.count - start) (4 ^ level) = take := by
          rw [progressiveTake_eq_min _ _ (by omega), ← counted]
        have block := rangeRoot_refines_layout desc value layoutArena arena view expected start
          (start + take) (4 ^ level).log2 budget safe descPhysical valuePhysical laidOut layoutEq
          enough (by omega) stopBound
        have collected := collect_layout_range budget expected start (start + take) (by omega) (by omega)
        have blockEq :
            (Ssz.layoutChunksAt budget expected start (some (start + take)) >>= fun chunks =>
              Ssz.merkleizeBounded chunks (some (2 ^ (4 ^ level).log2))) =
            progressiveBlockSpec (HashLayout.specLeaf budget expected) take start level := by
          rw [← collected]
          simp only [Nat.add_sub_cancel_left]
          unfold progressiveBlockSpec
          cases HashLayout.collect (HashLayout.specLeaf budget expected) take start <;> rfl
        rw [blockEq] at block
        rw [progressiveFrom]
        simp only [nonempty, ↓reduceDIte, takeEq]
        rw [progressiveSuffixSpec_step _ remaining start level positive]
        change Refines Eq
          (bind (rangeRoot view start (start + take) (4 ^ level).log2 arena) _)
          (progressiveBlockSpec (HashLayout.specLeaf budget expected) take start level >>= fun left =>
            progressiveSuffixSpec (HashLayout.specLeaf budget expected) (remaining - take)
              (start + take) (level + 1) >>= fun right => .ok (Ssz.combine left right))
        apply ResultRefines.bind Eq Eq _ _ _ _ block
        intro left expectedLeft same used
        subst expectedLeft
        by_cases terminal : start + take = view.count
        · simp only [terminal, ↓reduceIte]
          have empty : remaining - take = 0 := by omega
          simp only [empty, progressiveSuffixSpec_zero, Bind.bind, Except.bind]
          exact .ok _ _ (rawCombine_eq left Ssz.zeroChunk)
        · simp only [terminal, ↓reduceIte]
          have later := ih (remaining - take) (by omega) (start + take) (level + 1)
            { arena with used := used } (by omega)
          have capacityEq := progressiveFrom_capacity_eq view (start + take)
            (4 ^ (level + 1)) (4 ^ level * 4) (Nat.pow_pos (by decide))
            (Nat.mul_pos (Nat.pow_pos (by decide)) (by decide))
            { arena with used := used } (Nat.pow_succ 4 level)
          rw [capacityEq] at later
          apply ResultRefines.bind Eq Eq _ _ _ _ later
          intro right expectedRight same used'
          subst expectedRight
          exact .ok _ _ (rawCombine_eq left right)
      · have empty : remaining = 0 := by omega
        subst remaining
        rw [progressiveFrom]
        simp only [nonempty, ↓reduceDIte]
        rw [empty, progressiveSuffixSpec_zero]
        exact .ok _ _ rfl

/-- Complete arbitrary-level progressive suffix refinement. Only the existing
SafeWidths/physical domain and provenance of the completed layout are required;
recursive child errors and actual scratch exhaustion remain observable. -/
theorem progressiveFrom_refines_layout (desc : Codec.Desc) (value : Codec.Value)
    (layoutArena arena : Delimited.ArenaState) (view : HashLayout.Layout)
    (expected : Ssz.MerkleLayout) (start level budget : Nat)
    (safe : HashLayout.SafeWidths desc) (descPhysical : desc.Physical)
    (valuePhysical : value.Physical)
    (laidOut : (HashLayout.layout desc value layoutArena).result = .ok view)
    (layoutEq : Ssz.merkleLayout desc.erase value.erase = .ok expected)
    (enough : desc.nesting ≤ budget + 1) :
    Refines Eq (progressiveFrom view start (4 ^ level) (Nat.pow_pos (by decide)) arena)
      (Ssz.layoutChunksAt budget expected start >>= fun chunks =>
        .ok (Ssz.merkleizeProgressiveFrom chunks (4 ^ level))) := by
  obtain ⟨other, otherEq, related⟩ := HashLayout.layout_success desc value layoutArena
    safe descPhysical valuePhysical view laidOut
  rw [layoutEq] at otherEq
  cases Except.ok.inj otherEq
  have refined := progressiveFrom_refines_collect desc value layoutArena view expected budget
    safe descPhysical valuePhysical laidOut layoutEq related enough (view.count - start) start level arena rfl
  have countEq := HashLayout.LayoutRefines.count view expected related
  rw [← collect_layout_suffix budget expected start, ← countEq]
  cases roots : HashLayout.collect (HashLayout.specLeaf budget expected) (view.count - start) start <;>
    simpa only [progressiveSuffixSpec, roots, Except.map, Bind.bind, Except.bind,
      progressiveFrom_power] using refined

theorem progressiveFrom_refines (desc : Codec.Desc) (value : Codec.Value)
    (layoutArena arena : Delimited.ArenaState) (view : HashLayout.Layout)
    (start level budget : Nat)
    (safe : HashLayout.SafeWidths desc) (descPhysical : desc.Physical)
    (valuePhysical : value.Physical)
    (laidOut : (HashLayout.layout desc value layoutArena).result = .ok view)
    (enough : desc.nesting ≤ budget + 1) :
    ∃ expected, Ssz.merkleLayout desc.erase value.erase = .ok expected ∧
      Refines Eq (progressiveFrom view start (4 ^ level) (Nat.pow_pos (by decide)) arena)
        (Ssz.layoutChunksAt budget expected start >>= fun chunks =>
          .ok (Ssz.merkleizeProgressiveFrom chunks (4 ^ level))) := by
  obtain ⟨expected, layoutEq, _⟩ := HashLayout.layout_success desc value layoutArena
    safe descPhysical valuePhysical view laidOut
  exact ⟨expected, layoutEq, progressiveFrom_refines_layout desc value layoutArena arena view expected
    start level budget safe descPhysical valuePhysical laidOut layoutEq enough⟩

end SszNative.Proof
