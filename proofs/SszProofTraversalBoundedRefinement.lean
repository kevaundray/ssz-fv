import SszProofTraversalArithmetic
import SszProofTraversalRangeRefinement
import SszProofRefinement

set_option autoImplicit false

namespace SszNative.Proof

private theorem take_clip {α : Type} (values : List α) (count : Nat) :
    values.take (min count values.length) = values.take count := by
  induction values generalizing count with
  | nil => simp
  | cons first rest ih =>
      cases count with
      | zero => rfl
      | succ count =>
          have clip : min (count + 1) (rest.length + 1) = min count rest.length + 1 := by omega
          simp only [List.length_cons, clip, List.take_succ_cons, ih]

/-- Clipping changes only the requested interval's nonexistent suffix; errors
from actual nested leaves remain in precisely their original order. -/
theorem layoutChunksAt_clip (budget : Nat) (view : Ssz.MerkleLayout) (start stop : Nat) :
    Ssz.layoutChunksAt budget view start (some (min stop view.leaves.count)) =
      Ssz.layoutChunksAt budget view start (some stop) := by
  cases view with
  | mk leaves limit mixin =>
      cases leaves with
      | packed chunks =>
          simp only [Ssz.layoutChunksAt, Ssz.Leaves.count, Option.getD_some]
          congr 1
          apply Array.ext
          · simp only [Array.size_extract]
            omega
          · intro position left right
            simp only [Array.getElem_extract]
      | nested values =>
          have counts : min stop values.length - start = min (stop - start) (values.drop start).length := by
            simp only [List.length_drop]
            omega
          simp only [Ssz.layoutChunksAt, Ssz.Leaves.count, Option.getD_some, counts, take_clip]

theorem layoutChunksAt_outside (budget : Nat) (view : Ssz.MerkleLayout) (start stop : Nat)
    (outside : view.leaves.count ≤ start) :
    Ssz.layoutChunksAt budget view start (some stop) = .ok #[] := by
  cases view with
  | mk leaves limit mixin =>
      cases leaves with
      | packed chunks =>
          have empty : chunks.extract start stop = #[] := by
            apply Array.ext
            · simp only [Array.size_extract, Array.size_empty]
              change chunks.size ≤ start at outside
              omega
            · intro position left right
              simp only [Array.size_empty] at right
              omega
          simp only [Ssz.layoutChunksAt, Option.getD_some, empty]
          rfl
      | nested values =>
          have empty : values.drop start = [] := List.drop_eq_nil_of_le outside
          simp [Ssz.layoutChunksAt, empty]

theorem zeroSubtree_raw (depth : Nat) :
    MerkleAccumulator.zeroSubtree rawCombine Ssz.zeroChunk depth = Ssz.zeroSubtree depth := by
  have combineEq : rawCombine = Ssz.combine := funext fun left => funext fun right => rawCombine_eq left right
  rw [combineEq, MerkleAccumulator.zeroSubtree_refines]

private theorem empty_depth (depth : Nat) :
    Ssz.merkleizeBounded #[] (some (2 ^ depth)) = .ok (Ssz.zeroSubtree depth) := by
  simp only [Ssz.merkleizeBounded, Array.size_empty, Nat.not_lt_zero, ↓reduceIte,
    Ssz.depthFor_pow]
  rw [Ssz.subtreeAt.eq_def]
  rfl

theorem boundedNode_internal_refines (desc : Codec.Desc) (value : Codec.Value)
    (layoutArena arena : Delimited.ArenaState) (view : HashLayout.Layout)
    (expected : Ssz.MerkleLayout) (index : NatOperand) (depth base treeDepth budget : Nat)
    (visit : NodeVisit view) (safe : HashLayout.SafeWidths desc)
    (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (indexPhysical : index.words.length < 2 ^ 64)
    (laidOut : (HashLayout.layout desc value layoutArena).result = .ok view)
    (layoutEq : Ssz.merkleLayout desc.erase value.erase = .ok expected)
    (enough : desc.nesting ≤ budget + 1) (baseFits : base < 2 ^ 64)
    (inside : depth ≤ treeDepth) :
    Refines Eq (boundedNode view index depth base treeDepth arena visit)
      (Ssz.boundedNode budget expected index.value depth base (2 ^ treeDepth)) := by
  obtain ⟨other, otherEq, related⟩ := HashLayout.layout_success desc value layoutArena
    safe descPhysical valuePhysical view laidOut
  rw [layoutEq] at otherEq
  cases Except.ok.inj otherEq
  have countEq := HashLayout.LayoutRefines.count view expected related
  have countFits := HashLayout.layout_count_physical desc value layoutArena view
    descPhysical valuePhysical laidOut
  let span := 2 ^ (treeDepth - depth)
  let start := base + (index.value % 2 ^ depth) * span
  have width : 2 ^ treeDepth >>> depth = span := by
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_div inside (by decide)]
  simp only [Ssz.boundedNode, Ssz.nextPow2, Ssz.depthFor_pow, Nat.log2_two_pow,
    inside, ↓reduceIte, width, Ssz.gindexBelow]
  simp only [boundedNode, inside, ↓reduceIte]
  rw [boundedStart_eq index depth base (treeDepth - depth) indexPhysical baseFits]
  change Refines Eq
    (match physicalIndex start with
    | none => unchanged arena.used (.ok (MerkleAccumulator.zeroSubtree rawCombine Ssz.zeroChunk (treeDepth - depth)))
    | some start => if start < view.count then rangeRoot view start (boundedStop view.count start (treeDepth - depth)) (treeDepth - depth) arena
      else unchanged arena.used (.ok (MerkleAccumulator.zeroSubtree rawCombine Ssz.zeroChunk (treeDepth - depth))))
    (Ssz.layoutChunksAt budget expected start (some (start + span)) >>= fun chunks =>
      Ssz.merkleizeBounded chunks (some span))
  by_cases selected : start < view.count
  · have converted := physicalIndex_of_lt start (by omega)
    rw [converted]
    simp only [selected, ↓reduceIte]
    rw [boundedStop_eq view.count start (treeDepth - depth) countFits]
    rw [← layoutChunksAt_clip budget expected start (start + span), ← countEq]
    have ordered : start ≤ min (start + span) view.count :=
      Nat.le_min.mpr ⟨Nat.le_add_right start span, Nat.le_of_lt selected⟩
    exact rangeRoot_refines_layout desc value layoutArena arena view expected
      start (min (start + span) view.count) (treeDepth - depth) budget
      safe descPhysical valuePhysical laidOut layoutEq enough ordered (Nat.min_le_right _ _)
  · have outside : expected.leaves.count ≤ start := by omega
    rw [layoutChunksAt_outside budget expected start (start + span) outside]
    simp only [Bind.bind, Except.bind]
    rw [empty_depth]
    by_cases physical : start < 2 ^ 64
    · rw [physicalIndex_of_lt start physical]
      simp only [selected, ↓reduceIte]
      exact .ok _ _ (zeroSubtree_raw _)
    · rw [physicalIndex_of_ge start (by omega)]
      exact .ok _ _ (zeroSubtree_raw _)

/-- Relating a physical lookup to a pinned slot also covers inactive progressive
positions; a missing native view is exactly a missing or empty pinned slot. -/
theorem nested_lookup_refines (view : HashLayout.Layout) (expected : Ssz.MerkleLayout)
    (related : HashLayout.LayoutRefines view expected) (position : Nat) :
    (view.nested position).map HashLayout.erasePair =
      (match expected.leaves with | .packed _ => none | .nested slots => slots[position]?.getD none) := by
  cases view with
  | mk leaves limit mixin =>
      cases expected with
      | mk specLeaves specLimit specMixin =>
          cases related.1 with
          | packed packed chunks count each => rfl
          | nested nested slots count each => exact each position

theorem isPacked_refines (view : HashLayout.Layout) (expected : Ssz.MerkleLayout)
    (related : HashLayout.LayoutRefines view expected) :
    view.isPacked = (match expected.leaves with | .packed _ => true | .nested _ => false) := by
  cases view with
  | mk leaves limit mixin =>
      cases expected with
      | mk specLeaves specLimit specMixin =>
          cases related.1 <;> rfl

theorem physicalLeaf_eq (index : NatOperand) (offset width base : Nat)
    (physical : index.words.length < 2 ^ 64) :
    (window index offset width).bind (fun position => physicalIndex (base + position)) =
      physicalIndex (base + (index.value / 2 ^ offset) % 2 ^ width) := by
  rw [window_eq index offset width physical]
  split
  · rfl
  · rename_i large
    have total : ¬base + (index.value / 2 ^ offset) % 2 ^ width < 2 ^ 64 := by omega
    simp [physicalIndex, total]

theorem boundedNode_refines (desc : Codec.Desc) (value : Codec.Value)
    (layoutArena arena : Delimited.ArenaState) (view : HashLayout.Layout)
    (expected : Ssz.MerkleLayout) (index : NatOperand) (depth base treeDepth budget : Nat)
    (visit : NodeVisit view) (safe : HashLayout.SafeWidths desc)
    (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (indexPhysical : index.words.length < 2 ^ 64)
    (laidOut : (HashLayout.layout desc value layoutArena).result = .ok view)
    (layoutEq : Ssz.merkleLayout desc.erase value.erase = .ok expected)
    (enough : desc.nesting ≤ budget + 1) (baseFits : base < 2 ^ 64)
    (visits : ∀ position childDesc child selected below cursor,
      Refines Eq (visit position childDesc child selected below cursor)
        (Ssz.nodeRootAt budget childDesc.erase child.erase (Ssz.gindexRebase index.value below))) :
    Refines Eq (boundedNode view index depth base treeDepth arena visit)
      (Ssz.boundedNode budget expected index.value depth base (2 ^ treeDepth)) := by
  by_cases internal : depth ≤ treeDepth
  · exact boundedNode_internal_refines desc value layoutArena arena view expected index
      depth base treeDepth budget visit safe descPhysical valuePhysical indexPhysical
      laidOut layoutEq enough baseFits internal
  · obtain ⟨other, otherEq, related⟩ := HashLayout.layout_success desc value layoutArena
      safe descPhysical valuePhysical view laidOut
    rw [layoutEq] at otherEq
    cases Except.ok.inj otherEq
    have packed := isPacked_refines view expected related
    have countEq := HashLayout.LayoutRefines.count view expected related
    have countFits := HashLayout.layout_count_physical desc value layoutArena view
      descPhysical valuePhysical laidOut
    cases leavesEq : expected.leaves with
    | packed chunks =>
        simp only [leavesEq] at packed
        simp only [boundedNode, internal, packed, ↓reduceIte, Ssz.boundedNode,
          Ssz.nextPow2, Ssz.depthFor_pow, Nat.log2_two_pow, leavesEq]
        exact .error _ _ rfl
    | nested slots =>
        simp only [leavesEq] at packed
        let below := depth - treeDepth
        let position := base + (index.value / 2 ^ below) % 2 ^ treeDepth
        have spec :
            Ssz.boundedNode budget expected index.value depth base (2 ^ treeDepth) =
              (match slots[position]?.getD none with
              | none => .error .pathIntoGap
              | some (childDesc, child) =>
                  Ssz.nodeRootAt budget childDesc child (Ssz.gindexRebase index.value below)) := by
          simp only [Ssz.boundedNode, Ssz.nextPow2, Ssz.depthFor_pow, Nat.log2_two_pow,
            internal, ↓reduceIte, leavesEq, Ssz.gindexBelow, Nat.shiftRight_eq_div_pow]
          cases slots[position]? with
          | none => rfl
          | some slot =>
              cases slot with
              | none => rfl
              | some pair => rcases pair with ⟨childDesc, child⟩; rfl
        rw [spec]
        simp only [boundedNode, internal, packed, ↓reduceIte,
          physicalLeaf_eq index (depth - treeDepth) treeDepth base indexPhysical]
        change Refines Eq
          (match physicalIndex position with
          | none => unchanged arena.used (.error .pathIntoGap)
          | some position => match selected : view.nested position with
            | none => unchanged arena.used (.error .pathIntoGap)
            | some (childDesc, child) => visit position childDesc child selected below arena)
          (match slots[position]?.getD none with
          | none => .error .pathIntoGap
          | some (childDesc, child) =>
              Ssz.nodeRootAt budget childDesc child (Ssz.gindexRebase index.value below))
        by_cases fits : position < 2 ^ 64
        · rw [physicalIndex_of_lt position fits]
          dsimp only
          have selected := nested_lookup_refines view expected related position
          simp only [leavesEq] at selected
          rw [← selected]
          split
          · rename_i missing
            simpa only [missing, Option.map] using
              (show Refines Eq (unchanged arena.used (.error .pathIntoGap) : Outcome Ssz.Bytes)
                (.error .pathIntoGap) from .error _ _ rfl)
          · rename_i childDesc child childEq
            simpa only [childEq, Option.map, HashLayout.erasePair] using
              visits position childDesc child childEq below arena
        · have absent : slots[position]? = none := by
            apply List.getElem?_eq_none
            simp only [leavesEq, Ssz.Leaves.count] at countEq
            omega
          rw [physicalIndex_of_ge position (by omega), absent]
          exact .error _ _ rfl

end SszNative.Proof
