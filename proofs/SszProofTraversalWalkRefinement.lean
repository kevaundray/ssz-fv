import SszProofTraversalBoundedRefinement
import SszProofTraversalProgressiveRefinement

set_option autoImplicit false

namespace SszNative.Proof

theorem boundedNode_rebase_congr (budget : Nat) (view : Ssz.MerkleLayout)
    (index full depth base capacity : Nat) (inside : depth ≤ full) :
    Ssz.boundedNode budget view (Ssz.gindexRebase index full) depth base capacity =
      Ssz.boundedNode budget view index depth base capacity := by
  unfold Ssz.boundedNode
  split
  · rw [rebase_below index full depth inside]
  · have selected := rebase_window index full (depth - (Ssz.nextPow2 capacity).log2)
        (Ssz.nextPow2 capacity).log2 (by omega)
    simp only [Ssz.gindexBelow, Nat.shiftRight_eq_div_pow]
    rw [selected, rebase_rebase index full (depth - (Ssz.nextPow2 capacity).log2) (by omega)]

theorem progressiveNode_step (budget : Nat) (view : Ssz.MerkleLayout)
    (index depth start capacity : Nat) :
    Ssz.progressiveNode budget view index (depth + 1) start capacity =
      (if start ≥ view.leaves.count then .error .pathPastSpine
      else if !Ssz.gindexBit index depth then
        Ssz.boundedNode budget view index depth start capacity
      else Ssz.progressiveNode budget view index depth (start + capacity) (capacity * 4)) := by
  simp only [Ssz.progressiveNode, Ssz.spineWalk]
  split
  · rfl
  · split <;> rfl

theorem progressiveNode_rebase_congr (budget : Nat) (view : Ssz.MerkleLayout)
    (index full depth start capacity : Nat) (inside : depth ≤ full) :
    Ssz.progressiveNode budget view (Ssz.gindexRebase index full) depth start capacity =
      Ssz.progressiveNode budget view index depth start capacity := by
  induction depth generalizing start capacity with
  | zero => rfl
  | succ depth ih =>
      rw [progressiveNode_step, progressiveNode_step,
        rebase_bit index full depth (by omega)]
      split
      · rfl
      · split
        · exact boundedNode_rebase_congr budget view index full depth start capacity (by omega)
        · exact ih (start + capacity) (capacity * 4) (by omega)

theorem progressiveNodeFrom_refines (desc : Codec.Desc) (value : Codec.Value)
    (layoutArena arena : Delimited.ArenaState) (view : HashLayout.Layout)
    (expected : Ssz.MerkleLayout) (index : NatOperand) (depth start level budget : Nat)
    (visit : NodeVisit view) (safe : HashLayout.SafeWidths desc)
    (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (indexPhysical : index.words.length < 2 ^ 64)
    (laidOut : (HashLayout.layout desc value layoutArena).result = .ok view)
    (layoutEq : Ssz.merkleLayout desc.erase value.erase = .ok expected)
    (enough : desc.nesting ≤ budget + 1)
    (visits : ∀ position childDesc child selected below cursor,
      Refines Eq (visit position childDesc child selected below cursor)
        (Ssz.nodeRootAt budget childDesc.erase child.erase (Ssz.gindexRebase index.value below))) :
    Refines Eq (progressiveNodeFrom view index visit depth start (4 ^ level)
      (Nat.pow_pos (by decide)) arena)
      (Ssz.progressiveNode budget expected index.value depth start (4 ^ level)) := by
  obtain ⟨other, otherEq, related⟩ := HashLayout.layout_success desc value layoutArena
    safe descPhysical valuePhysical view laidOut
  rw [layoutEq] at otherEq
  cases Except.ok.inj otherEq
  have countEq := HashLayout.LayoutRefines.count view expected related
  have countFits := HashLayout.layout_count_physical desc value layoutArena view
    descPhysical valuePhysical laidOut
  induction depth generalizing start level with
  | zero =>
      have refined := progressiveFrom_refines_layout desc value layoutArena arena view expected
        start level budget safe descPhysical valuePhysical laidOut layoutEq enough
      simp only [Ssz.progressiveNode, Ssz.spineWalk, Except.bind] at ⊢
      simp only [progressiveNodeFrom]
      split
      · exact refined
      · rename_i outside
        rw [progressiveFrom, dif_neg outside] at refined
        exact refined
  | succ depth ih =>
      rw [progressiveNode_step]
      simp only [progressiveNodeFrom, ← countEq, Indices.bit_refines index depth indexPhysical]
      split
      · exact .error _ _ rfl
      · rename_i active
        split
        · have refined := boundedNode_refines desc value layoutArena arena view expected index
            depth start (4 ^ level).log2 budget visit safe descPhysical valuePhysical indexPhysical
            laidOut layoutEq enough (by omega) visits
          have width : 2 ^ (4 ^ level).log2 = 4 ^ level := by
            rw [MerkleProgressive.width_eq, Nat.log2_two_pow]
          rw [width] at refined
          exact refined
        · simpa only [Nat.pow_succ] using ih (start + 4 ^ level) (level + 1)

theorem progressiveNode_refines (desc : Codec.Desc) (value : Codec.Value)
    (layoutArena arena : Delimited.ArenaState) (view : HashLayout.Layout)
    (expected : Ssz.MerkleLayout) (index : NatOperand) (depth budget : Nat)
    (visit : NodeVisit view) (safe : HashLayout.SafeWidths desc)
    (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (indexPhysical : index.words.length < 2 ^ 64)
    (laidOut : (HashLayout.layout desc value layoutArena).result = .ok view)
    (layoutEq : Ssz.merkleLayout desc.erase value.erase = .ok expected)
    (enough : desc.nesting ≤ budget + 1)
    (visits : ∀ position childDesc child selected below cursor,
      Refines Eq (visit position childDesc child selected below cursor)
        (Ssz.nodeRootAt budget childDesc.erase child.erase (Ssz.gindexRebase index.value below))) :
    Refines Eq (progressiveNode view index depth arena visit)
      (Ssz.progressiveNode budget expected index.value depth 0 1) :=
  progressiveNodeFrom_refines desc value layoutArena arena view expected index depth 0 0 budget
    visit safe descPhysical valuePhysical indexPhysical laidOut layoutEq enough visits

end SszNative.Proof
