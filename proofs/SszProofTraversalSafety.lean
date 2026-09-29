import SszProofTraversalWalkRefinement

set_option autoImplicit false

namespace SszNative.Proof

/-- The states actually visited by the source spine loop. A successor exists
only after the current active-level check and an observed right turn. -/
inductive SpineVisited (count : Nat) (index : NatOperand) (fullDepth : Nat) :
    Nat → Nat → Nat → Nat → Prop where
  | initial : SpineVisited count index fullDepth fullDepth 0 1 0
  | right {depth start capacity level : Nat}
      (before : SpineVisited count index fullDepth (depth + 1) start capacity level)
      (active : start < count) (turn : Indices.bit index depth = true) :
      SpineVisited count index fullDepth depth (start + capacity) (capacity * 4) (level + 1)

theorem SpineVisited.invariant {count : Nat} {index : NatOperand}
    {fullDepth depth start capacity level : Nat}
    (visited : SpineVisited count index fullDepth depth start capacity level) :
    SpineInvariant start capacity ∧ capacity = 4 ^ level ∧ depth + level = fullDepth := by
  induction visited with
  | initial => exact ⟨spineInvariant_initial, rfl, by omega⟩
  | right before active turn ih =>
      exact ⟨spineInvariant_step _ _ ih.1, by rw [ih.2.1, Nat.pow_succ], by omega⟩

/-- Includes the state after the final right turn, even when it is already the
terminator: source multiplication is proved safe before the next guard runs. -/
theorem SpineVisited.u128 {count : Nat} {index : NatOperand}
    {fullDepth depth start capacity level : Nat}
    (physical : count < 2 ^ 64)
    (visited : SpineVisited count index fullDepth depth start capacity level) :
    start < 2 ^ 128 ∧ capacity < 2 ^ 128 ∧
      (start < count → start < 2 ^ 64 ∧ start + capacity < 2 ^ 128 ∧ capacity * 4 < 2 ^ 128) := by
  constructor
  · cases visited with
    | initial => decide
    | right before active turn => exact (spine_active_u128 count _ _ physical active before.invariant.1).2.1
  constructor
  · cases visited with
    | initial => decide
    | right before active turn => exact (spine_active_u128 count _ _ physical active before.invariant.1).2.2
  · intro active
    exact spine_active_u128 count start capacity physical active visited.invariant.1

/-- A suffix recursion happens only after rooting its whole current block and
only when another actual leaf remains. Terminal suffixes do not multiply. -/
inductive SuffixVisited (count initialStart initialCapacity : Nat) : Nat → Nat → Prop where
  | initial : SuffixVisited count initialStart initialCapacity initialStart initialCapacity
  | next {start capacity : Nat}
      (before : SuffixVisited count initialStart initialCapacity start capacity)
      (active : start < count)
      (nonterminal : start + progressiveTake (count - start) capacity ≠ count) :
      SuffixVisited count initialStart initialCapacity
        (start + progressiveTake (count - start) capacity) (capacity * 4)

theorem suffix_nonterminal_take (count start capacity : Nat)
    (physical : count < 2 ^ 64) (active : start < count)
    (nonterminal : start + progressiveTake (count - start) capacity ≠ count) :
    progressiveTake (count - start) capacity = capacity ∧ start + capacity < count := by
  rw [progressiveTake_eq_min (count - start) capacity (by omega)] at nonterminal ⊢
  omega

theorem SuffixVisited.invariant {count initialStart initialCapacity start capacity : Nat}
    (physical : count < 2 ^ 64) (initial : SpineInvariant initialStart initialCapacity)
    (visited : SuffixVisited count initialStart initialCapacity start capacity) :
    SpineInvariant start capacity := by
  induction visited with
  | initial => exact initial
  | next before active nonterminal ih =>
      rw [(suffix_nonterminal_take count _ _ physical active nonterminal).1]
      exact spineInvariant_step _ _ ih

theorem SuffixVisited.active {count initialStart initialCapacity start capacity : Nat}
    (physical : count < 2 ^ 64) (initial : initialStart < count)
    (visited : SuffixVisited count initialStart initialCapacity start capacity) : start < count := by
  cases visited with
  | initial => exact initial
  | next before active nonterminal =>
      obtain ⟨taken, activeNext⟩ := suffix_nonterminal_take count _ _ physical active nonterminal
      rw [taken]
      exact activeNext

/-- All source casts, additions, and capacity multiplications at reachable
progressive suffixes are justified solely by actual physical leaf storage. -/
theorem progressive_suffix_native_safe {count : Nat} {index : NatOperand}
    {fullDepth originStart originCapacity level start capacity : Nat}
    (physical : count < 2 ^ 64)
    (spine : SpineVisited count index fullDepth 0 originStart originCapacity level)
    (opened : originStart < count)
    (suffix : SuffixVisited count originStart originCapacity start capacity) :
    start < 2 ^ 64 ∧ start + capacity < 2 ^ 128 ∧ capacity * 4 < 2 ^ 128 := by
  exact spine_active_u128 count start capacity physical (suffix.active physical opened)
    (suffix.invariant physical spine.invariant.1)

/-- Successful planning provides the physical bound used above; logical layout
limits and index values are absent from that bound. -/
theorem node_layout_spine_native_safe (desc : Codec.Desc) (value : Codec.Value)
    (arena : Delimited.ArenaState) (view : HashLayout.Layout)
    (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (planned : (HashLayout.layout desc value arena).result = .ok view)
    (index : NatOperand) (fullDepth depth start capacity level : Nat)
    (visited : SpineVisited view.count index fullDepth depth start capacity level) :
    start < 2 ^ 128 ∧ capacity < 2 ^ 128 ∧
      (start < view.count → start < 2 ^ 64 ∧ start + capacity < 2 ^ 128 ∧ capacity * 4 < 2 ^ 128) :=
  visited.u128 (HashLayout.layout_count_physical desc value arena view descPhysical valuePhysical planned)

end SszNative.Proof
