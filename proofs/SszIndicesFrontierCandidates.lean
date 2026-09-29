import SszIndicesFrontier
import SszIndicesArithmeticSemanticPrefix
import SszIndicesPinnedFrontier

set_option autoImplicit false

namespace SszNative.Indices

/-- A proof-only view of the count/fill enumeration, not an allocated temporary
in the native model. Each key retains its original request ordinal and level. -/
def helperCandidateKeys (indices : List NatOperand) : List (NatOperand × Nat × Nat) :=
  indices.zipIdx.flatMap fun pair =>
    ((List.range (depth pair.1)).filter (isHelper indices pair.1 pair.2)).map
      (fun level => (pair.1, pair.2, level))

def helperCandidateValue (key : NatOperand × Nat × Nat) : Nat :=
  Ssz.gindexSibling (key.1.value >>> key.2.2)

def helperCandidates (indices : List NatOperand) : List Nat :=
  (helperCandidateKeys indices).map helperCandidateValue

theorem shift_log2 (index level : Nat) (named : 1 ≤ index)
    (within : level ≤ index.log2) :
    (index >>> level).log2 = index.log2 - level := by
  induction level with
  | zero => simp
  | succ level ih =>
      have before : level < index.log2 := by omega
      have below := path_shift_positive named before
      have previous := ih (by omega)
      have recursion := Nat.log2_def (index >>> level)
      simp only [below, ↓reduceIte] at recursion
      rw [Ssz.shiftRight_succ]
      omega

theorem path_level_unique (index left right : Nat) (named : 1 ≤ index)
    (leftInside : left < index.log2) (rightInside : right < index.log2)
    (same : index >>> left = index >>> right) : left = right := by
  have leftDepth := shift_log2 index left named (by omega)
  have rightDepth := shift_log2 index right named (by omega)
  rw [same] at leftDepth
  omega

theorem sibling_log2 (index : Nat) (below : 2 ≤ index) :
    (Ssz.gindexSibling index).log2 = index.log2 := by
  exact pinned_sibling_log2 index below

theorem sibling_injective (left right : Nat)
    (same : Ssz.gindexSibling left = Ssz.gindexSibling right) : left = right := by
  have inverted := congrArg Ssz.gindexSibling same
  simpa only [Ssz.gindexSibling_sibling] using inverted

/-- Every level traversed by the frontier lies in the prefix comparator's
non-root flip domain, including all raw zero-padded representations. -/
theorem candidate_flip_domain (index : NatOperand) (level : Nat)
    (inside : level < depth index) : PrefixFlipDomain index level true := by
  intro _
  unfold depth at inside
  omega

end SszNative.Indices
