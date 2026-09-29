import SszArm.IndicesStorage
import SszArm.IndicesLinkedSortInsertion
import SszArm.NatCompareProofs
import SszIndicesFrontierOrder

namespace SszArm.Indices.SortInsertion

open SszNative (NatOperand)
open SszArm.Codec.Storage (Image Physical Backing)
open Delimited (Span Protected MemoryFrame Returned)

/-- Sixty-four saved bytes and the sixteen-byte lowering/comparison slot. -/
def stackSpan (s : ArmState) : Span :=
  ((r (.GPR 31#5) s).toNat - 80, 80)

def writes (s : ArmState) (values : List NatOperand) : List Span :=
  [stackSpan s] ++ Storage.mutableSpan (r (.GPR 0#5) s).toNat (16 * values.length)

/-- Only physical ownership and the helper's nonempty-slice API requirement.
The record image protects headers from the stack, not from their own writes;
backing protection additionally excludes the mutable record array. Distinct
readonly limb slices need not be disjoint. No logical-value bound is imposed. -/
structure Owned (s : ArmState) (values : List NatOperand) : Prop where
  nonempty : 0 < values.length
  count : (r (.GPR 1#5) s).toNat = values.length
  stack : 80 ≤ (r (.GPR 31#5) s).toNat
  records : (Storage.operands (r (.GPR 0#5) s).toNat values).Owned [stackSpan s] s
  backings : ∀ value ∈ values, Backing (Protected (writes s values)) value

/-- Numeric ordering does not identify distinct representations of equal values. -/
def Descending (values : List NatOperand) : Prop :=
  values.Pairwise (fun left right => right.value ≤ left.value)

/-- Observes all borrowed limb bytes, including trailing zero limbs. The zero-byte
case is vacuous, so an empty Large imposes no spurious separation requirement. -/
def BackingsPreserved (values : List NatOperand) (s t : ArmState) : Prop :=
  ∀ pointer words, NatOperand.large pointer words ∈ values →
    ∀ a : BitVec 64, pointer.toNat ≤ a.toNat →
      a.toNat < pointer.toNat + 8 * words.length → t.mem a = s.mem a

structure Post (s t : ArmState) (input output : List NatOperand) : Prop where
  returned : Returned s t
  program : t.program = s.program
  permutation : output.Perm input
  descending : Descending output
  records : (Storage.operands (r (.GPR 0#5) s).toNat output).At t
  frame : MemoryFrame (writes s input) s t
  backings : BackingsPreserved input s t

theorem backings_preserved {s t : ArmState} {values : List NatOperand}
    (owned : Owned s values) (frame : MemoryFrame (writes s values) s t) :
    BackingsPreserved values s t := by
  intro pointer words member a low high
  have protected := (owned.backings (.large pointer words) member).2
  apply frame
  intro span spanMember
  rcases protected with empty | apart
  · omega
  · have separate := apart span spanMember
    omega

/-- Equal numeric values determine equal raw operands within a value-unique
frontier. This is not assumed by the insertion-sort helper itself. -/
theorem operand_eq_of_unique {values : List NatOperand}
    (unique : (values.map NatOperand.value).Nodup)
    {left right : NatOperand} (leftMem : left ∈ values) (rightMem : right ∈ values)
    (equal : left.value = right.value) : left = right := by
  induction values generalizing left right with
  | nil => simp at leftMem
  | cons first rest ih =>
      have split := List.nodup_cons.mp unique
      rcases List.mem_cons.mp leftMem with rfl | leftMem
      · rcases List.mem_cons.mp rightMem with rfl | rightMem
        · rfl
        · exact False.elim (split.1 (List.mem_map.mpr ⟨right, rightMem, equal.symm⟩))
      · rcases List.mem_cons.mp rightMem with rfl | rightMem
        · exact False.elim (split.1 (List.mem_map.mpr ⟨left, leftMem, equal⟩))
        · exact ih split.2 leftMem rightMem equal

/-- The original frontier's source sort event retains the exact raw operands.
Unique values turn numeric sortedness plus a raw permutation into equality with
that source event, without a stability assumption on the machine sort. -/
theorem source_sort_eq {input output : List NatOperand}
    (permutation : output.Perm input) (ordered : Descending output)
    (unique : (input.map NatOperand.value).Nodup) :
    output = input.mergeSort (fun left right => right.value ≤ left.value) := by
  apply List.Perm.eq_of_pairwise
    (le := fun left right : NatOperand => right.value ≤ left.value)
  · intro left right leftMem rightMem first second
    apply operand_eq_of_unique unique (permutation.subset leftMem)
      (List.mem_mergeSort.mp rightMem)
    omega
  · exact ordered
  · have sorted := List.pairwise_mergeSort
      (le := fun left right : NatOperand => decide (right.value ≤ left.value))
      (by intro a b c first second; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) input
    simpa only [decide_eq_true_eq] using sorted
  · exact permutation.trans (List.mergeSort_perm _ _).symm

theorem Post.source_sort {s t : ArmState} {input output : List NatOperand}
    (post : Post s t input output) (unique : (input.map NatOperand.value).Nodup) :
    output = input.mergeSort (fun left right => right.value ≤ left.value) :=
  source_sort_eq post.permutation post.descending unique

end SszArm.Indices.SortInsertion
