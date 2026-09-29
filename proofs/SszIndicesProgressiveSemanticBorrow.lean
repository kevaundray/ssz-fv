import SszIndicesProgressive
import SszIndicesProgressiveSemanticAlgebra
import SszIndicesArithmeticSemanticCore

set_option autoImplicit false

namespace SszNative.Indices.ProgressiveSemantic

/-- The subtraction portion of the source initializer, before either OR mask. -/
def difference (source offset : BitVec 64) (borrow : Bool) : BitVec 64 :=
  (source - offset) - (if borrow then 1 else 0)

def nextBorrow (source offset : BitVec 64) (borrow : Bool) : Bool :=
  decide (source.toNat < offset.toNat) ||
    decide ((source - offset).toNat < (if borrow then (1 : BitVec 64) else 0).toNat)

/-- Two overflowing subtractions implement one base-2^64 borrow, including the
case where the incoming borrow alone underflows a zero difference. -/
theorem difference_balance (source offset : BitVec 64) (borrow : Bool) :
    source.toNat + 2 ^ 64 * (nextBorrow source offset borrow).toNat =
      offset.toNat + borrow.toNat + (difference source offset borrow).toNat := by
  have sourceBound := source.isLt
  have offsetBound := offset.isLt
  have firstBound := (source - offset).isLt
  have firstValue := BitVec.toNat_sub source offset
  cases borrow with
  | false =>
      by_cases first : source.toNat < offset.toNat <;>
        simp [difference, nextBorrow, first] <;> omega
  | true =>
      have secondValue := BitVec.toNat_sub (source - offset) (1 : BitVec 64)
      rw [show (1 : BitVec 64).toNat = 1 from rfl] at secondValue
      change source.toNat + 2 ^ 64 *
          (decide (source.toNat < offset.toNat) ||
            decide ((source - offset).toNat < 1)).toNat =
        offset.toNat + 1 + ((source - offset) - (1 : BitVec 64)).toNat
      by_cases first : source.toNat < offset.toNat
      · simp only [first, decide_true, Bool.true_or, Bool.toNat_true]
        omega
      · simp only [first, decide_false, Bool.false_or]
        by_cases second : (source - offset).toNat < 1
        · simp only [second, decide_true, Bool.toNat_true]
          omega
        · simp only [second, decide_false, Bool.toNat_false]
          omega

/-- Quotient form of the borrow invariant. It avoids signed arithmetic and
makes no bound on the represented natural, only on each individual limb. -/
def BorrowInvariant (chunk start residue position : Nat) (borrow : Bool) : Prop :=
  chunk / 2 ^ (64 * position) =
    residue / 2 ^ (64 * position) + start / 2 ^ (64 * position) + borrow.toNat

theorem borrow_initial (chunk start : Nat) (lower : start ≤ chunk) :
    BorrowInvariant chunk start (chunk - start) 0 false := by
  simp only [BorrowInvariant, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Bool.toNat_false]
  omega

/-- The exact two-subtraction state transition recovers the next result digit
and re-establishes the quotient invariant for the following source word. -/
theorem borrow_transition (chunk start residue position : Nat) (borrow : Bool)
    (source offset : BitVec 64)
    (sourceValue : source.toNat = (chunk / 2 ^ (64 * position)) % 2 ^ 64)
    (offsetValue : offset.toNat = (start / 2 ^ (64 * position)) % 2 ^ 64)
    (invariant : BorrowInvariant chunk start residue position borrow) :
    (difference source offset borrow).toNat =
        (residue / 2 ^ (64 * position)) % 2 ^ 64 ∧
      BorrowInvariant chunk start residue (position + 1) (nextBorrow source offset borrow) := by
  have balance := difference_balance source offset borrow
  have remainderBound := (difference source offset borrow).isLt
  have residueDecomposition := Nat.mod_add_div (residue / 2 ^ (64 * position)) (2 ^ 64)
  have sourceDecomposition := Nat.mod_add_div (chunk / 2 ^ (64 * position)) (2 ^ 64)
  have offsetDecomposition := Nat.mod_add_div (start / 2 ^ (64 * position)) (2 ^ 64)
  have residueBound := Nat.mod_lt (residue / 2 ^ (64 * position)) (by decide : 0 < 2 ^ 64)
  have nextPower : 2 ^ (64 * (position + 1)) = 2 ^ (64 * position) * 2 ^ 64 := by
    rw [← Nat.pow_add]
    congr 1 <;> omega
  unfold BorrowInvariant at invariant ⊢
  rw [nextPower, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul]
  rw [sourceValue, offsetValue] at balance
  omega

theorem progressiveStep_borrow (chunk : NatOperand) (subtreeDepth position : Nat)
    (borrow : Bool) :
    (progressiveStep chunk subtreeDepth position borrow).2 =
      nextBorrow (word chunk position) (thresholdWord subtreeDepth position) borrow := rfl

theorem progressiveStep_word (chunk : NatOperand) (subtreeDepth position : Nat)
    (borrow : Bool) :
    (progressiveStep chunk subtreeDepth position borrow).1 =
      difference (word chunk position) (thresholdWord subtreeDepth position) borrow |||
        rangeWord position (subtreeDepth + 1) (subtreeDepth + subtreeDepth / 2 + 1) |||
        rangeWord position (subtreeDepth + subtreeDepth / 2 + 2)
          (subtreeDepth + subtreeDepth / 2 + 2 + 1) := rfl

end SszNative.Indices.ProgressiveSemantic
