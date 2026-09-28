import SszNatAdd
import SszLimbMul

set_option autoImplicit false

/- Exact mathematical algorithm/resource model of native/src/nat.rs:287–314,
409–428. Original operands may have arbitrary redundant high zero words.
This file is not an ISA execution or a memory-separation proof. -/
namespace SszNative.NatMul

open NatArithmetic

local notation "B" => (2 ^ 64 : Nat)

/-- The original word(0), not a replacement canonical operand. -/
def lowWord (operand : NatOperand) : BitVec 64 := NatAdd.lowWord operand

def wordProduct (operand : NatOperand) (factor : BitVec 64) : BitVec 128 :=
  LimbMul.wideProduct (lowWord operand) factor 0 0

/-- All mul_word scratch writes, including the zero-extended final input word. -/
def wordWritten (operand : NatOperand) (factor : BitVec 64) : List (BitVec 64) :=
  (LimbMul.inner (operand.wordCount + 1) factor (Limbs.trim operand.words) [] 0).1

/-- Every word of the zero-filled, row-major multiplication destination. -/
def writtenWords (left right : NatOperand) : List (BitVec 64) :=
  LimbMul.mul (Limbs.trim left.words) (Limbs.trim right.words)

/-- Checked usize addition precedes reserve; the write loop is invoked only in
the successful reservation branch. No logical operand length cap is imposed. -/
private def allocate (count : Nat) (makeWords : Unit → List (BitVec 64))
    (base capacity used : Nat) : Outcome NatOperand :=
  if count < B then
    match Arena.reserve base capacity used count with
    | none => unchanged used (.error .scratchExhausted)
    | some reservation => committed reservation (makeWords ())
  else unchanged used (.error .scratchExhausted)

/-- Native factor-zero, factor-one, from_u128, and allocating branch order. -/
def runWord (operand : NatOperand) (factor : BitVec 64)
    (base capacity used : Nat) : Outcome NatOperand :=
  if factor = 0 then unchanged used (.ok (.small 0))
  else if factor = 1 then unchanged used (.ok operand.normalized)
  else if operand.wordCount ≤ 1 then fromWide base capacity used (wordProduct operand factor)
  else allocate (operand.wordCount + 1) (fun _ => wordWritten operand factor) base capacity used

/-- Significant scans precede zero; the right-one branch precedes left-one. -/
def run (left right : NatOperand) (base capacity used : Nat) : Outcome NatOperand :=
  let leftCount := left.wordCount
  let rightCount := right.wordCount
  if leftCount = 0 ∨ rightCount = 0 then unchanged used (.ok (.small 0))
  else if rightCount = 1 then runWord left (lowWord right) base capacity used
  else if leftCount = 1 then runWord right (lowWord left) base capacity used
  else allocate (leftCount + rightCount) (fun _ => writtenWords left right) base capacity used

private theorem zero_value (operand : NatOperand) (zero : operand.wordCount = 0) :
    operand.value = 0 := by
  have length : (Limbs.trim operand.words).length = 0 := by
    rw [← NatOperand.wordCount_eq_trim_length, zero]
  exact (Limbs.trim_eq_nil_iff_value_zero operand.words).mp
    (List.eq_nil_of_length_eq_zero length)

theorem wordProduct_value (operand : NatOperand) (factor : BitVec 64)
    (small : operand.wordCount ≤ 1) :
    (wordProduct operand factor).toNat = operand.value * factor.toNat := by
  rw [wordProduct, LimbMul.wideProduct_toNat _ _ _ 0 (by decide)]
  change (lowWord operand).toNat * factor.toNat + 0 + 0 = operand.value * factor.toNat
  simp only [Nat.add_zero, lowWord, NatAdd.lowWord_value operand small]

/-- Zero extension observes the original physical operand at every inner index,
even when its redundant suffix extends beyond the significant prefix. -/
theorem inner_trim_eq_native (width index : Nat) (factor : BitVec 64)
    (words old : List (BitVec 64)) (carry : Nat) :
    LimbMul.inner width factor ((Limbs.trim words).drop index) (old.drop index) carry =
      LimbMul.inner width factor (words.drop index) (old.drop index) carry := by
  induction width generalizing index carry with
  | zero => rfl
  | succ width ih =>
      simp only [LimbMul.inner_indexed_succ, NatAdd.trim_word, ih]

theorem wordWritten_native_loop (operand : NatOperand) (factor : BitVec 64) :
    wordWritten operand factor =
      (LimbMul.inner (operand.wordCount + 1) factor operand.words [] 0).1 := by
  have same := inner_trim_eq_native (operand.wordCount + 1) 0 factor operand.words [] 0
  simpa only [List.drop_zero, wordWritten] using congrArg Prod.fst same

/-- General multiplication uses exactly the significant prefixes of the original
lists. Each inner recurrence is `LimbMul.inner_indexed_succ`; trimming preserves
all its original indexed observations by `inner_trim_eq_native`. -/
theorem writtenWords_native_loop (left right : NatOperand) :
    writtenWords left right =
      LimbMul.nativeRows (left.words.take left.wordCount) (right.words.take right.wordCount)
        (List.replicate (left.wordCount + right.wordCount) 0) := by
  rw [writtenWords, LimbMul.mul_native]
  rw [← NatOperand.wordCount_eq_trim_length left, ← NatOperand.wordCount_eq_trim_length right,
    NatAdd.trimmed_prefix left, NatAdd.trimmed_prefix right]

theorem wordWritten_length (operand : NatOperand) (factor : BitVec 64) :
    (wordWritten operand factor).length = operand.wordCount + 1 :=
  LimbMul.inner_length _ _ _ _ _

theorem wordWritten_final_carry (operand : NatOperand) (factor : BitVec 64) :
    (LimbMul.inner (operand.wordCount + 1) factor (Limbs.trim operand.words) [] 0).2 = 0 := by
  apply LimbMul.inner_extra_carry_zero
  · rw [← NatOperand.wordCount_eq_trim_length]
    omega
  · decide

theorem wordWritten_value (operand : NatOperand) (factor : BitVec 64) :
    Limbs.value (wordWritten operand factor) = operand.value * factor.toNat := by
  have complete := LimbMul.inner_value_complete (operand.wordCount + 1) factor
    (Limbs.trim operand.words) [] 0
    (by rw [← NatOperand.wordCount_eq_trim_length]; omega) (by simp)
  simpa only [wordWritten_final_carry, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Limbs.value,
    Limbs.trim_value, NatOperand.value, wordWritten, Nat.mul_comm] using complete

theorem writtenWords_length (left right : NatOperand) :
    (writtenWords left right).length = left.wordCount + right.wordCount := by
  simp only [writtenWords, LimbMul.mul_length, ← NatOperand.wordCount_eq_trim_length]

theorem writtenWords_value (left right : NatOperand) :
    Limbs.value (writtenWords left right) = left.value * right.value := by
  rw [writtenWords, LimbMul.mul_value, Limbs.trim_value, Limbs.trim_value]
  rfl

theorem runWord_zero (operand : NatOperand) (base capacity used : Nat) :
    runWord operand 0 base capacity used = unchanged used (.ok (.small 0)) := by
  simp only [runWord, ↓reduceIte]

theorem runWord_one (operand : NatOperand) (base capacity used : Nat) :
    runWord operand 1 base capacity used = unchanged used (.ok operand.normalized) := by
  simp [runWord]

theorem runWord_small (operand : NatOperand) (factor : BitVec 64) (base capacity used : Nat)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (small : operand.wordCount ≤ 1) :
    runWord operand factor base capacity used = fromWide base capacity used (wordProduct operand factor) := by
  simp only [runWord, nonzero, notone, small, ↓reduceIte]

theorem runWord_large (operand : NatOperand) (factor : BitVec 64) (base capacity used : Nat)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (large : 1 < operand.wordCount) :
    runWord operand factor base capacity used =
      if operand.wordCount + 1 < B then
        match Arena.reserve base capacity used (operand.wordCount + 1) with
        | none => unchanged used (.error .scratchExhausted)
        | some reservation => committed reservation (wordWritten operand factor)
      else unchanged used (.error .scratchExhausted) := by
  simp only [runWord, nonzero, notone, show ¬ operand.wordCount ≤ 1 by omega,
    ↓reduceIte, allocate]

theorem run_zero (left right : NatOperand) (base capacity used : Nat)
    (zero : left.wordCount = 0 ∨ right.wordCount = 0) :
    run left right base capacity used = unchanged used (.ok (.small 0)) := by
  simp only [run, zero, ↓reduceIte]

/-- In particular this branch wins when both significant lengths are one. -/
theorem run_right_one (left right : NatOperand) (base capacity used : Nat)
    (nonzero : left.wordCount ≠ 0) (one : right.wordCount = 1) :
    run left right base capacity used = runWord left (lowWord right) base capacity used := by
  simp [run, nonzero, one]

theorem run_left_one (left right : NatOperand) (base capacity used : Nat)
    (one : left.wordCount = 1) (nonzero : right.wordCount ≠ 0) (notone : right.wordCount ≠ 1) :
    run left right base capacity used = runWord right (lowWord left) base capacity used := by
  simp [run, one, nonzero, notone]

theorem run_large (left right : NatOperand) (base capacity used : Nat)
    (hl : 1 < left.wordCount) (hr : 1 < right.wordCount) :
    run left right base capacity used =
      if left.wordCount + right.wordCount < B then
        match Arena.reserve base capacity used (left.wordCount + right.wordCount) with
        | none => unchanged used (.error .scratchExhausted)
        | some reservation => committed reservation (writtenWords left right)
      else unchanged used (.error .scratchExhausted) := by
  simp only [run, show left.wordCount ≠ 0 by omega, show right.wordCount ≠ 0 by omega,
    show left.wordCount ≠ 1 by omega, show right.wordCount ≠ 1 by omega,
    false_or, ↓reduceIte, allocate]

private theorem allocate_value (count : Nat) (makeWords : Unit → List (BitVec 64))
    (base capacity used : Nat) (result : NatOperand)
    (success : (allocate count makeWords base capacity used).result = .ok result) :
    result.value = Limbs.value (makeWords ()) := by
  unfold allocate at success
  split at success
  · split at success
    · cases success
    · cases success
      exact NatOperand.fromWords_value _ _
  · cases success

theorem runWord_value (operand : NatOperand) (factor : BitVec 64)
    (base capacity used : Nat) (result : NatOperand)
    (success : (runWord operand factor base capacity used).result = .ok result) :
    result.value = operand.value * factor.toNat := by
  by_cases zero : factor = 0
  · subst factor
    rw [runWord_zero] at success
    cases success
    simp [NatOperand.value, NatOperand.words, Limbs.value]
  · by_cases one : factor = 1
    · subst factor
      rw [runWord_one] at success
      cases success
      simp [NatOperand.normalized_value]
    · by_cases small : operand.wordCount ≤ 1
      · rw [runWord_small operand factor base capacity used zero one small] at success
        exact (fromWide_value base capacity used _ result success).trans
          (wordProduct_value operand factor small)
      · simp only [runWord, zero, one, small, ↓reduceIte] at success
        exact (allocate_value _ _ base capacity used result success).trans
          (wordWritten_value operand factor)

theorem run_value (left right : NatOperand) (base capacity used : Nat) (result : NatOperand)
    (success : (run left right base capacity used).result = .ok result) :
    result.value = left.value * right.value := by
  by_cases zero : left.wordCount = 0 ∨ right.wordCount = 0
  · rw [run_zero left right base capacity used zero] at success
    cases success
    rcases zero with hl | hr
    · rw [zero_value left hl, Nat.zero_mul]
      rfl
    · rw [zero_value right hr, Nat.mul_zero]
      rfl
  · have hl : left.wordCount ≠ 0 := fun h => zero (Or.inl h)
    have hr : right.wordCount ≠ 0 := fun h => zero (Or.inr h)
    by_cases rightOne : right.wordCount = 1
    · rw [run_right_one left right base capacity used hl rightOne] at success
      rw [runWord_value left (lowWord right) base capacity used result success,
        lowWord, NatAdd.lowWord_value right (by omega)]
    · by_cases leftOne : left.wordCount = 1
      · rw [run_left_one left right base capacity used leftOne hr rightOne] at success
        rw [runWord_value right (lowWord left) base capacity used result success,
          lowWord, NatAdd.lowWord_value left (by omega), Nat.mul_comm]
      · simp only [run, zero, rightOne, leftOne, ↓reduceIte] at success
        exact (allocate_value _ _ base capacity used result success).trans (writtenWords_value left right)

/-- Exact mul_word exhaustion guards. Machine-count overflow is resource failure,
not an artificial bound on the natural represented by the operand. -/
theorem runWord_scratch_exhausted_iff (operand : NatOperand) (factor : BitVec 64)
    (base capacity used : Nat) :
    (runWord operand factor base capacity used).result = .error .scratchExhausted ↔
      factor ≠ 0 ∧ factor ≠ 1 ∧
        if operand.wordCount ≤ 1 then
          B ≤ operand.value * factor.toNat ∧ Arena.reserve base capacity used 2 = none
        else B ≤ operand.wordCount + 1 ∨
          (operand.wordCount + 1 < B ∧ Arena.reserve base capacity used (operand.wordCount + 1) = none) := by
  by_cases hz : factor = 0
  · simp [runWord, hz, unchanged]
  · by_cases ho : factor = 1
    · simp [runWord, ho, unchanged]
    · by_cases hs : operand.wordCount ≤ 1
      · rw [runWord_small operand factor base capacity used hz ho hs]
        simp only [Ne, hz, ho, hs, not_false_eq_true, true_and, ↓reduceIte]
        rw [fromWide, wordProduct_value operand factor hs]
        by_cases fits : operand.value * factor.toNat < B
        · simp [fits, unchanged, show ¬ B ≤ operand.value * factor.toNat by omega]
        · cases reserved : Arena.reserve base capacity used 2 <;>
            simp [fits, unchanged, committed, show B ≤ operand.value * factor.toNat by omega]
      · rw [runWord_large operand factor base capacity used hz ho (by omega)]
        simp only [Ne, hz, ho, hs, not_false_eq_true, true_and, ↓reduceIte]
        by_cases fits : operand.wordCount + 1 < B
        · cases reserved : Arena.reserve base capacity used (operand.wordCount + 1) <;>
            simp [fits, unchanged, committed, show ¬ B ≤ operand.wordCount + 1 by omega]
        · simp [fits, unchanged, show B ≤ operand.wordCount + 1 by omega]

/-- Ordered general multiplication guards; the one-word subconditions are fully
characterized by runWord_scratch_exhausted_iff, including factor 0 and 1. -/
theorem scratch_exhausted_iff (left right : NatOperand) (base capacity used : Nat) :
    (run left right base capacity used).result = .error .scratchExhausted ↔
      left.wordCount ≠ 0 ∧ right.wordCount ≠ 0 ∧
        if right.wordCount = 1 then
          (runWord left (lowWord right) base capacity used).result = .error .scratchExhausted
        else if left.wordCount = 1 then
          (runWord right (lowWord left) base capacity used).result = .error .scratchExhausted
        else B ≤ left.wordCount + right.wordCount ∨
          (left.wordCount + right.wordCount < B ∧
            Arena.reserve base capacity used (left.wordCount + right.wordCount) = none) := by
  by_cases hl : left.wordCount = 0
  · simp [run, hl, unchanged]
  · by_cases hr : right.wordCount = 0
    · simp [run, hl, hr, unchanged]
    · by_cases ro : right.wordCount = 1
      · simp [run, hl, ro]
      · by_cases lo : left.wordCount = 1
        · simp [run, hr, ro, lo]
        · simp only [run, hl, hr, ro, lo, false_or, ↓reduceIte,
            Ne, not_false_eq_true, true_and, allocate]
          by_cases fits : left.wordCount + right.wordCount < B
          · cases reserved : Arena.reserve base capacity used (left.wordCount + right.wordCount) <;>
              simp [fits, unchanged, committed, show ¬ B ≤ left.wordCount + right.wordCount by omega]
          · simp [fits, unchanged, show B ≤ left.wordCount + right.wordCount by omega]

/-- Resource classification uses the existing Arena.reserve and Outcome, without
assuming valid storage or capping logical operands. The allocated arm has no
post-reservation failure and retains the complete normalized-result buffer. -/
def Resources (base capacity used : Nat) (outcome : Outcome NatOperand) : Prop :=
  (∃ result, outcome = unchanged used result ∧ result ≠ .error .badRepresentation) ∨
  (∃ reservation words, 0 < words.length ∧
    Arena.reserve base capacity used words.length = some reservation ∧
    outcome = committed reservation words)

private theorem unchanged_resources (base capacity used : Nat) (result : Except Failure NatOperand)
    (valid : result ≠ .error .badRepresentation) :
    Resources base capacity used (unchanged used result) :=
  Or.inl ⟨result, rfl, valid⟩

private theorem fromWide_resources (base capacity used : Nat) (wide : BitVec 128) :
    Resources base capacity used (fromWide base capacity used wide) := by
  unfold fromWide
  split
  · exact unchanged_resources _ _ _ _ (by intro h; cases h)
  · split
    · exact unchanged_resources _ _ _ _ (by intro h; cases h)
    · rename_i reservation reserved
      exact Or.inr ⟨reservation, [wide.setWidth 64, (wide >>> 64).setWidth 64],
        by simp, reserved, rfl⟩

private theorem allocate_resources (count : Nat) (makeWords : Unit → List (BitVec 64))
    (base capacity used : Nat) (positive : 0 < count) (length : (makeWords ()).length = count) :
    Resources base capacity used (allocate count makeWords base capacity used) := by
  unfold allocate
  split
  · split
    · exact unchanged_resources _ _ _ _ (by intro h; cases h)
    · rename_i reservation reserved
      exact Or.inr ⟨reservation, makeWords (), by omega, by simpa only [length] using reserved, rfl⟩
  · exact unchanged_resources _ _ _ _ (by intro h; cases h)

theorem runWord_resources (operand : NatOperand) (factor : BitVec 64) (base capacity used : Nat) :
    Resources base capacity used (runWord operand factor base capacity used) := by
  unfold runWord
  split
  · exact unchanged_resources _ _ _ _ (by intro h; cases h)
  · split
    · exact unchanged_resources _ _ _ _ (by intro h; cases h)
    · split
      · exact fromWide_resources _ _ _ _
      · exact allocate_resources _ _ _ _ _ (by omega) (wordWritten_length operand factor)

theorem run_resources (left right : NatOperand) (base capacity used : Nat) :
    Resources base capacity used (run left right base capacity used) := by
  dsimp only [run]
  split
  · exact unchanged_resources _ _ _ _ (by intro h; cases h)
  · rename_i nonzero
    split
    · exact runWord_resources _ _ _ _ _
    · split
      · exact runWord_resources _ _ _ _ _
      · apply allocate_resources
        · omega
        · exact writtenWords_length left right

private theorem resources_failure (base capacity used : Nat) (outcome : Outcome NatOperand)
    (resources : Resources base capacity used outcome) (reason : Failure)
    (failed : outcome.result = .error reason) : outcome = unchanged used (.error reason) := by
  rcases resources with ⟨result, same, valid⟩ | ⟨reservation, words, positive, reserved, same⟩
  · rw [same] at failed ⊢
    cases failed
    rfl
  · rw [same] at failed
    cases failed

theorem runWord_failure_unchanged (operand : NatOperand) (factor : BitVec 64)
    (base capacity used : Nat) (reason : Failure)
    (failed : (runWord operand factor base capacity used).result = .error reason) :
    runWord operand factor base capacity used = unchanged used (.error reason) :=
  resources_failure _ _ _ _ (runWord_resources operand factor base capacity used) reason failed

/-- Every failure precedes reservation/writing. In particular no committed
reservation is rolled back, and no error erases a previously consumed cursor. -/
theorem failure_unchanged (left right : NatOperand) (base capacity used : Nat) (reason : Failure)
    (failed : (run left right base capacity used).result = .error reason) :
    run left right base capacity used = unchanged used (.error reason) :=
  resources_failure _ _ _ _ (run_resources left right base capacity used) reason failed

private theorem resources_no_badRepresentation (base capacity used : Nat) (outcome : Outcome NatOperand)
    (resources : Resources base capacity used outcome) : outcome.result ≠ .error .badRepresentation := by
  rcases resources with ⟨result, same, valid⟩ | ⟨reservation, words, positive, reserved, same⟩
  · simpa only [same, unchanged] using valid
  · simp [same, committed]

theorem runWord_no_badRepresentation (operand : NatOperand) (factor : BitVec 64)
    (base capacity used : Nat) :
    (runWord operand factor base capacity used).result ≠ .error .badRepresentation :=
  resources_no_badRepresentation _ _ _ _ (runWord_resources operand factor base capacity used)

theorem no_badRepresentation (left right : NatOperand) (base capacity used : Nat) :
    (run left right base capacity used).result ≠ .error .badRepresentation :=
  resources_no_badRepresentation _ _ _ _ (run_resources left right base capacity used)

private theorem resources_allocation (base capacity used : Nat) (outcome : Outcome NatOperand)
    (resources : Resources base capacity used outcome) (reservation : Arena.Reservation)
    (allocated : outcome.allocation = some reservation) :
    outcome = committed reservation outcome.written ∧ 0 < outcome.written.length ∧
      Arena.reserve base capacity used outcome.written.length = some reservation := by
  rcases resources with ⟨result, same, valid⟩ | ⟨actual, words, positive, reserved, same⟩
  · rw [same] at allocated
    cases allocated
  · rw [same] at allocated ⊢
    have equal : actual = reservation := Option.some.inj allocated
    subst actual
    exact ⟨rfl, positive, reserved⟩

/-- Exact reservation, entire scratch buffer, fromWords normalization, and cursor.
The branch equations above determine the exact written word count (2, n+1, n+m). -/
theorem allocation_exact (left right : NatOperand) (base capacity used : Nat)
    (reservation : Arena.Reservation)
    (allocated : (run left right base capacity used).allocation = some reservation) :
    run left right base capacity used = committed reservation (run left right base capacity used).written ∧
      0 < (run left right base capacity used).written.length ∧
      Arena.reserve base capacity used (run left right base capacity used).written.length = some reservation :=
  resources_allocation _ _ _ _ (run_resources left right base capacity used) reservation allocated

theorem runWord_allocation_exact (operand : NatOperand) (factor : BitVec 64) (base capacity used : Nat)
    (reservation : Arena.Reservation)
    (allocated : (runWord operand factor base capacity used).allocation = some reservation) :
    runWord operand factor base capacity used = committed reservation (runWord operand factor base capacity used).written ∧
      0 < (runWord operand factor base capacity used).written.length ∧
      Arena.reserve base capacity used (runWord operand factor base capacity used).written.length = some reservation :=
  resources_allocation _ _ _ _ (runWord_resources operand factor base capacity used) reservation allocated

private theorem resources_no_allocation (base capacity used : Nat) (outcome : Outcome NatOperand)
    (resources : Resources base capacity used outcome) (unallocated : outcome.allocation = none) :
    outcome.used = used ∧ outcome.written = [] := by
  rcases resources with ⟨result, same, valid⟩ | ⟨reservation, words, positive, reserved, same⟩
  · rw [same]
    exact ⟨rfl, rfl⟩
  · rw [same] at unallocated
    cases unallocated

theorem no_allocation_resources (left right : NatOperand) (base capacity used : Nat)
    (unallocated : (run left right base capacity used).allocation = none) :
    (run left right base capacity used).used = used ∧ (run left right base capacity used).written = [] :=
  resources_no_allocation _ _ _ _ (run_resources left right base capacity used) unallocated

theorem runWord_no_allocation_resources (operand : NatOperand) (factor : BitVec 64)
    (base capacity used : Nat) (unallocated : (runWord operand factor base capacity used).allocation = none) :
    (runWord operand factor base capacity used).used = used ∧
      (runWord operand factor base capacity used).written = [] :=
  resources_no_allocation _ _ _ _ (runWord_resources operand factor base capacity used) unallocated

/-- In the general branch the exact physical count and positive reservation
checks are both necessary and sufficient; there is no semantic size guard. -/
theorem large_success_iff (left right : NatOperand) (base capacity used : Nat)
    (hl : 1 < left.wordCount) (hr : 1 < right.wordCount) :
    (∃ result, (run left right base capacity used).result = .ok result) ↔
      left.wordCount + right.wordCount < B ∧
        Arena.Checks base capacity used (left.wordCount + right.wordCount) := by
  rw [run_large left right base capacity used hl hr]
  by_cases fits : left.wordCount + right.wordCount < B
  · simp only [fits, ↓reduceIte, true_and]
    cases reserved : Arena.reserve base capacity used (left.wordCount + right.wordCount) with
    | none =>
        have failed := (Arena.reserve_eq_none_iff_checks base capacity used
          (left.wordCount + right.wordCount) (by omega)).mp reserved
        simp [unchanged, failed]
    | some reservation =>
        have checks := ((Arena.reserve_eq_some_iff_checks base capacity used
          (left.wordCount + right.wordCount) (by omega) reservation).mp reserved).1
        simp [committed, checks]
  · simp [fits, unchanged]

theorem runWord_large_success_iff (operand : NatOperand) (factor : BitVec 64)
    (base capacity used : Nat) (nonzero : factor ≠ 0) (notone : factor ≠ 1)
    (large : 1 < operand.wordCount) :
    (∃ result, (runWord operand factor base capacity used).result = .ok result) ↔
      operand.wordCount + 1 < B ∧ Arena.Checks base capacity used (operand.wordCount + 1) := by
  rw [runWord_large operand factor base capacity used nonzero notone large]
  by_cases fits : operand.wordCount + 1 < B
  · simp only [fits, ↓reduceIte, true_and]
    cases reserved : Arena.reserve base capacity used (operand.wordCount + 1) with
    | none =>
        have failed := (Arena.reserve_eq_none_iff_checks base capacity used
          (operand.wordCount + 1) (by omega)).mp reserved
        simp [unchanged, failed]
    | some reservation =>
        have checks := ((Arena.reserve_eq_some_iff_checks base capacity used
          (operand.wordCount + 1) (by omega) reservation).mp reserved).1
        simp [committed, checks]
  · simp [fits, unchanged]

/-- The reservation geometry is exact even without Arena.Valid; committed
storage is never released by result normalization. -/
theorem allocation_geometry (left right : NatOperand) (base capacity used : Nat)
    (reservation : Arena.Reservation)
    (allocated : (run left right base capacity used).allocation = some reservation) :
    let count := (run left right base capacity used).written.length
    Arena.Checks base capacity used count ∧
      reservation.pointer = base + Arena.start base used ∧
      (run left right base capacity used).used = Arena.finish base used count := by
  obtain ⟨same, positive, reserved⟩ := allocation_exact left right base capacity used reservation allocated
  obtain ⟨checks, geometry⟩ := (Arena.reserve_eq_some_iff_checks base capacity used
    _ positive reservation).mp reserved
  have cursor := congrArg Outcome.used same
  dsimp only [committed] at cursor
  dsimp only
  exact ⟨checks, congrArg Arena.Reservation.pointer geometry,
    cursor.trans (congrArg Arena.Reservation.used geometry)⟩

end SszNative.NatMul
