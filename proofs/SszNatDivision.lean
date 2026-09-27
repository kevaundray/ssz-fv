import SszNatArithmetic
import SszLimbDivision

set_option autoImplicit false

namespace SszNative.NatDivision

open NatArithmetic

/-- The native `to_u128` branch is selected by the significant count, not by
an assumed bound on the input's logical value or its physical limb count. -/
def wideValue (operand : NatOperand) : BitVec 128 :=
  BitVec.ofNat 128 operand.value

def wideQuotient (operand : NatOperand) (divisor : BitVec 64) : BitVec 128 :=
  wideValue operand / divisor.setWidth 128

def wideRemainder (operand : NatOperand) (divisor : BitVec 64) : BitVec 64 :=
  (wideValue operand % divisor.setWidth 128).setWidth 64

/-- Exact algorithm/resource model of native `Nat::div_rem_small`. The wider
path reserves before copying or dividing limbs. Every allocated quotient word
is retained in `written`, even when the returned operand normalizes to Small.
This is not a claim about pointer accesses or ISA execution. -/
def run (operand : NatOperand) (divisor : BitVec 64)
    (base capacity used : Nat) : Outcome (NatOperand × BitVec 64) :=
  if divisor = 0 then
    unchanged used (.error .badRepresentation)
  else if divisor = 1 then
    unchanged used (.ok (operand.normalized, 0))
  else if operand.wordCount ≤ 2 then
    let quotient := fromWide base capacity used (wideQuotient operand divisor)
    { result := quotient.result.map (fun result => (result, wideRemainder operand divisor))
      used := quotient.used
      allocation := quotient.allocation
      written := quotient.written }
  else
    match Arena.reserve base capacity used operand.wordCount with
    | none => unchanged used (.error .scratchExhausted)
    | some reservation =>
        let divided := LimbDivision.divideWords divisor (Limbs.trim operand.words)
        { result := .ok (NatOperand.fromWords (BitVec.ofNat 64 reservation.pointer) divided.1,
            BitVec.ofNat 64 divided.2)
          used := reservation.used
          allocation := some reservation
          written := divided.1 }

/-- Arbitrarily many redundant high zeros do not invalidate the native fast path. -/
theorem value_lt_128 (operand : NatOperand) (count : operand.wordCount ≤ 2) :
    operand.value < 2 ^ 128 := by
  have bound := Limbs.value_lt (Limbs.trim operand.words)
  rw [Limbs.trim_value, Limbs.trim_length] at bound
  apply Nat.lt_of_lt_of_le bound
  apply Nat.pow_le_pow_right (by decide)
  change 64 * operand.wordCount ≤ 128
  omega

theorem wideValue_toNat (operand : NatOperand) (count : operand.wordCount ≤ 2) :
    (wideValue operand).toNat = operand.value := by
  exact Nat.mod_eq_of_lt (value_lt_128 operand count)

private theorem low_high_value (words : List (BitVec 64))
    (bound : Limbs.value words < 2 ^ 128) :
    Limbs.value words = (words[0]?.getD 0).toNat +
      2 ^ 64 * (words[1]?.getD 0).toNat := by
  cases words with
  | nil => rfl
  | cons low rest =>
    cases rest with
    | nil => simp [Limbs.value]
    | cons high rest =>
      have highZero : Limbs.value rest = 0 := by
        simp only [Limbs.value] at bound
        omega
      simp [Limbs.value, highZero]

/-- The exact shift/OR expression used by native `to_u128` agrees with the
bounded conversion, including zero extension and redundant high input zeros. -/
theorem wideValue_native (operand : NatOperand) (count : operand.wordCount ≤ 2) :
    wideValue operand =
      BitVec.or ((operand.words[0]?.getD 0).setWidth 128)
        (BitVec.shiftLeft ((operand.words[1]?.getD 0).setWidth 128) 64) := by
  let low := operand.words[0]?.getD 0
  let high := operand.words[1]?.getD 0
  have wordsValue : operand.value = low.toNat + 2 ^ 64 * high.toNat :=
    low_high_value operand.words (value_lt_128 operand count)
  have shiftBound : high.toNat <<< 64 < 2 ^ 128 := by
    rw [Nat.shiftLeft_eq]
    have bound := high.isLt
    omega
  apply BitVec.eq_of_toNat_eq
  change (wideValue operand).toNat =
    (BitVec.or (low.setWidth 128) (BitVec.shiftLeft (high.setWidth 128) 64)).toNat
  rw [wideValue_toNat operand count]
  change operand.value =
    ((low.setWidth 128 : BitVec 128) |||
      ((high.setWidth 128 : BitVec 128) <<< (64 : Nat))).toNat
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth_of_le (show 64 ≤ 128 by decide), Nat.mod_eq_of_lt shiftBound]
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt high.toNat]
  simpa only [Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm] using wordsValue

private theorem divisor_pos (divisor : BitVec 64) (nonzero : divisor ≠ 0) :
    0 < divisor.toNat := by
  have hn : divisor.toNat ≠ 0 := by
    intro zero
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using zero
  omega

theorem wideQuotient_toNat (operand : NatOperand) (divisor : BitVec 64)
    (count : operand.wordCount ≤ 2) :
    (wideQuotient operand divisor).toNat = operand.value / divisor.toNat := by
  simp only [wideQuotient, BitVec.toNat_udiv, wideValue_toNat operand count,
    BitVec.toNat_setWidth_of_le (show 64 ≤ 128 by decide)]

theorem wideRemainder_toNat (operand : NatOperand) (divisor : BitVec 64)
    (count : operand.wordCount ≤ 2) (nonzero : divisor ≠ 0) :
    (wideRemainder operand divisor).toNat = operand.value % divisor.toNat := by
  have bound := Nat.lt_trans (Nat.mod_lt operand.value (divisor_pos divisor nonzero)) divisor.isLt
  unfold wideRemainder
  rw [BitVec.toNat_setWidth, BitVec.toNat_umod, wideValue_toNat operand count,
    BitVec.toNat_setWidth_of_le (show 64 ≤ 128 by decide), Nat.mod_eq_of_lt bound]

/-- Zero is rejected before inspecting the operand or allocator. -/
theorem phase_zero (operand : NatOperand) (base capacity used : Nat) :
    run operand 0 base capacity used = unchanged used (.error .badRepresentation) := by
  simp only [run, ↓reduceIte]

/-- One borrows the normalized original operand; it does not allocate. -/
theorem phase_one (operand : NatOperand) (base capacity used : Nat) :
    run operand 1 base capacity used = unchanged used (.ok (operand.normalized, 0)) := by
  simp [run]

theorem phase_wide (operand : NatOperand) (divisor : BitVec 64) (base capacity used : Nat)
    (nonzero : divisor ≠ 0) (notone : divisor ≠ 1) (count : operand.wordCount ≤ 2) :
    run operand divisor base capacity used =
      let quotient := fromWide base capacity used (wideQuotient operand divisor)
      { result := quotient.result.map (fun result => (result, wideRemainder operand divisor))
        used := quotient.used
        allocation := quotient.allocation
        written := quotient.written } := by
  simp only [run, nonzero, notone, count, ↓reduceIte]

/-- Failed reservation performs neither the copy nor the division pass. -/
theorem phase_reserve_failure (operand : NatOperand) (divisor : BitVec 64)
    (base capacity used : Nat) (nonzero : divisor ≠ 0) (notone : divisor ≠ 1)
    (count : 2 < operand.wordCount)
    (failure : Arena.reserve base capacity used operand.wordCount = none) :
    run operand divisor base capacity used = unchanged used (.error .scratchExhausted) := by
  simp only [run, nonzero, notone, Nat.not_le.mpr count, ↓reduceIte, failure]

theorem phase_reserved (operand : NatOperand) (divisor : BitVec 64)
    (base capacity used : Nat) (nonzero : divisor ≠ 0) (notone : divisor ≠ 1)
    (count : 2 < operand.wordCount) (reservation : Arena.Reservation)
    (success : Arena.reserve base capacity used operand.wordCount = some reservation) :
    run operand divisor base capacity used =
      let divided := LimbDivision.divideWords divisor (Limbs.trim operand.words)
      { result := .ok (NatOperand.fromWords (BitVec.ofNat 64 reservation.pointer) divided.1,
            BitVec.ofNat 64 divided.2)
        used := reservation.used
        allocation := some reservation
        written := divided.1 } := by
  simp only [run, nonzero, notone, Nat.not_le.mpr count, ↓reduceIte, success]

/-- Successful output is the full natural quotient and remainder, not truncated
logical arithmetic. There is no canonical-input or input-value hypothesis. -/
theorem run_success (operand : NatOperand) (divisor : BitVec 64) (base capacity used : Nat)
    (result : NatOperand × BitVec 64)
    (success : (run operand divisor base capacity used).result = .ok result) :
    result.1.value = operand.value / divisor.toNat ∧
      result.2.toNat = operand.value % divisor.toNat ∧ result.2.toNat < divisor.toNat := by
  by_cases nonzero : divisor = 0
  · subst divisor
    simp only [phase_zero, unchanged] at success
    cases success
  · by_cases notone : divisor = 1
    · subst divisor
      simp only [phase_one, unchanged, Except.ok.injEq] at success
      subst result
      change operand.normalized.value = operand.value / 1 ∧
        0 = operand.value % 1 ∧ 0 < 1
      exact ⟨by simpa only [Nat.div_one] using NatOperand.normalized_value operand,
        (Nat.mod_one operand.value).symm, by decide⟩
    · by_cases count : operand.wordCount ≤ 2
      · rw [phase_wide operand divisor base capacity used nonzero notone count] at success
        dsimp only at success
        cases resultEq : (fromWide base capacity used (wideQuotient operand divisor)).result with
        | error failure => simp only [resultEq, Except.map] at success; cases success
        | ok quotient =>
          simp only [resultEq, Except.map, Except.ok.injEq] at success
          subst result
          have quotientValue := fromWide_value base capacity used
            (wideQuotient operand divisor) quotient resultEq
          rw [wideQuotient_toNat operand divisor count] at quotientValue
          exact ⟨quotientValue, wideRemainder_toNat operand divisor count nonzero,
            by rw [wideRemainder_toNat operand divisor count nonzero]
               exact Nat.mod_lt _ (divisor_pos divisor nonzero)⟩
      · cases reserved : Arena.reserve base capacity used operand.wordCount with
        | none =>
          rw [phase_reserve_failure operand divisor base capacity used nonzero notone
            (by omega) reserved] at success
          cases success
        | some reservation =>
          rw [phase_reserved operand divisor base capacity used nonzero notone
            (by omega) reservation reserved] at success
          simp only [Except.ok.injEq] at success
          subst result
          have correct := LimbDivision.divideWords_result divisor (Limbs.trim operand.words) nonzero
          have remBound := LimbDivision.divideWords_remainder_lt divisor
            (Limbs.trim operand.words) nonzero
          have castBound := Nat.lt_trans remBound divisor.isLt
          simp only [NatOperand.fromWords_value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt castBound]
          rw [Limbs.trim_value] at correct
          exact ⟨correct.1, correct.2, remBound⟩

/-- BadRepresentation is precisely the leading zero-divisor branch. -/
theorem run_badRepresentation_iff (operand : NatOperand) (divisor : BitVec 64)
    (base capacity used : Nat) :
    (run operand divisor base capacity used).result = .error .badRepresentation ↔ divisor = 0 := by
  by_cases zero : divisor = 0
  · subst divisor
    simp only [phase_zero, unchanged]
  · simp only [zero, iff_false]
    by_cases one : divisor = 1
    · subst divisor
      rw [phase_one]
      intro impossible
      cases impossible
    · by_cases count : operand.wordCount ≤ 2
      · rw [phase_wide operand divisor base capacity used zero one count]
        unfold fromWide
        split
        · simp only [unchanged, Except.map]
          intro impossible
          cases impossible
        · split
          · simp only [unchanged, Except.map]
            intro impossible
            cases impossible
          · simp only [committed, Except.map]
            intro impossible
            cases impossible
      · cases reserved : Arena.reserve base capacity used operand.wordCount with
        | none =>
          rw [phase_reserve_failure operand divisor base capacity used zero one (by omega) reserved]
          intro impossible
          cases impossible
        | some reservation =>
          rw [phase_reserved operand divisor base capacity used zero one (by omega) reservation reserved]
          intro impossible
          cases impossible

/-- Exact exhaustion condition, including every unsigned/isize reservation guard
through `Arena.reserve`. No capacity-below-2^63 assumption is used. -/
theorem run_scratchExhausted_iff (operand : NatOperand) (divisor : BitVec 64)
    (base capacity used : Nat) :
    (run operand divisor base capacity used).result = .error .scratchExhausted ↔
      divisor ≠ 0 ∧ divisor ≠ 1 ∧
        ((operand.wordCount ≤ 2 ∧ 2 ^ 64 ≤ operand.value / divisor.toNat ∧
            Arena.reserve base capacity used 2 = none) ∨
          (2 < operand.wordCount ∧ Arena.reserve base capacity used operand.wordCount = none)) := by
  by_cases zero : divisor = 0
  · subst divisor
    rw [phase_zero]
    simp [unchanged]
  · by_cases one : divisor = 1
    · subst divisor
      rw [phase_one]
      simp [unchanged]
    · simp only [Ne, zero, one, not_false_eq_true, true_and]
      by_cases count : operand.wordCount ≤ 2
      · rw [phase_wide operand divisor base capacity used zero one count]
        by_cases small : (wideQuotient operand divisor).toNat < 2 ^ 64
        · have smallNat : operand.value / divisor.toNat < 2 ^ 64 := by
            rwa [wideQuotient_toNat operand divisor count] at small
          simp [fromWide, small, unchanged, Except.map, count,
            Nat.not_lt.mpr count, Nat.not_le.mpr smallNat]
        · have largeNat : 2 ^ 64 ≤ operand.value / divisor.toNat := by
            rw [wideQuotient_toNat operand divisor count] at small
            omega
          cases reserved : Arena.reserve base capacity used 2 <;>
            simp [fromWide, small, reserved, unchanged, committed, Except.map,
              count, Nat.not_lt.mpr count, largeNat]
      · cases reserved : Arena.reserve base capacity used operand.wordCount with
        | none =>
          rw [phase_reserve_failure operand divisor base capacity used zero one (by omega) reserved]
          simp [unchanged, count, show 2 < operand.wordCount by omega]
        | some reservation =>
          rw [phase_reserved operand divisor base capacity used zero one (by omega) reservation reserved]
          simp [count]

/-- The reservation failures expand to the full unsigned-address, aligned-cursor,
capacity, and signed-payload checks, rather than a stronger arena invariant. -/
theorem run_scratchExhausted_iff_checks (operand : NatOperand) (divisor : BitVec 64)
    (base capacity used : Nat) :
    (run operand divisor base capacity used).result = .error .scratchExhausted ↔
      divisor ≠ 0 ∧ divisor ≠ 1 ∧
        ((operand.wordCount ≤ 2 ∧ 2 ^ 64 ≤ operand.value / divisor.toNat ∧
            ¬ Arena.Checks base capacity used 2) ∨
          (2 < operand.wordCount ∧ ¬ Arena.Checks base capacity used operand.wordCount)) := by
  rw [run_scratchExhausted_iff]
  constructor
  · rintro ⟨zero, one, small | large⟩
    · exact ⟨zero, one, Or.inl ⟨small.1, small.2.1,
        (Arena.reserve_eq_none_iff_checks base capacity used 2 (by decide)).1 small.2.2⟩⟩
    · exact ⟨zero, one, Or.inr ⟨large.1,
        (Arena.reserve_eq_none_iff_checks base capacity used operand.wordCount
          (by omega)).1 large.2⟩⟩
  · rintro ⟨zero, one, small | large⟩
    · exact ⟨zero, one, Or.inl ⟨small.1, small.2.1,
        (Arena.reserve_eq_none_iff_checks base capacity used 2 (by decide)).2 small.2.2⟩⟩
    · exact ⟨zero, one, Or.inr ⟨large.1,
        (Arena.reserve_eq_none_iff_checks base capacity used operand.wordCount
          (by omega)).2 large.2⟩⟩

/-- Allocation occurs only after the zero/one branches, and uses exactly two
words on the wide path or the significant input count on the long path. -/
theorem run_allocation_iff (operand : NatOperand) (divisor : BitVec 64)
    (base capacity used : Nat) (reservation : Arena.Reservation) :
    (run operand divisor base capacity used).allocation = some reservation ↔
      divisor ≠ 0 ∧ divisor ≠ 1 ∧
        ((operand.wordCount ≤ 2 ∧ 2 ^ 64 ≤ operand.value / divisor.toNat ∧
            Arena.reserve base capacity used 2 = some reservation) ∨
          (2 < operand.wordCount ∧
            Arena.reserve base capacity used operand.wordCount = some reservation)) := by
  by_cases zero : divisor = 0
  · subst divisor
    rw [phase_zero]
    simp [unchanged]
  · by_cases one : divisor = 1
    · subst divisor
      rw [phase_one]
      simp [unchanged]
    · simp only [Ne, zero, one, not_false_eq_true, true_and]
      by_cases count : operand.wordCount ≤ 2
      · rw [phase_wide operand divisor base capacity used zero one count]
        by_cases small : (wideQuotient operand divisor).toNat < 2 ^ 64
        · have smallNat : operand.value / divisor.toNat < 2 ^ 64 := by
            rwa [wideQuotient_toNat operand divisor count] at small
          simp [fromWide, small, unchanged, count,
            Nat.not_lt.mpr count, Nat.not_le.mpr smallNat]
        · have largeNat : 2 ^ 64 ≤ operand.value / divisor.toNat := by
            rw [wideQuotient_toNat operand divisor count] at small
            omega
          cases reserved : Arena.reserve base capacity used 2 <;>
            simp [fromWide, small, reserved, unchanged, committed,
              count, Nat.not_lt.mpr count, largeNat]
      · cases reserved : Arena.reserve base capacity used operand.wordCount with
        | none =>
          rw [phase_reserve_failure operand divisor base capacity used zero one (by omega) reserved]
          simp [unchanged, count]
        | some allocated =>
          rw [phase_reserved operand divisor base capacity used zero one (by omega) allocated reserved]
          simp [count, show 2 < operand.wordCount by omega]

/-- Failure returns no quotient/remainder pair, consumes no cursor, and writes
nothing. In particular a failed `fromWide` is not mapped to false success. -/
theorem failure_unchanged (operand : NatOperand) (divisor : BitVec 64)
    (base capacity used : Nat) (failure : Failure)
    (failed : (run operand divisor base capacity used).result = .error failure) :
    run operand divisor base capacity used = unchanged used (.error failure) := by
  by_cases zero : divisor = 0
  · subst divisor
    rw [phase_zero] at failed ⊢
    cases failed
    rfl
  · by_cases one : divisor = 1
    · subst divisor
      rw [phase_one] at failed
      cases failed
    · by_cases count : operand.wordCount ≤ 2
      · rw [phase_wide operand divisor base capacity used zero one count] at failed ⊢
        unfold fromWide at failed ⊢
        by_cases small : (wideQuotient operand divisor).toNat < 2 ^ 64
        · simp only [small, ↓reduceIte] at failed
          cases failed
        · simp only [small, ↓reduceIte] at failed ⊢
          cases reserved : Arena.reserve base capacity used 2
          · simp only [reserved, unchanged, Except.map] at failed ⊢
            cases failed
            rfl
          · simp only [reserved, committed, Except.map] at failed
            cases failed
      · cases reserved : Arena.reserve base capacity used operand.wordCount with
        | none =>
          rw [phase_reserve_failure operand divisor base capacity used zero one (by omega) reserved]
            at failed ⊢
          cases failed
          rfl
        | some reservation =>
          rw [phase_reserved operand divisor base capacity used zero one (by omega) reservation reserved]
            at failed
          cases failed

/-- Successful allocation preserves the exact reserved cursor and all written
positions, independently of normalization of the returned quotient. -/
theorem allocation_resources (operand : NatOperand) (divisor : BitVec 64)
    (base capacity used : Nat) (reservation : Arena.Reservation)
    (allocated : (run operand divisor base capacity used).allocation = some reservation) :
    (run operand divisor base capacity used).used = reservation.used ∧
      (run operand divisor base capacity used).written.length =
        (if operand.wordCount ≤ 2 then 2 else operand.wordCount) ∧
      Arena.Checks base capacity used (if operand.wordCount ≤ 2 then 2 else operand.wordCount) ∧
      reservation.pointer = base + Arena.start base used ∧
      reservation.used = Arena.finish base used (if operand.wordCount ≤ 2 then 2 else operand.wordCount) ∧
      ∃ result, (run operand divisor base capacity used).result = .ok result := by
  obtain ⟨zero, one, branches⟩ := (run_allocation_iff operand divisor base capacity used reservation).1 allocated
  rcases branches with ⟨count, largeNat, reserved⟩ | ⟨count, reserved⟩
  · have large : ¬ (wideQuotient operand divisor).toNat < 2 ^ 64 := by
      rw [wideQuotient_toNat operand divisor count]
      omega
    obtain ⟨checks, shape⟩ := (Arena.reserve_eq_some_iff_checks base capacity used 2
      (by decide) reservation).1 reserved
    rw [phase_wide operand divisor base capacity used zero one count]
    simp only [fromWide, large, ↓reduceIte, reserved, committed, Except.map, List.length_cons,
      List.length_nil, count]
    subst reservation
    exact ⟨by trivial, by trivial, checks, rfl, rfl, ⟨_, rfl⟩⟩
  · obtain ⟨checks, shape⟩ := (Arena.reserve_eq_some_iff_checks base capacity used operand.wordCount
      (by omega) reservation).1 reserved
    rw [phase_reserved operand divisor base capacity used zero one count reservation reserved]
    simp only [Nat.not_le.mpr count, ↓reduceIte, LimbDivision.divideWords_length,
      Limbs.trim_length]
    subst reservation
    exact ⟨by trivial, by trivial, checks, rfl, rfl, ⟨_, rfl⟩⟩

/-- Without allocation the original cursor and scratch contents are untouched. -/
theorem no_allocation_resources (operand : NatOperand) (divisor : BitVec 64)
    (base capacity used : Nat)
    (unallocated : (run operand divisor base capacity used).allocation = none) :
    (run operand divisor base capacity used).used = used ∧
      (run operand divisor base capacity used).written = [] := by
  by_cases zero : divisor = 0
  · subst divisor
    rw [phase_zero]
    exact ⟨rfl, rfl⟩
  · by_cases one : divisor = 1
    · subst divisor
      rw [phase_one]
      exact ⟨rfl, rfl⟩
    · by_cases count : operand.wordCount ≤ 2
      · rw [phase_wide operand divisor base capacity used zero one count] at unallocated ⊢
        unfold fromWide at unallocated ⊢
        by_cases small : (wideQuotient operand divisor).toNat < 2 ^ 64
        · simp only [small, ↓reduceIte]
          exact ⟨by trivial, by trivial⟩
        · simp only [small, ↓reduceIte] at unallocated ⊢
          cases reserved : Arena.reserve base capacity used 2
          · simp only [unchanged]
            exact ⟨by trivial, by trivial⟩
          · simp only [reserved, committed] at unallocated
            cases unallocated
      · cases reserved : Arena.reserve base capacity used operand.wordCount with
        | none =>
          rw [phase_reserve_failure operand divisor base capacity used zero one (by omega) reserved]
          exact ⟨rfl, rfl⟩
        | some reservation =>
          rw [phase_reserved operand divisor base capacity used zero one (by omega) reservation reserved]
            at unallocated
          cases unallocated

end SszNative.NatDivision
