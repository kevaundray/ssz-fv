import SszNatShift

set_option autoImplicit false

namespace SszNative.NatShift

open NatArithmetic

/-- A complete alternative for the actual outcome, retaining the exact output
limbs and original reservation, rather than assuming a later execution trace. -/
def Resources (base capacity used count : Nat) (generate : Nat → BitVec 64)
    (outcome : Outcome NatOperand) : Prop :=
  (outcome.allocation = none ∧ outcome.used = used ∧ outcome.written = []) ∨
  ∃ reservation, Arena.reserve base capacity used count = some reservation ∧
    outcome = large reservation (List.ofFn (fun i : Fin count => generate i.val))

private theorem unchanged_resources (base capacity used count : Nat)
    (generate : Nat → BitVec 64) (result : Except Failure NatOperand) :
    Resources base capacity used count generate (unchanged used result) :=
  Or.inl ⟨rfl, rfl, rfl⟩

theorem allocate_resources (base capacity used count : Nat) (generate : Nat → BitVec 64) :
    Resources base capacity used count generate (allocate base capacity used count generate) := by
  cases reserved : Arena.reserve base capacity used count with
  | none => exact Or.inl (by simp [allocate, reserved, unchanged])
  | some reservation => exact Or.inr ⟨reservation, reserved, by simp [allocate, reserved]⟩

theorem shl_resources (operand : NatOperand) (bits base capacity used : Nat) :
    Resources base capacity used (wordCount (bitLength operand + bits)) (leftWord operand bits)
      (shl operand bits base capacity used) := by
  unfold shl
  dsimp only
  split
  · exact unchanged_resources _ _ _ _ _ _
  · split
    · exact unchanged_resources _ _ _ _ _ _
    · split
      · split
        · exact unchanged_resources _ _ _ _ _ _
        · split
          · split
            · exact allocate_resources _ _ _ _ _
            · exact unchanged_resources _ _ _ _ _ _
          · exact unchanged_resources _ _ _ _ _ _
      · exact unchanged_resources _ _ _ _ _ _

theorem shr_resources (operand : NatOperand) (bits base capacity used : Nat) :
    Resources base capacity used (wordCount (bitLength operand - bits)) (shiftedWord operand bits)
      (shr operand bits base capacity used) := by
  unfold shr
  dsimp only
  split
  · exact unchanged_resources _ _ _ _ _ _
  · split
    · exact unchanged_resources _ _ _ _ _ _
    · split
      · exact unchanged_resources _ _ _ _ _ _
      · exact allocate_resources _ _ _ _ _

theorem Resources.no_allocation (base capacity used count : Nat)
    (generate : Nat → BitVec 64) (outcome : Outcome NatOperand)
    (resources : Resources base capacity used count generate outcome)
    (unallocated : outcome.allocation = none) :
    outcome.used = used ∧ outcome.written = [] := by
  rcases resources with uncommitted | ⟨reservation, _, exactOutcome⟩
  · exact uncommitted.2
  · rw [exactOutcome] at unallocated
    cases unallocated

theorem Resources.allocation_exact (base capacity used count : Nat)
    (generate : Nat → BitVec 64) (outcome : Outcome NatOperand)
    (resources : Resources base capacity used count generate outcome)
    (reservation : Arena.Reservation) (allocated : outcome.allocation = some reservation) :
    Arena.reserve base capacity used count = some reservation ∧
      outcome.used = reservation.used ∧
      outcome.result = .ok (.large (BitVec.ofNat 64 reservation.pointer) outcome.written) ∧
      outcome.written = List.ofFn (fun i : Fin count => generate i.val) := by
  rcases resources with uncommitted | ⟨actual, reserved, exactOutcome⟩
  · rw [uncommitted.1] at allocated
    cases allocated
  · rw [exactOutcome] at allocated ⊢
    have same : actual = reservation := Option.some.inj allocated
    subst actual
    exact ⟨reserved, rfl, rfl, rfl⟩

theorem Resources.failure_unchanged (base capacity used count : Nat)
    (generate : Nat → BitVec 64) (outcome : Outcome NatOperand)
    (resources : Resources base capacity used count generate outcome)
    (failure : Failure) (failed : outcome.result = .error failure) :
    outcome = unchanged used (.error failure) := by
  rcases resources with ⟨unallocated, cursor, written⟩ | ⟨reservation, _, exactOutcome⟩
  · cases outcome
    simp_all [unchanged]
  · rw [exactOutcome] at failed
    cases failed

theorem Resources.cursor (base capacity used count : Nat)
    (generate : Nat → BitVec 64) (outcome : Outcome NatOperand)
    (resources : Resources base capacity used count generate outcome)
    (positive : 0 < count) : used ≤ outcome.used := by
  rcases resources with uncommitted | ⟨reservation, reserved, exactOutcome⟩
  · rw [uncommitted.2.1]
    exact Nat.le_refl used
  · obtain ⟨_, exactReservation⟩ :=
      (Arena.reserve_eq_some_iff_checks base capacity used count positive reservation).mp reserved
    rw [exactOutcome, exactReservation]
    change used ≤ Arena.finish base used count
    have := Arena.used_le_start base used
    unfold Arena.finish
    omega

theorem Resources.cursor_bounds (base capacity used count : Nat)
    (generate : Nat → BitVec 64) (outcome : Outcome NatOperand)
    (resources : Resources base capacity used count generate outcome)
    (positive : 0 < count) (valid : Arena.Valid base capacity used) :
    used ≤ outcome.used ∧ outcome.used ≤ capacity := by
  refine ⟨resources.cursor _ _ _ _ _ _ positive, ?_⟩
  rcases resources with uncommitted | ⟨reservation, reserved, exactOutcome⟩
  · rw [uncommitted.2.1]
    exact valid.2.2.2
  · rw [exactOutcome]
    exact (Arena.valid_after_success base capacity used count valid reservation reserved).2.2.2

theorem shl_no_allocation_resources (operand : NatOperand) (bits base capacity used : Nat)
    (unallocated : (shl operand bits base capacity used).allocation = none) :
    (shl operand bits base capacity used).used = used ∧
      (shl operand bits base capacity used).written = [] :=
  Resources.no_allocation _ _ _ _ _ _ (shl_resources operand bits base capacity used) unallocated

theorem shr_no_allocation_resources (operand : NatOperand) (bits base capacity used : Nat)
    (unallocated : (shr operand bits base capacity used).allocation = none) :
    (shr operand bits base capacity used).used = used ∧
      (shr operand bits base capacity used).written = [] :=
  Resources.no_allocation _ _ _ _ _ _ (shr_resources operand bits base capacity used) unallocated

theorem shl_failure_unchanged (operand : NatOperand) (bits base capacity used : Nat)
    (failure : Failure) (failed : (shl operand bits base capacity used).result = .error failure) :
    shl operand bits base capacity used = unchanged used (.error failure) :=
  Resources.failure_unchanged _ _ _ _ _ _ (shl_resources operand bits base capacity used) failure failed

theorem shr_failure_unchanged (operand : NatOperand) (bits base capacity used : Nat)
    (failure : Failure) (failed : (shr operand bits base capacity used).result = .error failure) :
    shr operand bits base capacity used = unchanged used (.error failure) :=
  Resources.failure_unchanged _ _ _ _ _ _ (shr_resources operand bits base capacity used) failure failed

theorem shl_cursor (operand : NatOperand) (bits base capacity used : Nat) :
    used ≤ (shl operand bits base capacity used).used :=
  Resources.cursor _ _ _ _ _ _ (shl_resources operand bits base capacity used) (by unfold wordCount; omega)

theorem shr_cursor (operand : NatOperand) (bits base capacity used : Nat) :
    used ≤ (shr operand bits base capacity used).used :=
  Resources.cursor _ _ _ _ _ _ (shr_resources operand bits base capacity used) (by unfold wordCount; omega)

theorem shl_cursor_bounds (operand : NatOperand) (bits base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (shl operand bits base capacity used).used ∧
      (shl operand bits base capacity used).used ≤ capacity :=
  Resources.cursor_bounds _ _ _ _ _ _ (shl_resources operand bits base capacity used)
    (by unfold wordCount; omega) valid

theorem shr_cursor_bounds (operand : NatOperand) (bits base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (shr operand bits base capacity used).used ∧
      (shr operand bits base capacity used).used ≤ capacity :=
  Resources.cursor_bounds _ _ _ _ _ _ (shr_resources operand bits base capacity used)
    (by unfold wordCount; omega) valid

/-- Exact completed initialized prefixes of the actual output buffer. -/
theorem Resources.initialized_prefix (base capacity used count : Nat)
    (generate : Nat → BitVec 64) (outcome : Outcome NatOperand)
    (resources : Resources base capacity used count generate outcome)
    (reservation : Arena.Reservation) (allocated : outcome.allocation = some reservation)
    (initialized : Nat) :
    (outcome.written.take initialized).length = min initialized count ∧
      ∀ index, index < min initialized count →
        (outcome.written.take initialized)[index]? = some (generate index) := by
  obtain ⟨_, _, _, written⟩ := resources.allocation_exact _ _ _ _ _ _ reservation allocated
  rw [written]
  constructor
  · simp
  · intro index bound
    have inside : index < count := by omega
    have before : index < initialized := by omega
    simp [before, inside]

/-- The output allocation is disjoint from the complete pre-call used prefix.
This is an address/initialized-buffer frame theorem, not a machine execution
claim: every recorded store belongs to the newly reserved interval. -/
theorem Resources.frame (base capacity used count : Nat)
    (generate : Nat → BitVec 64) (outcome : Outcome NatOperand)
    (resources : Resources base capacity used count generate outcome)
    (positive : 0 < count) (valid : Arena.Valid base capacity used)
    (reservation : Arena.Reservation) (allocated : outcome.allocation = some reservation) :
    outcome.written.length = count ∧
      reservation.pointer % 8 = 0 ∧
      base + used ≤ reservation.pointer ∧
      reservation.pointer + 8 * count = base + outcome.used ∧
      reservation.pointer + 8 * count ≤ base + capacity ∧
      ∀ index, index < outcome.written.length →
        base + used ≤ reservation.pointer + 8 * index ∧
        reservation.pointer + 8 * index + 8 ≤ base + outcome.used := by
  obtain ⟨reserved, cursor, _, written⟩ :=
    resources.allocation_exact _ _ _ _ _ _ reservation allocated
  have geometry := Arena.success_properties base capacity used count valid positive reservation reserved
  rw [written, List.length_ofFn, cursor]
  obtain ⟨aligned, _, _, _, _, starts, finishes, fits, _⟩ := geometry
  refine ⟨rfl, aligned, starts, finishes, fits, ?_⟩
  intro index bound
  omega

private theorem normalized_physical (operand : NatOperand)
    (physical : operand.words.length < 2^64) : operand.normalized.words.length < 2^64 := by
  have retained : (Limbs.trim operand.words).length < 2^64 := by
    rw [Limbs.trim_length]
    exact Nat.lt_of_le_of_lt (Limbs.sigWords_le_length operand.words) physical
  cases trimmed : Limbs.trim operand.words with
  | nil =>
    unfold NatOperand.normalized NatOperand.fromWords
    rw [trimmed]
    change 1 < 2^64
    decide
  | cons first rest =>
    cases rest with
    | nil =>
      unfold NatOperand.normalized NatOperand.fromWords
      rw [trimmed]
      change 1 < 2^64
      decide
    | cons second rest =>
      unfold NatOperand.normalized NatOperand.fromWords
      rw [trimmed]
      rw [trimmed] at retained
      exact retained

theorem allocate_physical (base capacity used count : Nat) (generate : Nat → BitVec 64)
    (result : NatOperand)
    (success : (allocate base capacity used count generate).result = .ok result) :
    result.words.length < 2^64 := by
  unfold allocate at success
  split at success
  · cases success
  · rename_i reservation reserved
    cases success
    change (List.ofFn (fun i : Fin count => generate i.val)).length < 2^64
    rw [List.length_ofFn]
    by_cases zero : count = 0
    · simp [zero]
    · have checks := ((Arena.reserve_eq_some_iff_checks base capacity used count
        (by omega) reservation).mp reserved).1
      unfold Arena.Checks at checks
      omega

theorem shl_physical (operand : NatOperand) (bits base capacity used : Nat)
    (result : NatOperand) (physical : operand.words.length < 2^64)
    (success : (shl operand bits base capacity used).result = .ok result) :
    result.words.length < 2^64 := by
  unfold shl at success
  dsimp only at success
  split at success
  · cases success
    simp [NatOperand.words]
  · split at success
    · cases success
      exact normalized_physical operand physical
    · split at success
      · split at success
        · cases success
          simp [NatOperand.words]
        · split at success
          · split at success
            · exact allocate_physical _ _ _ _ _ result success
            · cases success
          · cases success
      · cases success

theorem shr_physical (operand : NatOperand) (bits base capacity used : Nat)
    (result : NatOperand) (physical : operand.words.length < 2^64)
    (success : (shr operand bits base capacity used).result = .ok result) :
    result.words.length < 2^64 := by
  unfold shr at success
  dsimp only at success
  split at success
  · cases success
    simp [NatOperand.words]
  · split at success
    · cases success
      exact normalized_physical operand physical
    · split at success
      · cases success
        simp [NatOperand.words]
      · exact allocate_physical _ _ _ _ _ result success

theorem allocate_error (base capacity used count : Nat) (generate : Nat → BitVec 64)
    (failure : Failure)
    (failed : (allocate base capacity used count generate).result = .error failure) :
    failure = .scratchExhausted := by
  unfold allocate at failed
  split at failed
  · cases failed
    rfl
  · cases failed

theorem shl_error (operand : NatOperand) (bits base capacity used : Nat)
    (failure : Failure) (failed : (shl operand bits base capacity used).result = .error failure) :
    failure = .scratchExhausted := by
  unfold shl at failed
  dsimp only at failed
  split at failed
  · cases failed
  · split at failed
    · cases failed
    · split at failed
      · split at failed
        · cases failed
        · split at failed
          · split at failed
            · exact allocate_error _ _ _ _ _ failure failed
            · cases failed
              rfl
          · cases failed
            rfl
      · cases failed
        rfl

theorem shr_error (operand : NatOperand) (bits base capacity used : Nat)
    (failure : Failure) (failed : (shr operand bits base capacity used).result = .error failure) :
    failure = .scratchExhausted := by
  unfold shr at failed
  dsimp only at failed
  split at failed
  · cases failed
  · split at failed
    · cases failed
    · split at failed
      · cases failed
      · exact allocate_error _ _ _ _ _ failure failed

end SszNative.NatShift
