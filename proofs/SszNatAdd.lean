import SszNatArithmetic
import SszLimbAdd

set_option autoImplicit false

/- Exact shared algorithm/resource model of native/src/nat.rs:233–253.
This is not an ISA execution or memory-separation theorem. Both original
representations may contain redundant high zeros, including an empty Large. -/
namespace SszNative.NatAdd

open NatArithmetic

local notation "B" => (2 ^ 64 : Nat)

/-- Native word(0), before normalization. -/
def lowWord (operand : NatOperand) : BitVec 64 := operand.words[0]?.getD 0

def count (left right : NatOperand) : Nat := max left.wordCount right.wordCount

def sumWide (left right : NatOperand) : BitVec 128 :=
  LimbAdd.wideSum (lowWord left) (lowWord right) 0

/-- All scratch writes, including the extra carry word, not the borrowed prefix.
This function is called only after the checked reservation succeeds. -/
def writtenWords (left right : NatOperand) : List (BitVec 64) :=
  (LimbAdd.loop (count left right + 1)
    (Limbs.trim left.words) (Limbs.trim right.words) 0).1

/-- Significant lengths are observed first. Zero branches borrow a normalized
input; the one-word branch uses from_u128. The large branch checks usize before
reserving, and performs the output loop only after reservation succeeds. -/
def run (left right : NatOperand) (base capacity used : Nat) : Outcome NatOperand :=
  let leftCount := left.wordCount
  let rightCount := right.wordCount
  if leftCount = 0 then
    unchanged used (.ok right.normalized)
  else if rightCount = 0 then
    unchanged used (.ok left.normalized)
  else if leftCount ≤ 1 ∧ rightCount ≤ 1 then
    fromWide base capacity used (sumWide left right)
  else
    let allocated := max leftCount rightCount + 1
    if allocated < B then
      match Arena.reserve base capacity used allocated with
      | none => unchanged used (.error .scratchExhausted)
      | some reservation => committed reservation (writtenWords left right)
    else
      unchanged used (.error .scratchExhausted)

/-- Trimming changes no zero-extended indexed observation, even beyond the
significant prefix or the original physical list. -/
theorem trim_word (words : List (BitVec 64)) (index : Nat) :
    (Limbs.trim words)[index]?.getD 0 = words[index]?.getD 0 := by
  induction words generalizing index with
  | nil => rfl
  | cons first rest ih =>
    by_cases empty : Limbs.trim rest = []
    · by_cases zero : first = 0
      · cases index <;> simp_all [Limbs.trim] <;> exact ih _
      · cases index <;> simp_all [Limbs.trim] <;> exact ih _
    · cases index <;> simp_all [Limbs.trim]

/-- Exact original-word correspondence for every loop phase. Consequently the
logical trimmed inputs introduce no canonical-input assumption. -/
theorem loop_trim_eq_native (width index : Nat) (left right : List (BitVec 64))
    (carry : Nat) :
    LimbAdd.loop width ((Limbs.trim left).drop index) ((Limbs.trim right).drop index) carry =
      LimbAdd.loop width (left.drop index) (right.drop index) carry := by
  induction width generalizing index carry with
  | zero => rfl
  | succ width ih =>
    simp only [LimbAdd.loop_indexed_succ, trim_word, ih]

theorem writtenWords_native_loop (left right : NatOperand) :
    writtenWords left right =
      (LimbAdd.loop (count left right + 1) left.words right.words 0).1 := by
  have same := loop_trim_eq_native (count left right + 1) 0 left.words right.words 0
  simpa only [List.drop_zero, writtenWords] using congrArg Prod.fst same

/-- The retained logical operands are exactly the native significant prefixes. -/
theorem trimmed_prefix (operand : NatOperand) :
    Limbs.trim operand.words = operand.words.take operand.wordCount :=
  Limbs.trim_eq_take operand.words

private theorem zero_value (operand : NatOperand) (zero : operand.wordCount = 0) :
    operand.value = 0 := by
  have length : (Limbs.trim operand.words).length = 0 := by
    rw [← NatOperand.wordCount_eq_trim_length, zero]
  exact (Limbs.trim_eq_nil_iff_value_zero operand.words).mp
    (List.eq_nil_of_length_eq_zero length)

/-- A one-word significant prefix agrees with the original word(0), including
zero and arbitrarily long zero-padded representations. -/
theorem lowWord_value (operand : NatOperand) (small : operand.wordCount ≤ 1) :
    (lowWord operand).toNat = operand.value := by
  have length : (Limbs.trim operand.words).length ≤ 1 := by
    rw [← NatOperand.wordCount_eq_trim_length]
    exact small
  have value := Limbs.trim_value operand.words
  have word := trim_word operand.words 0
  cases trimmed : Limbs.trim operand.words with
  | nil =>
    simp only [trimmed, List.getElem?_nil, Option.getD_none] at word
    have low : lowWord operand = 0 := by simpa [lowWord] using word.symm
    rw [low]
    change 0 = Limbs.value operand.words
    simpa only [trimmed, Limbs.value] using value
  | cons first rest =>
    cases rest with
    | nil =>
      have low : lowWord operand = first := by simpa [trimmed, lowWord] using word.symm
      rw [low]
      simpa only [trimmed, Limbs.value, Nat.mul_zero, Nat.add_zero,
        NatOperand.value] using value
    | cons second rest => simp only [trimmed, List.length_cons] at length; omega

theorem sumWide_value (left right : NatOperand)
    (leftSmall : left.wordCount ≤ 1) (rightSmall : right.wordCount ≤ 1) :
    (sumWide left right).toNat = left.value + right.value := by
  rw [sumWide, LimbAdd.wideSum_toNat _ _ 0 (by omega), Nat.add_zero,
    lowWord_value left leftSmall, lowWord_value right rightSmall]

theorem writtenWords_eq_add (left right : NatOperand) :
    writtenWords left right = LimbAdd.add (Limbs.trim left.words) (Limbs.trim right.words) := by
  simp only [writtenWords, count, NatOperand.wordCount_eq_trim_length, LimbAdd.add]

theorem writtenWords_length (left right : NatOperand) :
    (writtenWords left right).length = count left right + 1 :=
  LimbAdd.loop_length _ _ _ _

/-- Arithmetic conservation comes from the proved carry loop, not a value-level
replacement for native addition. The represented natural is unbounded. -/
theorem writtenWords_value (left right : NatOperand) :
    Limbs.value (writtenWords left right) = left.value + right.value := by
  rw [writtenWords_eq_add, LimbAdd.add_value, Limbs.trim_value, Limbs.trim_value]
  rfl

/-- The allocated extra word consumes the last carry; it is retained in the
written buffer even when zero. -/
theorem writtenWords_final_carry (left right : NatOperand) :
    (LimbAdd.loop (count left right + 1)
      (Limbs.trim left.words) (Limbs.trim right.words) 0).2 = 0 := by
  apply LimbAdd.loop_carry_eq_zero
  · simp only [Limbs.trim_length, count, NatOperand.wordCount]
    omega
  · simp only [Limbs.trim_length, count, NatOperand.wordCount]
    omega
  · omega

/- Executable phase equations expose branch order and the entire Outcome.
They distinguish the unchanged cursor/buffer from committed scratch storage. -/
theorem run_zero_left (left right : NatOperand) (base capacity used : Nat)
    (zero : left.wordCount = 0) :
    run left right base capacity used = unchanged used (.ok right.normalized) := by
  simp [run, zero]

theorem run_zero_right (left right : NatOperand) (base capacity used : Nat)
    (nonzero : left.wordCount ≠ 0) (zero : right.wordCount = 0) :
    run left right base capacity used = unchanged used (.ok left.normalized) := by
  simp [run, nonzero, zero]

theorem run_one_word (left right : NatOperand) (base capacity used : Nat)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (small : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1) :
    run left right base capacity used = fromWide base capacity used (sumWide left right) := by
  simp [run, leftNonzero, rightNonzero, small]

theorem run_small (left right : NatOperand) (base capacity used : Nat)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (small : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1)
    (fits : left.value + right.value < B) :
    run left right base capacity used =
      unchanged used (.ok (.small ((sumWide left right).setWidth 64))) := by
  rw [run_one_word left right base capacity used leftNonzero rightNonzero small]
  simp only [fromWide, sumWide_value left right small.1 small.2, fits, ↓reduceIte]

theorem run_small_overflow (left right : NatOperand) (base capacity used : Nat)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (small : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1)
    (overflow : B ≤ left.value + right.value) :
    run left right base capacity used =
      match Arena.reserve base capacity used 2 with
      | none => unchanged used (.error .scratchExhausted)
      | some reservation => committed reservation
          [(sumWide left right).setWidth 64, ((sumWide left right) >>> 64).setWidth 64] := by
  rw [run_one_word left right base capacity used leftNonzero rightNonzero small]
  simp only [fromWide, sumWide_value left right small.1 small.2,
    show ¬ left.value + right.value < B by omega, ↓reduceIte] <;> rfl

theorem run_large (left right : NatOperand) (base capacity used : Nat)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (large : ¬ (left.wordCount ≤ 1 ∧ right.wordCount ≤ 1)) :
    run left right base capacity used =
      if count left right + 1 < B then
        match Arena.reserve base capacity used (count left right + 1) with
        | none => unchanged used (.error .scratchExhausted)
        | some reservation => committed reservation (writtenWords left right)
      else unchanged used (.error .scratchExhausted) := by
  change (if left.wordCount = 0 then _ else _) = _
  simp only [leftNonzero, rightNonzero, large, ↓reduceIte] <;> rfl

theorem run_value (left right : NatOperand) (base capacity used : Nat)
    (result : NatOperand) (success : (run left right base capacity used).result = .ok result) :
    result.value = left.value + right.value := by
  by_cases hl : left.wordCount = 0
  · rw [run_zero_left left right base capacity used hl] at success
    cases success
    rw [NatOperand.normalized_value, zero_value left hl, Nat.zero_add]
  · by_cases hr : right.wordCount = 0
    · rw [run_zero_right left right base capacity used hl hr] at success
      cases success
      rw [NatOperand.normalized_value, zero_value right hr, Nat.add_zero]
    · by_cases hs : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1
      · rw [run_one_word left right base capacity used hl hr hs] at success
        exact (fromWide_value base capacity used _ result success).trans
          (sumWide_value left right hs.1 hs.2)
      · rw [run_large left right base capacity used hl hr hs] at success
        split at success
        · split at success
          · cases success
          · rename_i reservation reserved
            cases success
            exact (NatOperand.fromWords_value _ _).trans (writtenWords_value left right)
        · cases success

/-- All failure guards, with the checked-count guard before reserve. This uses
the exact unsigned Arena.reserve model, without Arena.Valid or a capacity bound. -/
theorem scratch_exhausted_iff (left right : NatOperand) (base capacity used : Nat) :
    (run left right base capacity used).result = .error .scratchExhausted ↔
      left.wordCount ≠ 0 ∧ right.wordCount ≠ 0 ∧
        if left.wordCount ≤ 1 ∧ right.wordCount ≤ 1 then
          B ≤ left.value + right.value ∧ Arena.reserve base capacity used 2 = none
        else
          B ≤ count left right + 1 ∨
            (count left right + 1 < B ∧
              Arena.reserve base capacity used (count left right + 1) = none) := by
  by_cases hl : left.wordCount = 0
  · simp [run, hl, unchanged]
  · by_cases hr : right.wordCount = 0
    · simp [run, hl, hr, unchanged]
    · by_cases hs : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1
      · rw [run_one_word left right base capacity used hl hr hs]
        simp only [Ne, hl, hr, hs, not_false_eq_true, true_and, ↓reduceIte]
        rw [fromWide, sumWide_value left right hs.1 hs.2]
        by_cases fits : left.value + right.value < B
        · simp [fits, unchanged, show ¬ B ≤ left.value + right.value by omega]
        · cases reserved : Arena.reserve base capacity used 2 <;>
            simp [fits, unchanged, committed, show B ≤ left.value + right.value by omega]
      · rw [run_large left right base capacity used hl hr hs]
        simp only [Ne, hl, hr, hs, not_false_eq_true, true_and, ↓reduceIte]
        by_cases fits : count left right + 1 < B
        · cases reserved : Arena.reserve base capacity used (count left right + 1) <;>
            simp [fits, unchanged, committed, show ¬ B ≤ count left right + 1 by omega]
        · simp [fits, unchanged, show B ≤ count left right + 1 by omega]

theorem no_badRepresentation (left right : NatOperand) (base capacity used : Nat) :
    (run left right base capacity used).result ≠ .error .badRepresentation := by
  dsimp only [run]
  split
  · simp [unchanged]
  · split
    · simp [unchanged]
    · split
      · unfold fromWide
        split
        · simp [unchanged]
        · split <;> simp [unchanged, committed]
      · split
        · split <;> simp [unchanged, committed]
        · simp [unchanged]

/-- Native addition never rolls back a committed reservation: every error is
before output initialization and leaves both allocation and writes absent. -/
theorem failure_unchanged (left right : NatOperand) (base capacity used : Nat)
    (failure : Failure) (failed : (run left right base capacity used).result = .error failure) :
    run left right base capacity used = unchanged used (.error failure) := by
  cases failure with
  | badRepresentation => exact False.elim (no_badRepresentation left right base capacity used failed)
  | scratchExhausted =>
    obtain ⟨hl, hr, guards⟩ := (scratch_exhausted_iff left right base capacity used).mp failed
    by_cases hs : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1
    · simp only [hs] at guards
      rw [run_small_overflow left right base capacity used hl hr hs guards.1, guards.2]
    · simp only [hs, ↓reduceIte] at guards
      rw [run_large left right base capacity used hl hr hs]
      rcases guards with overflow | ⟨fits, reserved⟩
      · simp only [show ¬ count left right + 1 < B by omega, ↓reduceIte]
      · simp only [fits, ↓reduceIte, reserved] <;> rfl

/-- Every committed allocation has exactly the returned reservation cursor,
complete written buffer, and normalized borrowed result. -/
theorem allocation_exact (left right : NatOperand) (base capacity used : Nat)
    (reservation : Arena.Reservation)
    (allocated : (run left right base capacity used).allocation = some reservation) :
    (run left right base capacity used).used = reservation.used ∧
      (run left right base capacity used).result =
        .ok (NatOperand.fromWords (BitVec.ofNat 64 reservation.pointer)
          (run left right base capacity used).written) ∧
      ((left.wordCount ≤ 1 ∧ right.wordCount ≤ 1 ∧
          B ≤ left.value + right.value ∧
          Arena.reserve base capacity used 2 = some reservation ∧
          (run left right base capacity used).written =
            [(sumWide left right).setWidth 64, ((sumWide left right) >>> 64).setWidth 64]) ∨
        (¬ (left.wordCount ≤ 1 ∧ right.wordCount ≤ 1) ∧
          count left right + 1 < B ∧
          Arena.reserve base capacity used (count left right + 1) = some reservation ∧
          (run left right base capacity used).written = writtenWords left right)) := by
  by_cases hl : left.wordCount = 0
  · rw [run_zero_left left right base capacity used hl] at allocated
    cases allocated
  · by_cases hr : right.wordCount = 0
    · rw [run_zero_right left right base capacity used hl hr] at allocated
      cases allocated
    · by_cases hs : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1
      · by_cases fits : left.value + right.value < B
        · rw [run_small left right base capacity used hl hr hs fits] at allocated
          cases allocated
        · have bound : B ≤ left.value + right.value := by omega
          have phase := run_small_overflow left right base capacity used hl hr hs bound
          cases reserved : Arena.reserve base capacity used 2 with
          | none =>
            rw [phase, reserved] at allocated
            cases allocated
          | some actual =>
            rw [phase, reserved] at allocated ⊢
            have same : actual = reservation := Option.some.inj allocated
            subst actual
            exact ⟨rfl, rfl, Or.inl ⟨hs.1, hs.2, bound, rfl, rfl⟩⟩
      · have phase := run_large left right base capacity used hl hr hs
        by_cases fits : count left right + 1 < B
        · cases reserved : Arena.reserve base capacity used (count left right + 1) with
          | none =>
            rw [phase] at allocated
            simp only [fits, ↓reduceIte, reserved] at allocated
            cases allocated
          | some actual =>
            have successful := phase
            simp only [fits, ↓reduceIte, reserved] at successful
            rw [successful] at allocated ⊢
            have same : actual = reservation := Option.some.inj allocated
            subst actual
            exact ⟨rfl, rfl, Or.inr ⟨hs, fits, rfl, rfl⟩⟩
        · rw [phase] at allocated
          simp only [fits, ↓reduceIte] at allocated
          cases allocated

/-- Successful reservation geometry, cursor consumption, and complete scratch
length. No older Arena.Valid capacity restriction is used. -/
theorem allocation_geometry (left right : NatOperand) (base capacity used : Nat)
    (reservation : Arena.Reservation)
    (allocated : (run left right base capacity used).allocation = some reservation) :
    let words := (run left right base capacity used).written.length
    Arena.Checks base capacity used words ∧
      reservation.pointer = base + Arena.start base used ∧
      (run left right base capacity used).used = Arena.finish base used words ∧
      words = (if left.wordCount ≤ 1 ∧ right.wordCount ≤ 1 then 2 else count left right + 1) := by
  obtain ⟨cursor, result, branches⟩ := allocation_exact left right base capacity used reservation allocated
  rcases branches with small | large
  · obtain ⟨hl, hr, overflow, reserved, written⟩ := small
    have geometry := (Arena.reserve_eq_some_iff_checks base capacity used 2 (by omega) reservation).mp reserved
    dsimp only
    rw [written]
    simp only [List.length_cons, List.length_nil]
    obtain ⟨checks, exactReservation⟩ := geometry
    rw [cursor, exactReservation]
    exact ⟨checks, rfl, rfl, by simp [hl, hr]⟩
  · obtain ⟨large, fits, reserved, written⟩ := large
    have geometry := (Arena.reserve_eq_some_iff_checks base capacity used (count left right + 1)
      (by omega) reservation).mp reserved
    dsimp only
    rw [written, writtenWords_length]
    obtain ⟨checks, exactReservation⟩ := geometry
    rw [cursor, exactReservation]
    exact ⟨checks, rfl, rfl, by simp [large]⟩

/-- Every allocation-free branch leaves the cursor and scratch bytes untouched,
whether it returns a borrowed normalized operand, a Small, or an error. -/
theorem no_allocation_resources (left right : NatOperand) (base capacity used : Nat)
    (unallocated : (run left right base capacity used).allocation = none) :
    (run left right base capacity used).used = used ∧
      (run left right base capacity used).written = [] := by
  by_cases hl : left.wordCount = 0
  · rw [run_zero_left left right base capacity used hl]
    exact ⟨rfl, rfl⟩
  · by_cases hr : right.wordCount = 0
    · rw [run_zero_right left right base capacity used hl hr]
      exact ⟨rfl, rfl⟩
    · by_cases hs : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1
      · by_cases fits : left.value + right.value < B
        · rw [run_small left right base capacity used hl hr hs fits]
          exact ⟨rfl, rfl⟩
        · have phase := run_small_overflow left right base capacity used hl hr hs (by omega)
          cases reserved : Arena.reserve base capacity used 2 with
          | none =>
            rw [phase, reserved]
            exact ⟨rfl, rfl⟩
          | some actual =>
            rw [phase, reserved] at unallocated
            cases unallocated
      · have phase := run_large left right base capacity used hl hr hs
        by_cases fits : count left right + 1 < B
        · cases reserved : Arena.reserve base capacity used (count left right + 1) with
          | none =>
            rw [phase]
            simp only [fits, ↓reduceIte, reserved]
            exact ⟨rfl, rfl⟩
          | some actual =>
            rw [phase] at unallocated
            simp only [fits, ↓reduceIte, reserved] at unallocated
            cases unallocated
        · rw [phase]
          simp only [fits, ↓reduceIte]
          exact ⟨rfl, rfl⟩

end SszNative.NatAdd
