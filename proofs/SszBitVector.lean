import SszBitView
import SszDelimited
import SszNatAdd
import SszNatNarrow

set_option autoImplicit false

namespace SszNative.BitVector

/-- Scope errors retain the actual borrowed or allocated Nat representation. -/
inductive Error where
  | arithmetic (reason : NatArithmetic.Failure)
  | scope (expected : NatOperand) (actual : Nat)
  | paddingBits

/-- Both helper outcomes are retained, including every scratch write before a
later rejection. There is no rollback and no inferred canonical allocation. -/
structure Outcome where
  result : Except Error (BitVec 128)
  divided : NatArithmetic.Outcome (NatOperand × BitVec 64)
  rounded : Option (NatArithmetic.Outcome NatOperand)

def Outcome.used (outcome : Outcome) : Nat :=
  match outcome.rounded with
  | none => outcome.divided.used
  | some rounded => rounded.used

/-- Conversion and the inlined Bits::new guard. The ceiling is expressed in Nat,
not as a possibly overflowing 128-bit addition of seven. -/
def construct (length : NatOperand) (data : Ssz.Bytes) : Except Error (BitVec 128) :=
  match NatNarrow.toU128 length with
  | none => .error (.arithmetic .badRepresentation)
  | some count =>
    if data.size = (count.toNat + 7) / 8 then .ok count
    else .error (.arithmetic .badRepresentation)

/-- Exact scope precedes any tail read, padding rejection, or representation guard. -/
def finish (length expected : NatOperand) (remainder : BitVec 64)
    (data : Ssz.Bytes) : Except Error (BitVec 128) :=
  if NatNarrow.runExact expected (BitVec.ofNat 64 data.size) then
    if remainder ≠ 0 ∧ 0 < data.size then
      if data[data.size - 1]! >>> UInt8.ofNat remainder.toNat ≠ 0 then
        .error .paddingBits
      else construct length data
    else construct length data
  else .error (.scope expected data.size)

/-- Native order: divide/reserve, optional round/reserve, exact, padding, borrow.
A failed second helper retains the first helper's cursor and written words. -/
def run (length : NatOperand) (data : Ssz.Bytes) (arena : Delimited.ArenaState) : Outcome :=
  let divided := NatDivision.run length 8 arena.base arena.capacity arena.used
  match divided.result with
  | .error reason => ⟨.error (.arithmetic reason), divided, none⟩
  | .ok (quotient, remainder) =>
    if remainder = 0 then
      ⟨finish length quotient remainder data, divided, none⟩
    else
      let rounded := NatAdd.run quotient (.small 1) arena.base arena.capacity divided.used
      match rounded.result with
      | .error reason => ⟨.error (.arithmetic reason), divided, some rounded⟩
      | .ok expected => ⟨finish length expected remainder data, divided, some rounded⟩

/-- Materialization is only for comparison with pinned SSZ. Host failures remain
explicit outer errors, including BadRepresentation until proved unreachable. -/
def eraseResult (data : Ssz.Bytes) : Except Error (BitVec 128) →
    Except NatArithmetic.Failure (Except Ssz.Err Ssz.Value)
  | .ok count => .ok (.ok (.bits (Ssz.unpackBits data count.toNat)))
  | .error (.arithmetic reason) => .error reason
  | .error (.scope expected actual) => .ok (.error (.scope expected.value actual))
  | .error .paddingBits => .ok (.error .paddingBits)

def Outcome.erase (outcome : Outcome) (data : Ssz.Bytes) :
    Except NatArithmetic.Failure (Except Ssz.Err Ssz.Value) :=
  eraseResult data outcome.result

theorem construct_ok (length : NatOperand) (data : Ssz.Bytes)
    (physical : data.size < 2 ^ 64) (scope : data.size = (length.value + 7) / 8) :
    construct length data = .ok (BitVec.ofNat 128 length.value) := by
  have bound := BitView.vector_count_bound length.value data.size scope physical
  have wide : length.value < 2 ^ 128 := by omega
  have represented : (BitVec.ofNat 128 length.value).toNat = length.value :=
    Nat.mod_eq_of_lt wide
  have narrowed := (NatNarrow.toU128_some_iff length
    (BitVec.ofNat 128 length.value)).2 represented
  simp only [construct, narrowed, represented, scope, ↓reduceIte]

theorem finish_refines (length expected : NatOperand) (remainder : BitVec 64)
    (data : Ssz.Bytes) (physical : data.size < 2 ^ 64)
    (expectedValue : expected.value = (length.value + 7) / 8)
    (remainderValue : remainder.toNat = length.value % 8) :
    eraseResult data (finish length expected remainder data) =
      .ok (BitView.vectorOutcome length.value data) := by
  have actual : (BitVec.ofNat 64 data.size).toNat = data.size := Nat.mod_eq_of_lt physical
  have exactScope : NatNarrow.runExact expected (BitVec.ofNat 64 data.size) = true ↔
      data.size = (length.value + 7) / 8 := by
    rw [NatNarrow.runExact_iff, actual, expectedValue]
    exact eq_comm
  by_cases scope : data.size = (length.value + 7) / 8
  · have checked := exactScope.2 scope
    have built := construct_ok length data physical scope
    have bound := BitView.vector_count_bound length.value data.size scope physical
    have represented : (BitVec.ofNat 128 length.value).toNat = length.value :=
      Nat.mod_eq_of_lt (by omega)
    have zero : (remainder = 0) = (length.value % 8 = 0) := by
      apply propext
      constructor
      · intro h
        calc
          length.value % 8 = remainder.toNat := remainderValue.symm
          _ = 0 := by rw [h]; rfl
      · intro h
        apply BitVec.eq_of_toNat_eq
        change remainder.toNat = 0
        rw [remainderValue, h]
    rw [BitView.vectorOutcome]
    split
    · rw [finish, checked]
      simp only [↓reduceIte, ne_eq, zero, remainderValue]
      by_cases padding : length.value % 8 ≠ 0 ∧ 0 < data.size <;>
        by_cases tail : data[data.size - 1]! >>> UInt8.ofNat (length.value % 8) ≠ 0 <;>
        simp [padding, tail, built, eraseResult, represented]
    · contradiction
  · have checked : NatNarrow.runExact expected (BitVec.ofNat 64 data.size) = false := by
      cases h : NatNarrow.runExact expected (BitVec.ofNat 64 data.size)
      · rfl
      · exact False.elim (scope (exactScope.1 h))
    simp only [finish, checked, Bool.false_eq_true, ↓reduceIte, eraseResult,
      expectedValue, BitView.vectorOutcome, scope]

/-- Every non-resource result agrees with pinned SSZ; representation failures
cannot occur for a physical byte slice, even with an unbounded descriptor. -/
theorem run_refines (length : NatOperand) (data : Ssz.Bytes) (arena : Delimited.ArenaState)
    (physical : data.size < 2 ^ 64) :
    (run length data arena).erase data = .ok (Ssz.deserialize (.bitVector length.value) data) ∨
    (run length data arena).erase data = .error .scratchExhausted := by
  cases divided : (NatDivision.run length 8 arena.base arena.capacity arena.used).result with
  | error reason =>
    cases reason with
    | scratchExhausted =>
      right
      simp only [run, divided, Outcome.erase, eraseResult]
    | badRepresentation =>
      have impossible := (NatDivision.run_badRepresentation_iff length 8 arena.base
        arena.capacity arena.used).1 divided
      exact False.elim ((by decide : (8#64 : BitVec 64) ≠ 0) impossible)
  | ok pair =>
    rcases pair with ⟨quotient, remainder⟩
    have arithmetic := NatDivision.run_success length 8 arena.base arena.capacity arena.used
      (quotient, remainder) divided
    have quotientValue : quotient.value = length.value / 8 := arithmetic.1
    have remainderValue : remainder.toNat = length.value % 8 := arithmetic.2.1
    by_cases zero : remainder = 0
    · have modZero : length.value % 8 = 0 := by
        calc
          length.value % 8 = remainder.toNat := remainderValue.symm
          _ = 0 := by rw [zero]; rfl
      have expectedValue : quotient.value = (length.value + 7) / 8 := by
        rw [← BitView.rounded_byte_count]
        split <;> omega
      left
      simp only [run, divided, zero, ↓reduceIte, Outcome.erase]
      simpa only [zero, BitView.vector_outcome_eq_deserialize] using
        finish_refines length quotient remainder data physical expectedValue remainderValue
    · have modNonzero : length.value % 8 ≠ 0 := by
        intro h
        apply zero
        apply BitVec.eq_of_toNat_eq
        change remainder.toNat = 0
        rw [remainderValue, h]
      cases rounded : (NatAdd.run quotient (.small 1) arena.base arena.capacity
          (NatDivision.run length 8 arena.base arena.capacity arena.used).used).result with
      | error reason =>
        cases reason with
        | scratchExhausted =>
          right
          simp only [run, divided, zero, ↓reduceIte, rounded, Outcome.erase, eraseResult]
        | badRepresentation =>
          exact False.elim (NatAdd.no_badRepresentation quotient (.small 1) arena.base
            arena.capacity _ rounded)
      | ok expected =>
        have added := NatAdd.run_value quotient (.small 1) arena.base arena.capacity
          (NatDivision.run length 8 arena.base arena.capacity arena.used).used expected rounded
        have one : (NatOperand.small 1).value = 1 := by rfl
        rw [one, quotientValue] at added
        have expectedValue : expected.value = (length.value + 7) / 8 := by
          rw [← BitView.rounded_byte_count]
          split <;> omega
        left
        simp only [run, divided, zero, ↓reduceIte, rounded, Outcome.erase]
        rw [finish_refines length expected remainder data physical expectedValue remainderValue,
          BitView.vector_outcome_eq_deserialize]

/-- Exhaustion depends on the two actual helper reservations, before any data
scope/padding check. Their checked unsigned arithmetic is not replaced by a
capacity estimate or a successful-allocation hypothesis. -/
def Exhausted (length : NatOperand) (arena : Delimited.ArenaState) : Prop :=
  let divided := NatDivision.run length 8 arena.base arena.capacity arena.used
  match divided.result with
  | .error reason => reason = .scratchExhausted
  | .ok (quotient, remainder) =>
    remainder ≠ 0 ∧
      (NatAdd.run quotient (.small 1) arena.base arena.capacity divided.used).result =
        .error .scratchExhausted

private theorem construct_not_scratch (length : NatOperand) (data : Ssz.Bytes) :
    eraseResult data (construct length data) ≠ .error .scratchExhausted := by
  cases narrowed : NatNarrow.toU128 length with
  | none => simp only [construct, narrowed, eraseResult, ne_eq, Except.error.injEq]; decide
  | some count =>
    by_cases scope : data.size = (count.toNat + 7) / 8 <;>
      simp [construct, narrowed, scope, eraseResult]

private theorem finish_not_scratch (length expected : NatOperand) (remainder : BitVec 64)
    (data : Ssz.Bytes) :
    eraseResult data (finish length expected remainder data) ≠ .error .scratchExhausted := by
  unfold finish
  split
  · split
    · split
      · simp [eraseResult]
      · exact construct_not_scratch length data
    · exact construct_not_scratch length data
  · simp [eraseResult]

theorem run_scratch_iff (length : NatOperand) (data : Ssz.Bytes)
    (arena : Delimited.ArenaState) :
    (run length data arena).erase data = .error .scratchExhausted ↔ Exhausted length arena := by
  cases divided : (NatDivision.run length 8 arena.base arena.capacity arena.used).result with
  | error reason =>
    cases reason <;>
      simp only [run, divided, Outcome.erase, eraseResult, Exhausted] <;> simp
  | ok pair =>
    rcases pair with ⟨quotient, remainder⟩
    by_cases zero : remainder = 0
    · simp only [run, divided, zero, ↓reduceIte, Outcome.erase, Exhausted]
      simp [finish_not_scratch]
    · cases rounded : (NatAdd.run quotient (.small 1) arena.base arena.capacity
          (NatDivision.run length 8 arena.base arena.capacity arena.used).used).result with
      | error reason =>
        cases reason <;>
          simp only [run, divided, zero, ↓reduceIte, rounded, Outcome.erase, eraseResult,
            Exhausted] <;> simp <;> exact zero
      | ok expected =>
        simp only [run, divided, zero, ↓reduceIte, rounded, Outcome.erase, Exhausted]
        simp [finish_not_scratch]

/-- In particular, a failed rounding reservation cannot undo division's committed
cursor or lose its recorded quotient buffer. -/
theorem rounding_failure_no_rollback (length quotient : NatOperand) (remainder : BitVec 64)
    (data : Ssz.Bytes) (arena : Delimited.ArenaState) (reason : NatArithmetic.Failure)
    (divided : (NatDivision.run length 8 arena.base arena.capacity arena.used).result =
      .ok (quotient, remainder))
    (nonzero : remainder ≠ 0)
    (rounded : (NatAdd.run quotient (.small 1) arena.base arena.capacity
      (NatDivision.run length 8 arena.base arena.capacity arena.used).used).result = .error reason) :
    (run length data arena).divided = NatDivision.run length 8 arena.base arena.capacity arena.used ∧
    (run length data arena).used = (NatDivision.run length 8 arena.base arena.capacity arena.used).used := by
  have unchanged := NatAdd.failure_unchanged quotient (.small 1) arena.base arena.capacity
    (NatDivision.run length 8 arena.base arena.capacity arena.used).used reason rounded
  simp only [run, divided, nonzero, ↓reduceIte, Outcome.used, unchanged,
    NatArithmetic.unchanged, and_self]

/-- The expected byte length keeps its physical representation; only this
arithmetic relation is used to discharge the later construction guard. -/
def Expected (length expected : NatOperand) (remainder : BitVec 64) : Prop :=
  expected.value = (length.value + 7) / 8 ∧ remainder.toNat = length.value % 8

theorem expected_of_division (length quotient : NatOperand) (remainder : BitVec 64)
    (address capacity used : Nat)
    (divided : (SszNative.NatDivision.run length 8 address capacity used).result =
      .ok (quotient, remainder)) (zero : remainder = 0#64) :
    Expected length quotient remainder := by
  have result := SszNative.NatDivision.run_success length 8 address capacity used
    (quotient, remainder) divided
  have quotientValue : quotient.value = length.value / 8 := result.1
  have remainderValue : remainder.toNat = length.value % 8 := result.2.1
  have modZero : length.value % 8 = 0 := by
    rw [← remainderValue, zero]
    rfl
  refine ⟨?_, remainderValue⟩
  rw [← BitView.rounded_byte_count]
  simpa only [modZero, ↓reduceIte] using quotientValue

theorem expected_of_round (length quotient expected : NatOperand) (remainder : BitVec 64)
    (address capacity used : Nat)
    (divided : (SszNative.NatDivision.run length 8 address capacity used).result =
      .ok (quotient, remainder)) (nonzero : remainder ≠ 0#64)
    (rounded : (SszNative.NatAdd.run quotient (.small 1) address capacity
      (SszNative.NatDivision.run length 8 address capacity used).used).result = .ok expected) :
    Expected length expected remainder := by
  have result := SszNative.NatDivision.run_success length 8 address capacity used
    (quotient, remainder) divided
  have quotientValue : quotient.value = length.value / 8 := result.1
  have remainderValue : remainder.toNat = length.value % 8 := result.2.1
  have modNonzero : length.value % 8 ≠ 0 := by
    intro zero
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    change remainder.toNat = 0
    rw [remainderValue, zero]
  have added := SszNative.NatAdd.run_value quotient (.small 1) address capacity
    (SszNative.NatDivision.run length 8 address capacity used).used expected rounded
  change expected.value = quotient.value + 1 at added
  refine ⟨?_, remainderValue⟩
  rw [← BitView.rounded_byte_count]
  simpa only [modNonzero, ↓reduceIte] using
    added.trans (congrArg (· + 1) quotientValue)

theorem expected_remainder_bound {length expected : NatOperand} {remainder : BitVec 64}
    (arithmetic : Expected length expected remainder) : remainder.toNat < 8 := by
  rw [arithmetic.2]
  exact Nat.mod_lt _ (by decide)

/-- Exact's full-Nat success proves both the u128 Some branch and the final
Bits::new length guard. No descriptor canonicality or size bound is assumed. -/
theorem scope_narrows (length expected : NatOperand) (remainder actual : BitVec 64)
    (arithmetic : Expected length expected remainder)
    (scope : NatNarrow.runExact expected actual = true) :
    length.value < 2^67 ∧
    NatNarrow.toU128 length = some (BitVec.ofNat 128 length.value) ∧
    actual.toNat = ((BitVec.ofNat 128 length.value).toNat + 7) / 8 := by
  have equal : expected.value = actual.toNat := (NatNarrow.runExact_iff _ _).1 scope
  have size : actual.toNat = (length.value + 7) / 8 := equal.symm.trans arithmetic.1
  have bound := BitView.vector_count_bound length.value actual.toNat size actual.isLt
  have wide : length.value < 2^128 := by omega
  have represented : (BitVec.ofNat 128 length.value).toNat = length.value :=
    Nat.mod_eq_of_lt wide
  exact ⟨bound, (NatNarrow.toU128_some_iff _ _).2 represented, by simpa only [represented] using size⟩

end SszNative.BitVector
