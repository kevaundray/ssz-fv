import SszCodecMeasure
import SszSerializeMeasure

set_option autoImplicit false

namespace SszNative.CodecMeasure

open Codec (Desc Value Error)

/-- Semantic agreement includes semantic rejection. The only alternatives are
actual host failures in the returned result, never assumed scratch availability. -/
def Refines {α β : Type} (project : α → β) (result : Except Error α)
    (expected : Except Ssz.Err β) : Prop :=
  Codec.eraseResult (result.map project) = .ok expected ∨
    result = .error (.primitive (.arithmetic .scratchExhausted)) ∨
    result = .error (.primitive .outputTooSmall)

theorem refines_unchanged {α β : Type} (project : α → β) (value : α) (used : Nat) :
    Refines project (unchanged used (.ok value)).result (.ok (project value)) :=
  Or.inl rfl

theorem refines_bind {α β γ δ : Type} (project : α → β) (projectNext : γ → δ)
    (first : Outcome α) (next : α → Nat → Outcome γ)
    (expected : Except Ssz.Err β) (expectedNext : β → Except Ssz.Err δ)
    (firstCorrect : Refines project first.result expected)
    (nextCorrect : ∀ value used, Refines projectNext (next value used).result
      (expectedNext (project value))) :
    Refines projectNext (bind first next).result (expected.bind expectedNext) := by
  rcases firstCorrect with correct | scratch | output
  · cases result : first.result with
    | ok value =>
      have same : expected = .ok (project value) := by
        simpa only [result, Except.map, Codec.eraseResult, Except.ok.injEq] using correct.symm
      simpa only [bind, result, same, Except.bind] using nextCorrect value first.used
    | error reason =>
      cases reason with
      | primitive reason =>
        cases reason with
        | wrongType | scope _ _ | limit _ _ =>
          left
          simp only [result, Except.map, Codec.eraseResult, Serialize.eraseResult,
            Except.ok.injEq] at correct
          simp only [bind, result, Except.map, Codec.eraseResult,
            Serialize.eraseResult, ← correct, Except.bind]
        | arithmetic fault =>
          simp only [result, Except.map, Codec.eraseResult, Serialize.eraseResult] at correct
          cases correct
        | outputTooSmall =>
          simp only [result, Except.map, Codec.eraseResult, Serialize.eraseResult] at correct
          cases correct
      | offsetOverflow _ | unknownSelector _ | scopeTooSmall _ _
      | scopeUndivided _ _ | scopeWidthless | firstOffset _ _
      | offsetUnordered | offsetPastScope | offsetUnaligned | offsetBelowTable
      | truncated | notABit _ | paddingBits | emptyEncoding | noDelimiter
      | trailingZeros | noSelector =>
        left
        simp only [result, Except.map, Codec.eraseResult, Except.ok.injEq] at correct
        simp only [bind, result, Except.map, Codec.eraseResult, ← correct, Except.bind]
  · right; left
    simp only [bind, scratch]
  · right; right
    simp only [bind, output]

theorem primitive_refines (shape : Serialize.Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) :
    Refines (fun plan => plan.size.value) (primitive shape value arena).result
      (Serialize.expectedSize shape value.toPrimitive) := by
  rcases Serialize.measure_refines shape value.toPrimitive arena
      (Value.physical_toPrimitive value physical) with correct | scratch
  · left
    cases result : (Serialize.measure shape value.toPrimitive arena).result with
    | ok size =>
      simpa only [primitive, result, Except.map, Except.mapError, Codec.eraseResult,
        Serialize.eraseResult, Plan.leaf, Plan.size] using correct
    | error reason =>
      simpa only [primitive, result, Except.map, Except.mapError, Codec.eraseResult] using correct
  · right; left
    simp only [primitive, scratch, Except.map, Except.mapError]

theorem add_refines (left right : NatOperand) (arena : Delimited.ArenaState) :
    Refines NatOperand.value (add left right arena).result (.ok (left.value + right.value)) := by
  cases result : (NatAdd.run left right arena.base arena.capacity arena.used).result with
  | ok value =>
    left
    simp only [add, result, Except.mapError, Except.map, Codec.eraseResult,
      NatAdd.run_value left right arena.base arena.capacity arena.used value result]
  | error reason =>
    cases reason with
    | scratchExhausted =>
      right; left
      simp only [add, result, Except.mapError]
    | badRepresentation =>
      exact False.elim (NatAdd.no_badRepresentation left right arena.base arena.capacity arena.used result)

theorem reservePlans_refines (count : Nat) (arena : Delimited.ArenaState) :
    Refines (fun _ => ()) (reservePlans count arena).result (.ok ()) := by
  cases reserved : Arena.reserve arena.base arena.capacity arena.used (5 * count) with
  | none =>
    right; left
    simp only [reservePlans, reserved]
  | some reservation =>
    left
    simp only [reservePlans, reserved, Except.map, Codec.eraseResult]

theorem writePlan_refines (allocation : Option Arena.Reservation) (index : Nat)
    (plan : Plan) (used : Nat) :
    Refines (fun _ => ()) (writePlan allocation index plan used).result (.ok ()) := by
  cases allocation <;> exact Or.inl rfl

theorem exact_refines (expected : NatOperand) (actual used : Nat)
    (physical : actual < 2 ^ 64) :
    Refines (fun _ => ()) (exactCount expected actual used).result
      (if expected.value = actual then .ok () else .error (.scope expected.value actual)) := by
  unfold exactCount
  split <;> left <;>
    simp only [unchanged, Except.map, Codec.eraseResult, Serialize.eraseResult,
      Serialize.count_value actual physical]

theorem bounded_refines (limit : Option NatOperand) (actual : NatOperand) (used : Nat) :
    Refines (fun _ => ()) (bounded limit actual used).result
      (Ssz.boundCheck (limit.map NatOperand.value) actual.value) := by
  cases limit with
  | none => exact Or.inl rfl
  | some limit =>
    by_cases fits : actual.value ≤ limit.value <;> left <;>
      simp only [bounded, Serialize.bounded, Option.map, Ssz.boundCheck, fits,
        ↓reduceIte, Serialize.unchanged, Except.mapError, Except.map,
        Codec.eraseResult, Serialize.eraseResult]

theorem hostSize_refines (size : NatOperand) (used : Nat) :
    Refines id (hostSize size used).result (.ok size.value) := by
  unfold hostSize Serialize.hostSize
  split
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

theorem compositeSize_refines (size : NatOperand) (used : Nat) :
    Refines (fun _ => ()) (compositeSize size used).result
      (if 2 ^ 32 ≤ size.value then .error (.offsetOverflow size.value) else .ok ()) := by
  unfold compositeSize
  split <;> exact Or.inl rfl

end SszNative.CodecMeasure
