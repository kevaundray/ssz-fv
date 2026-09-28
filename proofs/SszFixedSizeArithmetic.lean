import SszFixedSize

namespace SszNative.FixedSize

open Serialize (Outcome unchanged)

/-- A proof predicate, not a second execution or arena model: every successful
result satisfies the postcondition and the only possible error is exhaustion. -/
def ResultSpec {α : Type} (result : Except Serialize.Error α) (post : α → Prop) : Prop :=
  match result with
  | .ok value => post value
  | .error reason => reason = .arithmetic .scratchExhausted

theorem ResultSpec.mono {α : Type} (result : Except Serialize.Error α)
    (first second : α → Prop) (spec : ResultSpec result first)
    (implies : ∀ value, first value → second value) : ResultSpec result second := by
  cases result with
  | error reason => exact spec
  | ok value => exact implies value spec

theorem bind_spec {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (pre : α → Prop) (post : β → Prop) (firstSpec : ResultSpec first.result pre)
    (nextSpec : ∀ value used, pre value → ResultSpec (next value used).result post) :
    ResultSpec (Serialize.bind first next).result post := by
  cases result : first.result with
  | error reason =>
    simpa only [Serialize.bind, result, ResultSpec] using firstSpec
  | ok value =>
    have valid : pre value := by simpa only [ResultSpec, result] using firstSpec
    simpa only [Serialize.bind, result] using nextSpec value first.used valid

theorem unchanged_spec {α : Type} (used : Nat) (value : α) (post : α → Prop)
    (valid : post value) : ResultSpec (unchanged used (.ok value)).result post := valid

theorem arithmetic_spec (call : NatArithmetic.Outcome NatOperand)
    (post : NatOperand → Prop)
    (success : ∀ value, call.result = .ok value → post value)
    (notBad : call.result ≠ .error .badRepresentation) :
    ResultSpec (arithmetic call).result post := by
  cases result : call.result with
  | ok value =>
    simpa only [arithmetic, result, Except.mapError, ResultSpec] using success value result
  | error reason =>
    cases reason with
    | scratchExhausted => simp only [arithmetic, result, Except.mapError, ResultSpec]
    | badRepresentation => exact False.elim (notBad result)

theorem add_spec (left right : NatOperand) (arena : Delimited.ArenaState) :
    ResultSpec (add left right arena).result (fun result => result.value = left.value + right.value) :=
  arithmetic_spec _ _
    (NatAdd.run_value left right arena.base arena.capacity arena.used)
    (NatAdd.no_badRepresentation left right arena.base arena.capacity arena.used)

theorem mul_spec (left right : NatOperand) (arena : Delimited.ArenaState) :
    ResultSpec (mul left right arena).result (fun result => result.value = left.value * right.value) :=
  arithmetic_spec _ _
    (NatMul.run_value left right arena.base arena.capacity arena.used)
    (NatMul.no_badRepresentation left right arena.base arena.capacity arena.used)

/-- Divisor eight excludes badRepresentation without any operand invariant. -/
theorem div8_no_badRepresentation (length : NatOperand) (arena : Delimited.ArenaState) :
    (NatDivision.run length 8 arena.base arena.capacity arena.used).result ≠
      .error .badRepresentation := by
  intro bad
  have zero := (NatDivision.run_badRepresentation_iff length 8
    arena.base arena.capacity arena.used).1 bad
  exact (by decide : (8 : BitVec 64) ≠ 0) zero

theorem div8_spec (length : NatOperand) (arena : Delimited.ArenaState) :
    ResultSpec (div8 length arena).result (fun result =>
      result.1.value = length.value / 8 ∧ result.2.toNat = length.value % 8) := by
  cases result : (NatDivision.run length 8 arena.base arena.capacity arena.used).result with
  | error reason =>
    cases reason with
    | badRepresentation => exact False.elim (div8_no_badRepresentation length arena result)
    | scratchExhausted => simp only [div8, result, Except.mapError, ResultSpec]
  | ok divided =>
    have correct := NatDivision.run_success length 8 arena.base arena.capacity arena.used divided result
    simpa only [div8, result, Except.mapError, ResultSpec,
      show (8 : BitVec 64).toNat = 8 by decide] using And.intro correct.1 correct.2.1

theorem small_one_value : (NatOperand.small 1).value = 1 := rfl

theorem small_zero_value : (NatOperand.small 0).value = 0 := rfl

/-- Native quotient-plus-conditional-increment is upstream's exact ceil(n/8),
not a truncated machine-width computation. -/
theorem bitWidth_spec (length : NatOperand) (arena : Delimited.ArenaState) :
    ResultSpec (bitWidth length arena).result
      (fun result => result.value = (length.value + 7) / 8) := by
  unfold bitWidth
  apply bind_spec _ _ _ _ (div8_spec length arena)
  intro divided used correct
  by_cases zero : divided.2 = 0
  · simp only [zero, ↓reduceIte, unchanged, ResultSpec]
    have remainder : length.value % 8 = 0 := by
      simpa only [zero, show (0 : BitVec 64).toNat = 0 by decide] using correct.2.symm
    rw [correct.1]
    omega
  · simp only [zero, ↓reduceIte]
    apply ResultSpec.mono _ _ _ (add_spec divided.1 (.small 1) { arena with used := used })
    intro result value
    have nonzero : divided.2.toNat ≠ 0 := by
      intro equal
      apply zero
      apply BitVec.eq_of_toNat_eq
      simpa using equal
    rw [small_one_value, correct.1] at value
    have remainder := correct.2
    omega

end SszNative.FixedSize
