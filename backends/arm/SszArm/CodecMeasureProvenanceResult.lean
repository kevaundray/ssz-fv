import SszArm.CodecMeasureProvenanceCore
import SszArm.CodecStorageLegacy
import SszCodecMeasureResources

namespace SszArm.Codec.Measure.Provenance

open SszNative (NatOperand)
open SszNative.Codec (Desc Value Error)
open SszNative.CodecMeasure
open Delimited (Span Protected)

 def ErrorOwned (writes : List Span) (reason : Error) : Prop :=
  NatDivision.OperandOwned writes (errorOperands reason).1 ∧
    NatDivision.OperandOwned writes (errorOperands reason).2

 def ResultOwned {α : Type} (writes : List Span) (property : α → Prop) : Except Error α → Prop
  | .ok value => property value
  | .error reason => ErrorOwned writes reason

 theorem bind_owned {α β : Type} {writes : List Span} (property : α → Prop) (post : β → Prop)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (input : ResultOwned writes property first.result)
    (continued : ∀ value, property value → ResultOwned writes post (next value first.used).result) :
    ResultOwned writes post (bind first next).result := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using input
  | ok value =>
      simpa only [bind, result] using
        continued value (by simpa only [result, ResultOwned] using input)

 theorem unchanged_owned {α : Type} {writes : List Span} (property : α → Prop)
    (value : α) (used : Nat) (input : property value) :
    ResultOwned writes property (unchanged used (.ok value)).result := input

 theorem arithmetic_error_owned (writes : List Span) (reason : SszNative.NatArithmetic.Failure) :
    ErrorOwned writes (.primitive (.arithmetic reason)) := ⟨True.intro, True.intro⟩

 theorem add_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (left right : NatOperand) (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (leftOwned : NatDivision.OperandOwned writes left)
    (rightOwned : NatDivision.OperandOwned writes right) :
    ResultOwned writes (NatDivision.OperandOwned writes) (add left right arena).result := by
  cases result : (SszNative.NatAdd.run left right arena.base arena.capacity arena.used).result with
  | error reason =>
      simpa only [add, result, Except.mapError, ResultOwned] using arithmetic_error_owned writes reason
  | ok number =>
      simpa only [add, result, Except.mapError, ResultOwned] using
        add_result_owned writes arena left right number storage free leftOwned rightOwned result

 theorem primitive_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (shape : SszNative.Serialize.Desc) (logical : Value)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (inputs : ∀ operand ∈ Emit.descriptorOperands shape, NatDivision.OperandOwned writes operand) :
    ResultOwned writes (Storage.PlanBackingsProtected writes) (primitive shape logical arena).result := by
  have owned := Serialize.measure_operands_owned writes arena shape logical.toPrimitive storage free inputs
  cases result : (SszNative.Serialize.measure shape logical.toPrimitive arena).result with
  | error reason =>
      simpa only [primitive, result, Except.map, Except.mapError, ResultOwned, ErrorOwned,
        errorOperands, Serialize.ResultOperandsOwned] using owned
  | ok number =>
      simpa only [primitive, result, Except.map, Except.mapError, ResultOwned] using
        (show Storage.PlanBackingsProtected writes (Plan.leaf number) from
          ⟨by simpa only [result, Serialize.ResultOperandsOwned] using owned, True.intro⟩)

 theorem exactCount_owned (writes : List Span) (expected : NatOperand) (actual used : Nat)
    (input : NatDivision.OperandOwned writes expected) :
    ResultOwned writes (fun _ => True) (exactCount expected actual used).result := by
  unfold exactCount
  split
  · trivial
  · exact ⟨input, True.intro⟩

 theorem bounded_owned (writes : List Span) (limit : Option NatOperand) (actual : NatOperand)
    (used : Nat) (actualOwned : NatDivision.OperandOwned writes actual)
    (limitOwned : ∀ number, limit = some number → NatDivision.OperandOwned writes number) :
    ResultOwned writes (fun _ => True) (bounded limit actual used).result := by
  cases limit with
  | none => trivial
  | some number =>
      unfold bounded SszNative.Serialize.bounded
      split
      · trivial
      · exact ⟨limitOwned number rfl, actualOwned⟩

 theorem hostSize_owned (writes : List Span) (number : NatOperand) (used : Nat) :
    ResultOwned writes (fun _ => True) (hostSize number used).result := by
  unfold hostSize SszNative.Serialize.hostSize
  split <;> trivial

 theorem compositeSize_owned (writes : List Span) (number : NatOperand) (used : Nat)
    (input : NatDivision.OperandOwned writes number) :
    ResultOwned writes (fun _ => True) (compositeSize number used).result := by
  unfold compositeSize
  split
  · exact ⟨input, True.intro⟩
  · trivial

 theorem reservePlans_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (count : Nat) (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used)) :
    ResultOwned writes (fun allocation => Protected writes allocation.pointer (40 * count))
      (reservePlans count arena).result := by
  cases reserved : SszNative.Arena.reserve arena.base arena.capacity arena.used (5 * count) with
  | none =>
      simpa only [reservePlans, reserved, ResultOwned] using arithmetic_error_owned writes .scratchExhausted
  | some allocation =>
      simp only [reservePlans, reserved, ResultOwned]
      by_cases empty : count = 0
      · subst count
        exact Or.inl (by omega)
      · obtain ⟨checks, rfl⟩ :=
          (SszNative.Arena.reserve_eq_some_iff_checks arena.base arena.capacity arena.used (5 * count)
            (by omega) allocation).mp reserved
        have low := SszNative.Arena.used_le_start arena.base arena.used
        have high := checks.2.2.2.2.2
        apply Serialize.protected_subspan_of_bounds free
        · omega
        · dsimp [SszNative.Arena.finish] at high
          omega

end SszArm.Codec.Measure.Provenance
