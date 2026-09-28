import SszArm.SerializeOwnershipMeasure
import SszArm.MeasureHelpersAllocation

namespace SszArm.Serialize

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Outcome Error)
open Delimited (Span Protected)

/-- The result can borrow original limbs or fresh constructor limbs. Both error
payload operands remain protected, including after a retained first allocation. -/
def ResultOperandsOwned (writes : List Span) : Except Error NatOperand → Prop
  | .ok operand => NatDivision.OperandOwned writes operand
  | .error reason => NatDivision.OperandOwned writes (Measure.errorOperands reason).1 ∧
      NatDivision.OperandOwned writes (Measure.errorOperands reason).2

theorem free_protected_after {writes : List Span} (arena : SszNative.Delimited.ArenaState)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (cursor : Nat) (monotone : arena.used ≤ cursor) :
    Protected writes (arena.base + cursor) (arena.capacity - cursor) := by
  by_cases available : cursor < arena.capacity
  · apply protected_subspan_of_bounds free <;> omega
  · left
    omega

theorem fromWide_operands_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (wide : BitVec 128) (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used)) :
    ResultOperandsOwned writes (SszNative.Serialize.fromWide arena wide).result := by
  cases result : (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used wide).result with
  | ok operand =>
    simpa only [SszNative.Serialize.fromWide, result, Except.mapError, ResultOperandsOwned] using
      Measure.Helpers.fromWide_result_owned writes arena wide storage free operand result
  | error reason =>
    simp only [SszNative.Serialize.fromWide, result, Except.mapError, ResultOperandsOwned,
      Measure.errorOperands, NatDivision.OperandOwned, and_self]

theorem measureList_operands_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (cap : Option NatOperand) (bits : SszNative.Serialize.Packed)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (capOwned : ∀ operand, cap = some operand → NatDivision.OperandOwned writes operand) :
    ResultOperandsOwned writes (SszNative.Serialize.measureList cap bits arena).result := by
  have firstOwned := fromWide_operands_owned writes arena bits.count storage free
  have monotone := (Measure.resource_fromWide arena bits.count).monotone
  have nextFree := free_protected_after arena free (SszNative.Serialize.fromWide arena bits.count).used monotone
  cases first : (SszNative.Serialize.fromWide arena bits.count).result with
  | error reason =>
    simpa only [SszNative.Serialize.measureList, SszNative.Serialize.bind, first] using
      (show ResultOperandsOwned writes (.error reason) from by simpa only [first] using firstOwned)
  | ok actual =>
    have actualOwned : NatDivision.OperandOwned writes actual := by
      simpa only [first, ResultOperandsOwned] using firstOwned
    have nextOwned := fromWide_operands_owned writes
      { arena with used := (SszNative.Serialize.fromWide arena bits.count).used }
      (BitVec.ofNat 128 (bits.count.toNat / 8 + 1)) storage nextFree
    cases cap with
    | none =>
      simpa only [SszNative.Serialize.measureList, SszNative.Serialize.bind, first,
        SszNative.Serialize.bounded, SszNative.Serialize.unchanged] using nextOwned
    | some operand =>
      by_cases fitting : actual.value ≤ operand.value
      · simpa only [SszNative.Serialize.measureList, SszNative.Serialize.bind, first,
          SszNative.Serialize.bounded, fitting, ↓reduceIte, SszNative.Serialize.unchanged] using nextOwned
      · simpa only [SszNative.Serialize.measureList, SszNative.Serialize.bind, first,
          SszNative.Serialize.bounded, fitting, ↓reduceIte, SszNative.Serialize.unchanged,
          ResultOperandsOwned, Measure.errorOperands] using
          (show NatDivision.OperandOwned writes operand ∧ NatDivision.OperandOwned writes actual from
            ⟨capOwned operand rfl, actualOwned⟩)

theorem measure_operands_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (desc : Desc) (value : Value) (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (inputs : ∀ operand ∈ Emit.descriptorOperands desc, NatDivision.OperandOwned writes operand) :
    ResultOperandsOwned writes (SszNative.Serialize.measure desc value arena).result := by
  cases desc with
  | bool =>
    cases value <;> simp [SszNative.Serialize.measure, SszNative.Serialize.unchanged,
      SszNative.Serialize.count, ResultOperandsOwned, Measure.errorOperands, NatDivision.OperandOwned]
  | uint operand =>
    cases value with
    | uint number =>
      by_cases fitting : SszNative.Serialize.uintFits operand number
      · simpa only [SszNative.Serialize.measure, fitting, ↓reduceIte, SszNative.Serialize.unchanged,
          ResultOperandsOwned] using inputs operand (by simp [Emit.descriptorOperands])
      · simp [SszNative.Serialize.measure, fitting, SszNative.Serialize.unchanged,
          ResultOperandsOwned, Measure.errorOperands, NatDivision.OperandOwned]
    | _ => exact ⟨trivial, trivial⟩
  | byteVector operand =>
    cases value with
    | bytes bytes =>
      by_cases fitting : operand.value = bytes.size
      · simp [SszNative.Serialize.measure, fitting, SszNative.Serialize.unchanged,
          ResultOperandsOwned, SszNative.Serialize.count, NatDivision.OperandOwned]
      · exact (by
          simpa only [SszNative.Serialize.measure, fitting, ↓reduceIte, SszNative.Serialize.unchanged,
            ResultOperandsOwned, Measure.errorOperands] using
            (show NatDivision.OperandOwned writes operand ∧
              NatDivision.OperandOwned writes (SszNative.Serialize.count bytes.size) from
              ⟨inputs operand (by simp [Emit.descriptorOperands]), trivial⟩))
    | _ => exact ⟨trivial, trivial⟩
  | byteList operand =>
    cases value with
    | bytes bytes =>
      by_cases fitting : (SszNative.Serialize.count bytes.size).value ≤ operand.value
      · simp only [SszNative.Serialize.measure, SszNative.Serialize.bind, SszNative.Serialize.bounded,
          fitting, ↓reduceIte, SszNative.Serialize.unchanged, ResultOperandsOwned]
        trivial
      · simpa only [SszNative.Serialize.measure, SszNative.Serialize.bind, SszNative.Serialize.bounded,
          fitting, ↓reduceIte, SszNative.Serialize.unchanged, ResultOperandsOwned, Measure.errorOperands] using
          (show NatDivision.OperandOwned writes operand ∧
            NatDivision.OperandOwned writes (SszNative.Serialize.count bytes.size) from
            ⟨inputs operand (by simp [Emit.descriptorOperands]), trivial⟩)
    | _ => exact ⟨trivial, trivial⟩
  | bitVector operand =>
    cases value with
    | bits bits =>
      by_cases fitting : operand.value = bits.count.toNat
      · simp [SszNative.Serialize.measure, fitting, SszNative.Serialize.unchanged,
          ResultOperandsOwned, SszNative.Serialize.count, NatDivision.OperandOwned]
      · have firstOwned := fromWide_operands_owned writes arena bits.count storage free
        cases first : (SszNative.Serialize.fromWide arena bits.count).result with
        | error reason =>
          simpa only [SszNative.Serialize.measure, fitting, ↓reduceIte, SszNative.Serialize.bind, first] using
            (show ResultOperandsOwned writes (.error reason) from by simpa only [first] using firstOwned)
        | ok actual =>
          have actualOwned : NatDivision.OperandOwned writes actual := by
            simpa only [first, ResultOperandsOwned] using firstOwned
          simpa only [SszNative.Serialize.measure, fitting, ↓reduceIte, SszNative.Serialize.bind,
            first, SszNative.Serialize.unchanged, ResultOperandsOwned, Measure.errorOperands] using
            (show NatDivision.OperandOwned writes operand ∧ NatDivision.OperandOwned writes actual from
              ⟨inputs operand (by simp [Emit.descriptorOperands]), actualOwned⟩)
    | _ => exact ⟨trivial, trivial⟩
  | bitList operand =>
    cases value with
    | bits bits =>
      exact measureList_operands_owned writes arena (some operand) bits storage free (by
        intro selected same
        have equal : operand = selected := Option.some.inj same
        subst selected
        exact inputs operand (by simp [Emit.descriptorOperands]))
    | _ => exact ⟨trivial, trivial⟩
  | progressiveBitList cap =>
    cases value with
    | bits bits =>
      exact measureList_operands_owned writes arena cap bits storage free (by
        intro operand same
        subst cap
        exact inputs operand (by simp [Emit.descriptorOperands]))
    | _ => exact ⟨trivial, trivial⟩

theorem Owned.measured_operands {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) :
    ResultOperandsOwned (stackSpans args ++ externalSpans args) (measured s args desc value).result := by
  apply measure_operands_owned _ _ _ _ owned.storageBound
  · exact protected_of_covers owned.freeOwned
      (Covers.of_subset (fun span member => List.mem_append.mpr (Or.inl member)))
  · intro operand member
    apply operand_owned_of_covers _ operand
      (owned.operandOwned operand (List.mem_append.mpr (Or.inl member)))
    exact Covers.of_subset (fun span inWrites => List.mem_append.mpr (Or.inl inWrites))

theorem Owned.measured_result_owned {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (operand : NatOperand)
    (success : (measured s args desc value).result = .ok operand) :
    NatDivision.OperandOwned (stackSpans args ++ externalSpans args) operand := by
  simpa only [success, ResultOperandsOwned] using owned.measured_operands

theorem Owned.measured_error_owned {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (reason : Error)
    (failure : (measured s args desc value).result = .error reason) :
    NatDivision.OperandOwned (stackSpans args ++ externalSpans args) (Measure.errorOperands reason).1 ∧
    NatDivision.OperandOwned (stackSpans args ++ externalSpans args) (Measure.errorOperands reason).2 := by
  simpa only [failure, ResultOperandsOwned] using owned.measured_operands

end SszArm.Serialize
