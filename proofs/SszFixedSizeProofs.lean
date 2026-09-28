import SszFixedSizeClassification
import SszFixedSizeArithmetic

namespace SszNative.FixedSize

open Serialize (Outcome unchanged)

theorem measurePrimitive_spec (shape : Serialize.Desc) (arena : Delimited.ArenaState) :
    ResultSpec (measurePrimitive shape arena).result
      (fun result => result.map NatOperand.value = shape.erase.fixedSize) := by
  cases shape with
  | bitVector length =>
    simp only [measurePrimitive, Serialize.Desc.erase, Ssz.Desc.fixedSize]
    apply bind_spec _ _ _ _ (bitWidth_spec length arena)
    intro width used correct
    simpa only [unchanged, ResultSpec, Option.map] using congrArg some correct
  | _ => rfl

mutual
  /-- Every successful raw measurement has exactly the erased upstream value;
  a failed arithmetic helper can only report scratch exhaustion. -/
  theorem measureFixed_spec (desc : Codec.Desc) (arena : Delimited.ArenaState) :
      ResultSpec (measureFixed desc arena).result
        (fun result => result.map NatOperand.value = desc.erase.fixedSize) := by
    cases desc with
    | primitive shape => exact measurePrimitive_spec shape arena
    | vector element length =>
      simp only [measureFixed, Codec.Desc.erase, Ssz.Desc.fixedSize]
      apply bind_spec _ _ _ _ (measureFixed_spec element arena)
      intro measured used correct
      cases measured with
      | none =>
        simp only [Option.map] at correct
        simp only [unchanged, ResultSpec, ← correct, Option.map]
      | some width =>
        simp only [Option.map] at correct
        apply bind_spec _ _ _ _ (mul_spec width length { arena with used := used })
        intro total used value
        simpa only [unchanged, ResultSpec, Option.map, ← correct] using congrArg some value
    | container fields =>
      simpa only [measureFixed, Codec.Desc.erase, Ssz.Desc.fixedSize,
        small_zero_value, Nat.zero_add, Option.map_id'] using
        measureFields_spec fields (.small 0) arena
    | progressiveContainer active fields =>
      simpa only [measureFixed, Codec.Desc.erase, Ssz.Desc.fixedSize,
        small_zero_value, Nat.zero_add, Option.map_id'] using
        measureFields_spec fields (.small 0) arena
    | _ => rfl

  /-- Ordered accumulation is extensionally the upstream sum; the operand total
  remains native and may be borrowed, padded, or empty Large. -/
  theorem measureFields_spec (fields : List (String × Codec.Desc)) (total : NatOperand)
      (arena : Delimited.ArenaState) :
      ResultSpec (measureFields fields total arena).result (fun result =>
        result.map NatOperand.value =
          (Ssz.Desc.fieldsFixedSize (Codec.Desc.eraseFields fields)).map (total.value + ·)) := by
    cases fields with
    | nil => simp only [measureFields, unchanged, ResultSpec, Codec.Desc.eraseFields,
        Ssz.Desc.fieldsFixedSize, Option.map, Nat.add_zero]
    | cons field rest =>
      rcases field with ⟨name, shape⟩
      simp only [measureFields, Codec.Desc.eraseFields, Ssz.Desc.fieldsFixedSize]
      apply bind_spec _ _ _ _ (measureFixed_spec shape arena)
      intro measured used correct
      cases measured with
      | none =>
        simp only [Option.map] at correct
        simp only [unchanged, ResultSpec, ← correct, Option.map]
      | some width =>
        simp only [Option.map] at correct
        apply bind_spec _ _ _ _ (add_spec total width { arena with used := used })
        intro next used value
        apply ResultSpec.mono _ _ _ (measureFields_spec rest next { arena with used := used })
        intro measured remaining
        rw [remaining]
        rw [← correct]
        cases Ssz.Desc.fieldsFixedSize (Codec.Desc.eraseFields rest) <;>
          simp only [Option.map, value, Nat.add_assoc]
end

theorem fixedSize_spec (desc : Codec.Desc) (arena : Delimited.ArenaState) :
    ResultSpec (fixedSize desc arena).result
      (fun result => result.map NatOperand.value = desc.erase.fixedSize) := by
  cases classified : isFixed desc with
  | false =>
    rw [fixedSize_variable desc arena classified]
    exact ((isFixed_false_iff desc).1 classified).symm
  | true =>
    rw [fixedSize_fixed desc arena classified]
    exact measureFixed_spec desc arena

/-- Erasing any successful result yields the exact upstream option, with uint
width measured in bytes. No successful validation or canonicality is required. -/
theorem fixedSize_success (desc : Codec.Desc) (arena : Delimited.ArenaState)
    (result : Option NatOperand) (success : (fixedSize desc arena).result = .ok result) :
    result.map NatOperand.value = desc.erase.fixedSize := by
  have spec := fixedSize_spec desc arena
  simpa only [ResultSpec, success] using spec

theorem measureFixed_success (desc : Codec.Desc) (arena : Delimited.ArenaState)
    (result : Option NatOperand) (success : (measureFixed desc arena).result = .ok result) :
    result.map NatOperand.value = desc.erase.fixedSize := by
  have spec := measureFixed_spec desc arena
  simpa only [ResultSpec, success] using spec

theorem fixedSize_value (desc : Codec.Desc) (arena : Delimited.ArenaState)
    (width : NatOperand) (success : (fixedSize desc arena).result = .ok (some width)) :
    desc.erase.fixedSize = some width.value :=
  (fixedSize_success desc arena (some width) success).symm

/-- None is exactly structural variability, and its public result has no effects. -/
theorem fixedSize_none_iff (desc : Codec.Desc) (arena : Delimited.ArenaState) :
    (fixedSize desc arena).result = .ok none ↔ isFixed desc = false := by
  constructor
  · intro success
    apply (isFixed_false_iff desc).2
    exact (fixedSize_success desc arena none success).symm
  · intro notFixed
    rw [fixedSize_variable desc arena notFixed]
    rfl

theorem fixedSize_none_no_effects (desc : Codec.Desc) (arena : Delimited.ArenaState)
    (noneResult : (fixedSize desc arena).result = .ok none) :
    fixedSize desc arena = unchanged arena.used (.ok none) :=
  fixedSize_variable desc arena ((fixedSize_none_iff desc arena).1 noneResult)

theorem fixedSize_error (desc : Codec.Desc) (arena : Delimited.ArenaState)
    (reason : Serialize.Error) (failed : (fixedSize desc arena).result = .error reason) :
    reason = .arithmetic .scratchExhausted := by
  have spec := fixedSize_spec desc arena
  simpa only [ResultSpec, failed] using spec

theorem measureFixed_error (desc : Codec.Desc) (arena : Delimited.ArenaState)
    (reason : Serialize.Error) (failed : (measureFixed desc arena).result = .error reason) :
    reason = .arithmetic .scratchExhausted := by
  have spec := measureFixed_spec desc arena
  simpa only [ResultSpec, failed] using spec

theorem fixedSize_no_badRepresentation (desc : Codec.Desc) (arena : Delimited.ArenaState) :
    (fixedSize desc arena).result ≠ .error (.arithmetic .badRepresentation) := by
  intro failed
  have impossible := fixedSize_error desc arena _ failed
  cases impossible

/-- A raw None also means variability, but the converse is deliberately not
claimed: raw measurement may exhaust scratch before reaching a variable field. -/
theorem measureFixed_none_variable (desc : Codec.Desc) (arena : Delimited.ArenaState)
    (noneResult : (measureFixed desc arena).result = .ok none) :
    isFixed desc = false := by
  apply (isFixed_false_iff desc).2
  exact (measureFixed_success desc arena none noneResult).symm

/-- Complete public erasure alternative, keeping host resource failure separate
from the total upstream fixed-size option. -/
theorem fixedSize_refines (desc : Codec.Desc) (arena : Delimited.ArenaState) :
    (fixedSize desc arena).result.map (Option.map NatOperand.value) =
        .ok desc.erase.fixedSize ∨
      (fixedSize desc arena).result = .error (.arithmetic .scratchExhausted) := by
  cases result : (fixedSize desc arena).result with
  | ok width =>
    left
    simp only [Except.map]
    exact congrArg Except.ok (fixedSize_success desc arena width result)
  | error reason =>
    right
    rw [fixedSize_error desc arena reason result]

end SszNative.FixedSize
