import SszArm.CodecMeasurePrimitiveStorage
import SszArm.CodecStorageLegacy

set_option autoImplicit false

namespace SszArm.Codec.Measure.Primitive

open SszNative (NatOperand)

private def ResultBacking (measured : SszNative.Serialize.Outcome NatOperand) : Prop :=
  ∀ size, measured.result = .ok size → Storage.Backing (fun _ _ => True) size

private theorem unchanged_backing (used : Nat) (size : NatOperand)
    (backing : Storage.Backing (fun _ _ => True) size) :
    ResultBacking (SszNative.Serialize.unchanged used (.ok size)) := by
  intro result success
  cases success
  exact backing

private theorem error_backing (used : Nat) (reason : SszNative.Serialize.Error) :
    ResultBacking (SszNative.Serialize.unchanged used (.error reason)) := by
  intro result success
  cases success

private theorem bind_backing {α : Type} (first : SszNative.Serialize.Outcome α)
    (next : α → Nat → SszNative.Serialize.Outcome NatOperand)
    (later : ∀ value used, ResultBacking (next value used)) :
    ResultBacking (SszNative.Serialize.bind first next) := by
  intro size success
  cases checked : first.result with
  | error reason => simp only [SszNative.Serialize.bind, checked] at success; cases success
  | ok value => exact later value first.used size
      (by simpa only [SszNative.Serialize.bind, checked] using success)

private theorem fromWords_backing (address : BitVec 64) (limbs : List (BitVec 64))
    (physical : 8 * limbs.length < 2^63) :
    Storage.Backing (fun _ _ => True) (NatOperand.fromWords address limbs) := by
  have bound : (SszNative.Limbs.trim limbs).length ≤ limbs.length := by
    rw [SszNative.Limbs.trim_length]
    exact SszNative.Limbs.sigWords_le_length limbs
  cases trimmed : SszNative.Limbs.trim limbs with
  | nil => simp only [NatOperand.fromWords, trimmed, Storage.Backing]
  | cons first rest =>
    cases rest with
    | nil => simp only [NatOperand.fromWords, trimmed, Storage.Backing]
    | cons second rest =>
      simp only [NatOperand.fromWords, trimmed, Storage.Backing]
      rw [trimmed] at bound
      exact ⟨by omega, trivial⟩

private theorem fromWide_backing (arena : SszNative.Delimited.ArenaState) (wide : BitVec 128) :
    ResultBacking (SszNative.Serialize.fromWide arena wide) := by
  intro size success
  unfold SszNative.Serialize.fromWide SszNative.NatArithmetic.fromWide at success
  split at success
  · cases success
    trivial
  · split at success
    · cases success
    · cases success
      apply fromWords_backing
      decide

private theorem measureList_backing (limit : Option NatOperand)
    (bits : SszNative.Serialize.Packed) (arena : SszNative.Delimited.ArenaState) :
    ResultBacking (SszNative.Serialize.measureList limit bits arena) := by
  unfold SszNative.Serialize.measureList
  apply bind_backing
  intro actual used
  apply bind_backing
  intro ignored nextUsed
  exact fromWide_backing _ _

/-- Primitive success either borrows the original Uint width or returns a small
count / at-most-two-limb constructor. Arbitrary width values are not narrowed. -/
theorem measure_backing (shape : SszNative.Serialize.Desc) (value : SszNative.Serialize.Value)
    (arena : SszNative.Delimited.ArenaState)
    (inputs : ∀ size ∈ Emit.descriptorOperands shape, Storage.Backing (fun _ _ => True) size)
    (size : NatOperand) (success : (SszNative.Serialize.measure shape value arena).result = .ok size) :
    Storage.Backing (fun _ _ => True) size := by
  have all : ResultBacking (SszNative.Serialize.measure shape value arena) := by
    cases shape with
    | uint width =>
      cases value with
      | uint number =>
        simp only [SszNative.Serialize.measure]
        split
        · exact unchanged_backing _ width (inputs width (by simp [Emit.descriptorOperands]))
        · exact error_backing _ _
      | _ => exact error_backing _ _
    | bool | byteVector _ | byteList _ | bitVector _ | bitList _ | progressiveBitList _ =>
      cases value <;> simp only [SszNative.Serialize.measure]
      all_goals first
        | exact error_backing _ _
        | exact unchanged_backing _ _ True.intro
        | exact measureList_backing _ _ _
        | (apply bind_backing; intro actual used; exact unchanged_backing _ _ True.intro)
        | (split
           · exact unchanged_backing _ _ True.intro
           · first
             | exact error_backing _ _
             | (apply bind_backing; intro actual used; exact error_backing _ _))
  exact all size success

/-- Descriptor storage retains the physical backing invariant under arbitrary
immutable aliasing. This is independent of the subsequent machine execution. -/
theorem descriptor_backing {writes s address shape}
    (input : Storage.DescOwned writes s address (.primitive shape))
    (size : NatOperand) (member : size ∈ Emit.descriptorOperands shape) :
    Storage.Backing (fun _ _ => True) size := by
  have stored := Storage.desc_at input
  cases shape with
  | bool => simp [Emit.descriptorOperands] at member
  | uint n | byteVector n | byteList n | bitVector n | bitList n =>
    simp only [Emit.descriptorOperands, List.mem_singleton] at member
    subst size
    exact stored.2.2.2.2.1
  | progressiveBitList limit =>
    cases limit with
    | none => simp [Emit.descriptorOperands] at member
    | some n =>
      simp only [Emit.descriptorOperands, List.mem_singleton] at member
      subst size
      exact stored.2.2.2.2.2.1

end SszArm.Codec.Measure.Primitive
