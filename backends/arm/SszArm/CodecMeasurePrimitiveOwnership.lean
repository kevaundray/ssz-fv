import SszArm.CodecMeasurePrimitiveGeometry

set_option autoImplicit false

namespace SszArm.Codec.Measure

open SszNative.Codec (Value)
open Delimited (Protected)
open Serialize (Covers protected_of_covers protected_subspan_of_bounds)

/-- The immutable primitive provider is invoked using only projections of the
recursive original-state ownership, never an assumed successful measurement. -/
theorem Owned.primitive {s : ArmState} {args : Args} {shape : SszNative.Serialize.Desc}
    {value : Value} (owned : Owned s args (.primitive shape) value) :
    SszArm.Measure.Owned s args shape value.toPrimitive := by
  have low : 288 ≤ args.stack.toNat := owned.stackLow
  have covered := Primitive.writes_covered s args shape value low
  have localCover := Primitive.local_covered args shape (Primitive.measured s args shape value) low
  have stackCover := Primitive.stack_covered args shape (Primitive.measured s args shape value) low
  have descriptorCover := Primitive.descriptor_covered args shape
  have valueCover := Primitive.value_covered args value
  have descBound := (Storage.desc_physical (Storage.desc_at owned.descriptor)).2.2.1
  have valueBound := (Storage.value_physical (Storage.value_at owned.value_at)).2.2.1
  have descProtected := protected_of_covers (Storage.descriptor_protected owned.descriptor) covered
  have valueProtected := protected_of_covers (Storage.value_protected owned.value_at) covered
  refine {
    retain := owned.retain
    physical := Storage.primitive_value_physical (Storage.value_at owned.value_at)
    descriptor := Storage.primitive_projection (Storage.desc_at owned.descriptor)
    value_at := Storage.value_projection (Storage.value_at owned.value_at)
    descriptorBound := ?_
    valueBound := ?_
    resultBound := ?_
    arenaBound := owned.arena.2.2.1
    storageBound := owned.storageBound
    nonnull := owned.nonnull
    stackLow := low
    resultStack := ?_
    headerLocal := protected_of_covers owned.headerLocal localCover
    freeLocal := ?_
    descriptorOwned := ?_
    valueOwned := ?_
    operandOwned := ?_
    backingOwned := ?_ }
  · intro span member
    obtain ⟨outer, outerMember, lower, upper⟩ := descriptorCover span member
    simp only [List.mem_singleton] at outerMember
    subst outer
    exact Nat.le_trans upper descBound
  · intro span member
    obtain ⟨outer, outerMember, lower, upper⟩ := valueCover span member
    simp only [List.mem_singleton] at outerMember
    subst outer
    exact Nat.le_trans upper valueBound
  · have extent := Serialize.resultExtent_le (Primitive.measured s args shape value)
    have bound := owned.result.2.2.1
    omega
  · intro span member
    obtain ⟨outer, outerMember, lower, upper⟩ := Primitive.result_covered args _ span member
    simp only [List.mem_singleton] at outerMember
    subst outer
    exact protected_subspan_of_bounds (protected_of_covers owned.resultStack stackCover) lower upper
  · apply protected_of_covers owned.freeLocal
    intro span member
    rcases List.mem_append.mp member with localMember | header
    · obtain ⟨outer, outerMember, lower, upper⟩ := localCover span localMember
      exact ⟨outer, List.mem_append.mpr (Or.inl outerMember), lower, upper⟩
    · exact ⟨span, List.mem_append.mpr (Or.inr header), Nat.le_refl _, Nat.le_refl _⟩
  · intro span member
    obtain ⟨outer, outerMember, lower, upper⟩ := descriptorCover span member
    simp only [List.mem_singleton] at outerMember
    subst outer
    exact protected_subspan_of_bounds descProtected lower upper
  · intro span member
    obtain ⟨outer, outerMember, lower, upper⟩ := valueCover span member
    simp only [List.mem_singleton] at outerMember
    subst outer
    exact protected_subspan_of_bounds valueProtected lower upper
  · intro operand member
    apply Serialize.operand_owned_of_covers covered operand
    rcases List.mem_append.mp member with descriptor | stored
    · exact Storage.descriptor_operands_owned owned.descriptor operand descriptor
    · exact Storage.value_operands_owned owned.value_at operand stored
  · intro span member
    rw [Primitive.backing_eq] at member
    exact protected_of_covers
      (Storage.value_backing_owned (Primitive.inputArgs args) owned.value_at span member) covered

end SszArm.Codec.Measure
