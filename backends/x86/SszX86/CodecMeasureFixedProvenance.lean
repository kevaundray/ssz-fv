import SszX86.CodecMeasureFixedArithmeticMulResources
import SszX86.CodecMeasureFixedArithmeticDivideResources
import SszX86.CodecStorageViews
import SszFixedSizeOrder

namespace SszX86.CodecMeasureFixed
open SszNative

/-- Trace concatenation preserves both earlier and later complete allocations. -/
theorem allocationWrites_append (left right : List (NatArithmetic.Outcome NatOperand))
    (a : BitVec 64) :
    Measure.AllocationWrites (left ++ right) a ↔
      Measure.AllocationWrites left a ∨ Measure.AllocationWrites right a := by
  constructor
  · rintro ⟨call, member, reservation, allocated, inside⟩
    rcases List.mem_append.mp member with member | member
    · exact Or.inl ⟨call, member, reservation, allocated, inside⟩
    · exact Or.inr ⟨call, member, reservation, allocated, inside⟩
  · rintro (⟨call, member, reservation, allocated, inside⟩ |
      ⟨call, member, reservation, allocated, inside⟩)
    · exact ⟨call, List.mem_append.mpr (Or.inl member), reservation, allocated, inside⟩
    · exact ⟨call, List.mem_append.mpr (Or.inr member), reservation, allocated, inside⟩

theorem add_width_provenance (left right : NatOperand) (arena : Delimited.ArenaState)
    (width : NatOperand) (success : (FixedSize.add left right arena).result = .ok width)
    (a : BitVec 64) (borrowed : Emit.NatBorrowed width a) :
    Emit.NatBorrowed left a ∨ Emit.NatBorrowed right a ∨
      Measure.AllocationWrites (FixedSize.add left right arena).calls a := by
  have arithmeticSuccess :
      (SszNative.NatAdd.run left right arena.base arena.capacity arena.used).result = .ok width := by
    cases result : (SszNative.NatAdd.run left right arena.base arena.capacity arena.used).result <;>
      simpa only [FixedSize.add, FixedSize.arithmetic, result, Except.mapError] using success
  rcases add_result_provenance left right arena.base arena.capacity arena.used width
    arithmeticSuccess a borrowed with (left | right) | allocated
  · exact Or.inl left
  · exact Or.inr (Or.inl right)
  · exact Or.inr (Or.inr ((arithmeticWrites_singleton _ _).mp allocated))

theorem mul_width_provenance (left right : NatOperand) (arena : Delimited.ArenaState)
    (width : NatOperand) (success : (FixedSize.mul left right arena).result = .ok width)
    (a : BitVec 64) (borrowed : Emit.NatBorrowed width a) :
    Emit.NatBorrowed left a ∨ Emit.NatBorrowed right a ∨
      Measure.AllocationWrites (FixedSize.mul left right arena).calls a := by
  have arithmeticSuccess :
      (SszNative.NatMul.run left right arena.base arena.capacity arena.used).result = .ok width := by
    cases result : (SszNative.NatMul.run left right arena.base arena.capacity arena.used).result <;>
      simpa only [FixedSize.mul, FixedSize.arithmetic, result, Except.mapError] using success
  rcases mul_result_provenance left right arena.base arena.capacity arena.used width
    arithmeticSuccess a borrowed with (left | right) | allocated
  · exact Or.inl left
  · exact Or.inr (Or.inl right)
  · exact Or.inr (Or.inr ((arithmeticWrites_singleton _ _).mp allocated))

/-- A rounded bit width can borrow only the quotient initialized earlier in
this same model trace, or its own increment allocation. -/
theorem bit_width_provenance (length width : NatOperand) (arena : Delimited.ArenaState)
    (success : (FixedSize.bitWidth length arena).result = .ok width)
    (a : BitVec 64) (borrowed : Emit.NatBorrowed width a) :
    Measure.AllocationWrites (FixedSize.bitWidth length arena).calls a := by
  cases divided : (SszNative.NatDivision.run length 8 arena.base arena.capacity arena.used).result with
  | error reason =>
    simp only [FixedSize.bitWidth, FixedSize.div8, Serialize.bind, divided, Except.mapError] at success
  | ok quotient =>
    rcases quotient with ⟨quotient, remainder⟩
    have dividedModel : (FixedSize.div8 length arena).result = .ok (quotient, remainder) := by
      simp only [FixedSize.div8, divided, Except.mapError]
    have quotientWrites (borrowed : Emit.NatBorrowed quotient a) :
        Measure.AllocationWrites (FixedSize.div8 length arena).calls a := by
      have writes := divide8_result_provenance length arena.base arena.capacity arena.used
        (quotient, remainder) divided a borrowed
      apply (arithmeticWrites_singleton _ _).mp
      exact writes
    by_cases exactDivision : remainder = 0
    · subst remainder
      rw [FixedSize.bitWidth_exact length quotient arena dividedModel] at success ⊢
      cases success
      exact quotientWrites borrowed
    · rw [FixedSize.bitWidth_rounded length quotient remainder arena dividedModel exactDivision]
        at success ⊢
      rcases add_width_provenance quotient (.small 1)
        {arena with used := (FixedSize.div8 length arena).used} width success a borrowed with
          quotientBorrowed | smallBorrowed | allocated
      · exact (allocationWrites_append _ _ _).mpr (Or.inl (quotientWrites quotientBorrowed))
      · exact False.elim smallBorrowed
      · exact (allocationWrites_append _ _ _).mpr (Or.inr allocated)

mutual
  /-- A measured Nat's borrowed limbs are in the original recursive readonly
  graph or in an earlier completed arithmetic allocation. This is the ownership
  fact needed before passing that Nat to the next native arithmetic call. -/
  theorem measure_fixed_provenance (m : DataMem) (r : Codec.Footprint) (p : BitVec 64)
      (desc : SszNative.Codec.Desc) (stored : Codec.DescAt m r p desc)
      (arena : Delimited.ArenaState) (width : NatOperand)
      (success : (FixedSize.measureFixed desc arena).result = .ok (some width))
      (a : BitVec 64) (borrowed : Emit.NatBorrowed width a) :
      r a ∨ Measure.AllocationWrites (FixedSize.measureFixed desc arena).calls a := by
    cases desc with
    | primitive shape =>
      cases stored with
      | descPrimitive storage =>
        cases shape with
        | bool => cases success; exact False.elim borrowed
        | uint length | byteVector length =>
          cases success
          exact Or.inl (storage.borrowed a borrowed)
        | bitVector length =>
          cases measured : (FixedSize.bitWidth length arena).result with
          | error reason =>
            simp only [FixedSize.measureFixed, FixedSize.measurePrimitive, Serialize.bind, measured] at success
          | ok measuredWidth =>
            simp only [FixedSize.measureFixed, FixedSize.measurePrimitive, Serialize.bind, measured,
              Serialize.unchanged, Except.ok.injEq, Option.some.injEq] at success
            subst width
            exact Or.inr (by
              simpa only [FixedSize.measureFixed, FixedSize.measurePrimitive, Serialize.bind,
                measured, Serialize.unchanged, List.append_nil] using
                bit_width_provenance length measuredWidth arena measured a borrowed)
        | byteList length | bitList length | progressiveBitList limit => cases success
    | vector element length =>
      obtain ⟨child, _, childStored⟩ := Codec.DescAt.vector stored
      have lengthStored := Codec.DescAt.vector_length stored
      cases childResult : (FixedSize.measureFixed element arena).result with
      | error reason => simp only [FixedSize.measureFixed, Serialize.bind, childResult] at success
      | ok measured =>
        cases measured with
        | none => simp only [FixedSize.measureFixed, Serialize.bind, childResult, Serialize.unchanged] at success
        | some childWidth =>
          have model := FixedSize.measureFixed_vector_step element length childWidth arena childResult
          cases productResult : (FixedSize.mul childWidth length
              {arena with used := (FixedSize.measureFixed element arena).used}).result with
          | error reason => simp only [model, productResult, Except.map] at success
          | ok product =>
            simp only [model, productResult, Except.map, Except.ok.injEq, Option.some.injEq] at success
            subst width
            have result := mul_width_provenance childWidth length
              {arena with used := (FixedSize.measureFixed element arena).used} product productResult a borrowed
            rw [model]
            rcases result with childBorrowed | lengthBorrowed | allocated
            · rcases measure_fixed_provenance m r child element childStored arena childWidth
                childResult a childBorrowed with original | allocated
              · exact Or.inl original
              · exact Or.inr ((allocationWrites_append _ _ _).mpr (Or.inl allocated))
            · exact Or.inl (lengthStored.borrowed a lengthBorrowed)
            · exact Or.inr ((allocationWrites_append _ _ _).mpr (Or.inr allocated))
    | container fields =>
      obtain ⟨pointer, _, fieldsStored⟩ := Codec.DescAt.container stored
      rcases measure_fields_provenance m r pointer fields fieldsStored (.small 0)
        arena width success a borrowed with small | result
      · exact False.elim small
      · exact result
    | progressiveContainer active fields =>
      obtain ⟨pointer, _, fieldsStored⟩ := Codec.DescAt.progressiveContainer stored
      rcases measure_fields_provenance m r pointer fields fieldsStored (.small 0)
        arena width success a borrowed with small | result
      · exact False.elim small
      · exact result
    | list element limit | progressiveList element limit | compatibleUnion variants => cases success

  theorem measure_fields_provenance (m : DataMem) (r : Codec.Footprint) (p : BitVec 64)
      (fields : List (String × SszNative.Codec.Desc)) (stored : Codec.FieldsAt m r p fields)
      (total : NatOperand) (arena : Delimited.ArenaState) (width : NatOperand)
      (success : (FixedSize.measureFields fields total arena).result = .ok (some width))
      (a : BitVec 64) (borrowed : Emit.NatBorrowed width a) :
      Emit.NatBorrowed total a ∨ r a ∨
        Measure.AllocationWrites (FixedSize.measureFields fields total arena).calls a := by
    cases fields with
    | nil => cases success; exact Or.inl borrowed
    | cons field rest =>
      rcases field with ⟨name, desc⟩
      obtain ⟨child, _, childStored, restStored⟩ := Codec.FieldsAt.cons stored
      cases childResult : (FixedSize.measureFixed desc arena).result with
      | error reason => simp only [FixedSize.measureFields, Serialize.bind, childResult] at success
      | ok measured =>
        cases measured with
        | none => simp only [FixedSize.measureFields, Serialize.bind, childResult, Serialize.unchanged] at success
        | some childWidth =>
          cases sumResult : (FixedSize.add total childWidth
              {arena with used := (FixedSize.measureFixed desc arena).used}).result with
          | error reason =>
            simp only [FixedSize.measureFields, Serialize.bind, childResult, sumResult] at success
          | ok next =>
            have model := FixedSize.measureFields_step name desc rest total childWidth next arena
              childResult sumResult
            have remaining : (FixedSize.measureFields rest next
                {arena with used := (FixedSize.add total childWidth
                  {arena with used := (FixedSize.measureFixed desc arena).used}).used}).result =
                .ok (some width) := by simpa only [model] using success
            have result := measure_fields_provenance m r (p + 24) rest restStored next _ width
              remaining a borrowed
            rw [model]
            rcases result with nextBorrowed | original | allocated
            · rcases add_width_provenance total childWidth
                {arena with used := (FixedSize.measureFixed desc arena).used} next sumResult a nextBorrowed with
                  totalBorrowed | childBorrowed | allocated
              · exact Or.inl totalBorrowed
              · rcases measure_fixed_provenance m r child desc childStored arena childWidth
                  childResult a childBorrowed with original | allocated
                · exact Or.inr (Or.inl original)
                · exact Or.inr (Or.inr ((allocationWrites_append _ _ _).mpr
                    (Or.inl ((allocationWrites_append _ _ _).mpr (Or.inl allocated)))))
              · exact Or.inr (Or.inr ((allocationWrites_append _ _ _).mpr
                  (Or.inl ((allocationWrites_append _ _ _).mpr (Or.inr allocated)))))
            · exact Or.inr (Or.inl original)
            · exact Or.inr (Or.inr ((allocationWrites_append _ _ _).mpr (Or.inr allocated)))
end

end SszX86.CodecMeasureFixed
