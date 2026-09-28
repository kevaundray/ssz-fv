import SszX86.SerializePublishSemantic
import SszX86.SerializeMemory

namespace SszX86.Serialize
open SszNative SszNative.Serialize UintCodec

def ResultBorrows (result : Except Error NatOperand) (a : BitVec 64) : Prop :=
  match result with
  | .ok operand => Emit.NatBorrowed operand a
  | .error reason => Publish.ErrorBorrows reason a

theorem allocation_append_left (left right : List (NatArithmetic.Outcome NatOperand))
    (a : BitVec 64) (inside : Measure.AllocationWrites left a) :
    Measure.AllocationWrites (left ++ right) a := by
  obtain ⟨call, member, reservation, allocated, span⟩ := inside
  exact ⟨call, List.mem_append_left right member, reservation, allocated, span⟩

theorem allocation_append_right (left right : List (NatArithmetic.Outcome NatOperand))
    (a : BitVec 64) (inside : Measure.AllocationWrites right a) :
    Measure.AllocationWrites (left ++ right) a := by
  obtain ⟨call, member, reservation, allocated, span⟩ := inside
  exact ⟨call, List.mem_append_right left member, reservation, allocated, span⟩

theorem fromWide_provenance (arena : Delimited.ArenaState) (wide : BitVec 128)
    (a : BitVec 64) (borrowed : ResultBorrows (fromWide arena wide).result a) :
    Measure.AllocationWrites (fromWide arena wide).calls a := by
  by_cases small : wide.toNat < 2 ^ 64
  · simp only [fromWide, NatArithmetic.fromWide, small, ↓reduceIte,
      NatArithmetic.unchanged, Except.mapError, ResultBorrows, Emit.NatBorrowed] at borrowed
  · have high : (wide >>> 64).setWidth 64 ≠ 0#64 := fun zero =>
      small ((NatFromU128.wide_small_iff wide).2 zero)
    cases reserved : Arena.reserve arena.base arena.capacity arena.used 2 with
    | none =>
      simp only [fromWide, NatArithmetic.fromWide, small, ↓reduceIte, reserved,
        NatArithmetic.unchanged, Except.mapError, ResultBorrows, Publish.ErrorBorrows] at borrowed
    | some reservation =>
      simp only [fromWide, NatArithmetic.fromWide, small, ↓reduceIte, reserved,
        NatArithmetic.committed, Except.mapError] at borrowed ⊢
      refine ⟨NatArithmetic.committed reservation
        [wide.setWidth 64, (wide >>> 64).setWidth 64], ?_, reservation, rfl, ?_⟩
      · simp only [NatArithmetic.committed, List.mem_singleton]
      · simpa [ResultBorrows, NatOperand.fromWords, Limbs.trim, high, Emit.NatBorrowed,
          NatArithmetic.committed, Emit.InSpan, Measure.InSpan] using borrowed

theorem list_provenance (limit : Option NatOperand) (bits : Packed)
    (arena : Delimited.ArenaState) (a : BitVec 64)
    (borrowed : ResultBorrows (measureList limit bits arena).result a) :
    (∃ cap, limit = some cap ∧ Emit.NatBorrowed cap a) ∨
      Measure.AllocationWrites (measureList limit bits arena).calls a := by
  rcases fromWide_cases arena bits.count with ⟨actual, counted, actualValue⟩ | exhausted
  · cases limit with
    | none =>
      have final := fromWide_provenance
        {arena with used := (fromWide arena bits.count).used}
        (BitVec.ofNat 128 (bits.count.toNat / 8 + 1)) a (by
          simpa only [measureList, SszNative.Serialize.bind, counted, bounded, unchanged] using borrowed)
      right
      simpa only [measureList, SszNative.Serialize.bind, counted, bounded, unchanged,
        List.nil_append] using allocation_append_right (fromWide arena bits.count).calls _ a final
    | some cap =>
      by_cases fits : actual.value ≤ cap.value
      · have final := fromWide_provenance
          {arena with used := (fromWide arena bits.count).used}
          (BitVec.ofNat 128 (bits.count.toNat / 8 + 1)) a (by
            simpa only [measureList, SszNative.Serialize.bind, counted, bounded, fits,
              ↓reduceIte, unchanged] using borrowed)
        right
        simpa only [measureList, SszNative.Serialize.bind, counted, bounded, fits,
          ↓reduceIte, unchanged, List.nil_append] using
          allocation_append_right (fromWide arena bits.count).calls _ a final
      · simp only [measureList, SszNative.Serialize.bind, counted, bounded, fits,
          ↓reduceIte, unchanged, ResultBorrows, Publish.ErrorBorrows] at borrowed
        rcases borrowed with expected | count
        · exact Or.inl ⟨cap, rfl, expected⟩
        · right
          have first := fromWide_provenance arena bits.count a (by
            simpa only [counted, ResultBorrows] using count)
          simpa only [measureList, SszNative.Serialize.bind, counted, bounded, fits,
            ↓reduceIte, unchanged, List.append_nil] using first
  · simp only [measureList, SszNative.Serialize.bind, exhausted,
      ResultBorrows, Publish.ErrorBorrows] at borrowed

/-- A returned primitive Nat borrows only an original descriptor or an allocation
in this exact measurement trace. This derives later store safety, not success. -/
theorem measure_provenance (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (a : BitVec 64) (borrowed : ResultBorrows (SszNative.Serialize.measure desc value arena).result a) :
    Emit.DescBorrowed desc a ∨
      Measure.AllocationWrites (SszNative.Serialize.measure desc value arena).calls a := by
  cases desc <;> cases value <;>
    simp only [SszNative.Serialize.measure] at borrowed ⊢
  all_goals try { exact False.elim borrowed }
  · rename_i logicalWidth number
    by_cases fits : uintFits logicalWidth number
    · left; simpa only [fits, ↓reduceIte, unchanged, ResultBorrows, Emit.DescBorrowed] using borrowed
    · simp only [fits, ↓reduceIte, unchanged, ResultBorrows, Publish.ErrorBorrows] at borrowed
  · rename_i length bytes
    by_cases same : length.value = bytes.size
    · simp only [same, ↓reduceIte, unchanged, ResultBorrows, count, Emit.NatBorrowed] at borrowed
    · left
      simpa only [same, ↓reduceIte, unchanged, ResultBorrows, Publish.ErrorBorrows,
        count, Emit.NatBorrowed, or_false, Emit.DescBorrowed] using borrowed
  · rename_i cap bytes
    by_cases fits : (count bytes.size).value ≤ cap.value
    · simp only [bounded, fits, ↓reduceIte, SszNative.Serialize.bind, unchanged] at borrowed
      exact False.elim borrowed
    · left
      simp only [bounded, fits, ↓reduceIte, SszNative.Serialize.bind, unchanged,
        ResultBorrows, Publish.ErrorBorrows] at borrowed
      rcases borrowed with expected | actual
      · exact expected
      · exact False.elim actual
  · rename_i length bits
    by_cases same : length.value = bits.count.toNat
    · simp only [same, ↓reduceIte, unchanged, ResultBorrows, count, Emit.NatBorrowed] at borrowed
    · rcases fromWide_cases arena bits.count with ⟨actual, counted, actualValue⟩ | exhausted
      · simp only [same, ↓reduceIte, SszNative.Serialize.bind, counted, unchanged,
          ResultBorrows, Publish.ErrorBorrows] at borrowed
        rcases borrowed with expected | actualBorrowed
        · exact Or.inl expected
        · right
          have first := fromWide_provenance arena bits.count a (by
            simpa only [counted, ResultBorrows] using actualBorrowed)
          simpa only [same, ↓reduceIte, SszNative.Serialize.bind, counted, unchanged,
            List.append_nil] using first
      · simp only [same, ↓reduceIte, SszNative.Serialize.bind, exhausted,
          ResultBorrows, Publish.ErrorBorrows] at borrowed
  · rename_i cap bits
    rcases list_provenance (some cap) bits arena a borrowed with ⟨bound, equal, limbs⟩ | allocation
    · cases equal; exact Or.inl limbs
    · exact Or.inr allocation
  · rename_i limit bits
    rcases list_provenance limit bits arena a borrowed with ⟨bound, equal, limbs⟩ | allocation
    · rw [equal]; exact Or.inl limbs
    · exact Or.inr allocation

theorem Owned.result_borrows_safe {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address «capacity» used ra : BitVec 64}
    (owned : Owned s base desc value buffer address «capacity» used ra)
    (a : BitVec 64)
    (borrowed : ResultBorrows
      (SszNative.Serialize.measure desc value (arenaState address «capacity» used)).result a) :
    ¬ LaterWrites s a := by
  rcases measure_provenance desc value (arenaState address «capacity» used) a borrowed with
      input | allocation
  · intro writes
    exact owned.readonly a (Or.inr (Or.inr (Or.inl input)))
      (later_reserved s address «capacity» used a writes)
  · exact owned.later_free a (Measure.allocation_in_free desc value address «capacity» used a allocation)

end SszX86.Serialize
