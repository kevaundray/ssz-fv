import SszArm.CodecMeasureProvenanceLoop

namespace SszArm.Codec.Measure.Provenance

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure
open Delimited (Span Protected)

 theorem result_strengthen {α : Type} {writes : List Span} (property fact : α → Prop)
    (result : Except SszNative.Codec.Error α) (input : ResultOwned writes property result)
    (facts : ∀ value, result = .ok value → fact value) :
    ResultOwned writes (fun value => property value ∧ fact value) result := by
  cases result with
  | error reason => exact input
  | ok value => exact ⟨input, facts value rfl⟩

 theorem measureParts_owned (writes : List Span) (source : Desc → Prop)
    (parts : Parts) (values : List Value) (visit : Visit values)
    (arena : SszNative.Delimited.ArenaState) (retain : Bool)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (schemas : PartsSource source parts)
    (visitOwned : ∀ child member shape arena retain, source shape →
      arena.base + arena.capacity ≤ 2^64 →
      Protected writes (arena.base + arena.used) (arena.capacity - arena.used) →
      ResultOwned writes (Storage.PlanBackingsProtected writes)
        (visit child member shape arena retain).result)
    (visitMono : ∀ child member shape arena retain,
      CursorSafe arena (visit child member shape arena retain).used) :
    ResultOwned writes (Storage.PlanBackingsProtected writes)
      (measureParts parts values visit arena retain).result := by
  unfold measureParts
  dsimp only
  split
  · rename_i kept
    apply bind_owned (fun allocation => Protected writes allocation.pointer (40 * parts.paired values))
    · exact reservePlans_owned writes arena _ free
    · intro allocation allocated
      have nextFree := Serialize.free_protected_after arena free _ (reservePlans_cursorSafe _ arena).1
      apply bind_owned (fun totals => PartialOwned writes totals ∧
        totals.children.length = parts.paired values)
      · apply result_strengthen (PartialOwned writes)
        · exact measureLoop_owned writes source parts values visit _ _ 0 initial _
            storage nextFree (initial_owned writes) schemas visitOwned visitMono
        · intro totals success
          have count := measureLoop_child_count parts values visit _ _ 0 initial totals _ success
          simpa only [initial, List.length_nil, Nat.zero_add, kept, ↓reduceIte] using count
      · intro totals stored
        apply finishParts_owned writes _ parts values totals (some allocation) storage
        · exact Serialize.free_protected_after _ nextFree _
            (measureLoop_cursorSafe parts values visit _ _ 0 initial _ visitMono).1
        · exact stored.1
        · simpa only [stored.2] using allocated
  · rename_i notKept
    apply bind_owned (fun totals => PartialOwned writes totals ∧ totals.children.length = 0)
    · apply result_strengthen (PartialOwned writes)
      · exact measureLoop_owned writes source parts values visit _ _ 0 initial arena
          storage free (initial_owned writes) schemas visitOwned visitMono
      · intro totals success
        have count := measureLoop_child_count parts values visit _ _ 0 initial totals arena success
        simpa only [initial, List.length_nil, Nat.zero_add, notKept, ↓reduceIte] using count
    · intro totals stored
      apply finishParts_owned writes _ parts values totals none storage
      · exact Serialize.free_protected_after arena free _
          (measureLoop_cursorSafe parts values visit _ _ 0 initial arena visitMono).1
      · exact stored.1
      · rw [stored.2]
        exact Or.inl (by omega)

end SszArm.Codec.Measure.Provenance
