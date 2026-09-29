import SszArm.CodecMeasureProvenancePartial

namespace SszArm.Codec.Measure.Provenance

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure
open Delimited (Span Protected)

 def PartsSource (source : Desc → Prop) : Parts → Prop
  | .repeated shape => source shape
  | .fields fields => ∀ field ∈ fields, source field.2

 theorem writePlan_bind_result {α : Type} (allocation : Option SszNative.Arena.Reservation)
    (index : Nat) (plan : Plan) (used : Nat) (next : Nat → Outcome α) :
    (bind (writePlan allocation index plan used) (fun _ cursor => next cursor)).result =
      (next used).result := by
  cases allocation <;> rfl

 theorem measureLoop_owned (writes : List Span) (source : Desc → Prop)
    (parts : Parts) (values : List Value) (visit : Visit values)
    (keep : Bool) (allocation : Option SszNative.Arena.Reservation) (index : Nat)
    (totals : Partial) (arena : SszNative.Delimited.ArenaState)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (input : PartialOwned writes totals) (schemas : PartsSource source parts)
    (visitOwned : ∀ child member shape arena retain, source shape →
      arena.base + arena.capacity ≤ 2^64 →
      Protected writes (arena.base + arena.used) (arena.capacity - arena.used) →
      ResultOwned writes (Storage.PlanBackingsProtected writes)
        (visit child member shape arena retain).result)
    (visitMono : ∀ child member shape arena retain,
      CursorSafe arena (visit child member shape arena retain).used) :
    ResultOwned writes (PartialOwned writes)
      (measureLoop parts values visit keep allocation index totals arena).result := by
  induction values generalizing parts index totals arena with
  | nil => exact input
  | cons first rest ih =>
      cases parts with
      | repeated shape =>
          simp only [measureLoop]
          apply bind_owned (Storage.PlanBackingsProtected writes)
          · exact visitOwned first _ shape arena keep schemas storage free
          · intro child childOwned
            have childFree := Serialize.free_protected_after arena free _
              (visitMono first _ shape arena keep).1
            apply bind_owned (PartialOwned writes)
            · exact accumulate_owned writes _ _ child totals storage childFree childOwned input
            · intro next nextOwned
              rw [writePlan_bind_result]
              apply ih
              · exact storage
              · exact Serialize.free_protected_after _ childFree _
                  (accumulate_cursorSafe _ child totals _).1
              · exact partial_retain keep nextOwned childOwned
              · exact schemas
              · intro other member desc nextArena retain known bounded freeNext
                exact visitOwned other (List.mem_cons_of_mem _ member) desc nextArena retain known bounded freeNext
              · intro other member desc nextArena retain
                exact visitMono other (List.mem_cons_of_mem _ member) desc nextArena retain
      | fields fields =>
          cases fields with
          | nil => exact input
          | cons field fields =>
              obtain ⟨name, shape⟩ := field
              simp only [measureLoop]
              apply bind_owned (Storage.PlanBackingsProtected writes)
              · exact visitOwned first _ shape arena keep (schemas _ (by simp)) storage free
              · intro child childOwned
                have childFree := Serialize.free_protected_after arena free _
                  (visitMono first _ shape arena keep).1
                apply bind_owned (PartialOwned writes)
                · exact accumulate_owned writes _ _ child totals storage childFree childOwned input
                · intro next nextOwned
                  rw [writePlan_bind_result]
                  apply ih
                  · exact storage
                  · exact Serialize.free_protected_after _ childFree _
                      (accumulate_cursorSafe _ child totals _).1
                  · exact partial_retain keep nextOwned childOwned
                  · intro field member
                    exact schemas field (List.mem_cons_of_mem _ member)
                  · intro other member desc nextArena retain known bounded freeNext
                    exact visitOwned other (List.mem_cons_of_mem _ member) desc nextArena retain known bounded freeNext
                  · intro other member desc nextArena retain
                    exact visitMono other (List.mem_cons_of_mem _ member) desc nextArena retain

end SszArm.Codec.Measure.Provenance
