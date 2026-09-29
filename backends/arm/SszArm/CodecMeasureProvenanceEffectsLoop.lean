import SszArm.CodecMeasureProvenanceEffectsModel

namespace SszArm.Codec.Measure.Provenance

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure
open Delimited (Span Protected)

 def SlotsOwned (writes : List Span) (allocation : Option SszNative.Arena.Reservation)
    (index count : Nat) : Prop :=
  ∀ reservation, allocation = some reservation →
    Protected writes (reservation.pointer + 40 * index) (40 * count)

 theorem slots_head {writes allocation index count} (input : SlotsOwned writes allocation index count)
    (positive : 0 < count) : ∀ reservation, allocation = some reservation →
    Protected writes (reservation.pointer + 40 * index) 40 := by
  intro reservation same
  simpa only [Nat.add_zero] using (input reservation same).subspan 0 40 (by omega)

 theorem slots_tail {writes allocation index count}
    (input : SlotsOwned writes allocation index (count + 1)) :
    SlotsOwned writes allocation (index + 1) count := by
  intro reservation same
  have rest := (input reservation same).subspan 40 (40 * count) (by omega)
  simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using rest

 theorem measureLoop_effects_owned (writes : List Span) (source : Desc → Prop)
    (parts : Parts) (values : List Value) (visit : Visit values)
    (keep : Bool) (allocation : Option SszNative.Arena.Reservation) (index : Nat)
    (totals : Partial) (arena : SszNative.Delimited.ArenaState)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (schemas : PartsSource source parts)
    (slots : SlotsOwned writes allocation index (parts.paired values))
    (visitOwned : ∀ child member shape arena retain, source shape →
      arena.base + arena.capacity ≤ 2^64 →
      Protected writes (arena.base + arena.used) (arena.capacity - arena.used) →
      ResultOwned writes (Storage.PlanBackingsProtected writes) (visit child member shape arena retain).result)
    (visitEffects : ∀ child member shape arena retain, source shape →
      arena.base + arena.capacity ≤ 2^64 →
      Protected writes (arena.base + arena.used) (arena.capacity - arena.used) →
      EffectsOwned writes (visit child member shape arena retain).effects)
    (visitMono : ∀ child member shape arena retain,
      CursorSafe arena (visit child member shape arena retain).used) :
    EffectsOwned writes (measureLoop parts values visit keep allocation index totals arena).effects := by
  induction values generalizing parts index totals arena with
  | nil => exact effectsOwned_nil writes
  | cons first rest ih =>
      cases parts with
      | repeated shape =>
          simp only [measureLoop]
          apply bind_effects
          · exact visitEffects first _ shape arena keep schemas storage free
          · intro child returned
            have childOwned : Storage.PlanBackingsProtected writes child := by
              simpa only [returned, ResultOwned] using visitOwned first _ shape arena keep schemas storage free
            have childFree := Serialize.free_protected_after arena free _ (visitMono first _ shape arena keep).1
            apply bind_effects
            · exact accumulate_effects_owned writes _ _ child totals storage childFree
            · intro next _
              apply bind_effects
              · exact writePlan_effects_owned allocation index child _ childOwned
                  (slots_head slots (by simp [Parts.paired]))
              · intro _ _
                simp only [writePlan_used]
                apply ih
                · exact storage
                · exact Serialize.free_protected_after _ childFree _ (accumulate_cursorSafe _ child totals _).1
                · exact schemas
                · exact slots_tail slots
                · intro other member desc nextArena retain known bounded freeNext
                  exact visitOwned other (List.mem_cons_of_mem _ member) desc nextArena retain known bounded freeNext
                · intro other member desc nextArena retain known bounded freeNext
                  exact visitEffects other (List.mem_cons_of_mem _ member) desc nextArena retain known bounded freeNext
                · intro other member desc nextArena retain
                  exact visitMono other (List.mem_cons_of_mem _ member) desc nextArena retain
      | fields fields =>
          cases fields with
          | nil => exact effectsOwned_nil writes
          | cons field fields =>
              obtain ⟨name, shape⟩ := field
              have paired : (Parts.fields ((name, shape) :: fields)).paired (first :: rest) =
                  (Parts.fields fields).paired rest + 1 := by
                simp only [Parts.paired, List.length_cons]
                omega
              simp only [measureLoop]
              apply bind_effects
              · exact visitEffects first _ shape arena keep (schemas _ (by simp)) storage free
              · intro child returned
                have childOwned : Storage.PlanBackingsProtected writes child := by
                  simpa only [returned, ResultOwned] using
                    visitOwned first _ shape arena keep (schemas _ (by simp)) storage free
                have childFree := Serialize.free_protected_after arena free _ (visitMono first _ shape arena keep).1
                apply bind_effects
                · exact accumulate_effects_owned writes _ _ child totals storage childFree
                · intro next _
                  apply bind_effects
                  · exact writePlan_effects_owned allocation index child _ childOwned
                      (slots_head slots (by rw [paired]; omega))
                  · intro _ _
                    simp only [writePlan_used]
                    apply ih
                    · exact storage
                    · exact Serialize.free_protected_after _ childFree _ (accumulate_cursorSafe _ child totals _).1
                    · intro field member
                      exact schemas field (List.mem_cons_of_mem _ member)
                    · apply slots_tail
                      simpa only [paired] using slots
                    · intro other member desc nextArena retain known bounded freeNext
                      exact visitOwned other (List.mem_cons_of_mem _ member) desc nextArena retain known bounded freeNext
                    · intro other member desc nextArena retain known bounded freeNext
                      exact visitEffects other (List.mem_cons_of_mem _ member) desc nextArena retain known bounded freeNext
                    · intro other member desc nextArena retain
                      exact visitMono other (List.mem_cons_of_mem _ member) desc nextArena retain

end SszArm.Codec.Measure.Provenance
