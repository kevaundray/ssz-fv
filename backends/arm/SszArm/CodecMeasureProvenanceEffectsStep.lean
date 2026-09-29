import SszArm.CodecMeasureProvenanceEffectsParts

namespace SszArm.Codec.Measure.Provenance

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure
open Delimited (Span Protected)

 theorem measureStep_effects_owned (writes : List Span) (original : ArmState)
    (shape : Desc) (logical : Value) (arena : SszNative.Delimited.ArenaState)
    (retain : Bool) (visit : Visit logical.children)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (schema : DescSource writes original shape) (value : ValueSource writes original logical)
    (visitOwned : ∀ child member desc arena retain, DescSource writes original desc →
      arena.base + arena.capacity ≤ 2^64 →
      Protected writes (arena.base + arena.used) (arena.capacity - arena.used) →
      ResultOwned writes (Storage.PlanBackingsProtected writes) (visit child member desc arena retain).result)
    (visitEffects : ∀ child member desc arena retain, DescSource writes original desc →
      arena.base + arena.capacity ≤ 2^64 →
      Protected writes (arena.base + arena.used) (arena.capacity - arena.used) →
      EffectsOwned writes (visit child member desc arena retain).effects)
    (visitMono : ∀ child member desc arena retain,
      CursorSafe arena (visit child member desc arena retain).used) :
    EffectsOwned writes (measureStep shape logical arena retain visit).effects := by
  obtain ⟨descAddress, descAt⟩ := schema
  obtain ⟨valueAddress, valueAt⟩ := value
  cases shape with
  | primitive shape => exact primitive_effects_owned writes arena shape logical storage free
  | vector child count =>
      cases logical with
      | seq children =>
          obtain ⟨pointer, _, childAt⟩ := Storage.vector_child descAt
          simp only [measureStep]
          apply bind_effects
          · rw [(exactCount_resources count children.length arena.used).2]
            exact effectsOwned_nil writes
          · intro _ _
            apply measureParts_effects_owned writes (DescSource writes original) _ children visit _ retain storage
            · simpa only [(exactCount_resources count children.length arena.used).1] using free
            · exact ⟨pointer, childAt⟩
            · exact visitOwned
            · exact visitEffects
            · exact visitMono
      | _ => exact effectsOwned_nil writes
  | list child limit =>
      cases logical with
      | seq children =>
          obtain ⟨pointer, _, childAt⟩ := Storage.list_child descAt
          simp only [measureStep]
          apply bind_effects
          · rw [(bounded_resources (some limit) (SszNative.Serialize.count children.length) arena.used).2]
            exact effectsOwned_nil writes
          · intro _ _
            apply measureParts_effects_owned writes (DescSource writes original) _ children visit _ retain storage
            · simpa only [(bounded_resources (some limit) (SszNative.Serialize.count children.length) arena.used).1] using free
            · exact ⟨pointer, childAt⟩
            · exact visitOwned
            · exact visitEffects
            · exact visitMono
      | _ => exact effectsOwned_nil writes
  | progressiveList child limit =>
      cases logical with
      | seq children =>
          obtain ⟨pointer, _, childAt⟩ := Storage.progressiveList_child descAt
          simp only [measureStep]
          apply bind_effects
          · rw [(bounded_resources limit (SszNative.Serialize.count children.length) arena.used).2]
            exact effectsOwned_nil writes
          · intro _ _
            apply measureParts_effects_owned writes (DescSource writes original) _ children visit _ retain storage
            · simpa only [(bounded_resources limit (SszNative.Serialize.count children.length) arena.used).1] using free
            · exact ⟨pointer, childAt⟩
            · exact visitOwned
            · exact visitEffects
            · exact visitMono
      | _ => exact effectsOwned_nil writes
  | container fields =>
      cases logical with
      | seq children =>
          obtain ⟨pointer, _, _, _, fieldsAt⟩ := Storage.container_fields descAt
          exact measureParts_effects_owned writes (DescSource writes original) (.fields fields) children visit
            arena retain storage free (field_sources fields fieldsAt) visitOwned visitEffects visitMono
      | _ => exact effectsOwned_nil writes
  | progressiveContainer active fields =>
      cases logical with
      | seq children =>
          obtain ⟨pointer, _, _, _, fieldsAt⟩ := Storage.progressiveContainer_fields descAt
          exact measureParts_effects_owned writes (DescSource writes original) (.fields fields) children visit
            arena retain storage free (field_sources fields fieldsAt) visitOwned visitEffects visitMono
      | _ => exact effectsOwned_nil writes
  | compatibleUnion variants =>
      cases logical with
      | union selector child =>
          obtain ⟨pointer, _, _, _, variantsAt⟩ := Storage.compatibleUnion_variants descAt
          simp only [measureStep]
          apply bind_effects
          · exact effectsOwned_nil writes
          · intro chosen selected
            have chosenSource : DescSource writes original chosen := by
              simpa only [unchanged, selected, ResultOwned] using
                option_source variants selector (Storage.operand_owned valueAt.2.2.1)
                  (variant_sources variants variantsAt)
            apply bind_effects
            · exact visitEffects child _ chosen arena retain chosenSource storage free
            · intro planned returned
              have plannedOwned : Storage.PlanBackingsProtected writes planned := by
                simpa only [returned, ResultOwned] using
                  visitOwned child _ chosen arena retain chosenSource storage free
              apply unionPlan_effects_owned writes _ planned retain storage
              · exact Serialize.free_protected_after arena free _ (visitMono child _ chosen arena retain).1
              · exact plannedOwned
      | _ => exact effectsOwned_nil writes

end SszArm.Codec.Measure.Provenance
