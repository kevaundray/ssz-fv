import SszArm.CodecMeasureProvenanceSource

namespace SszArm.Codec.Measure.Provenance

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure
open Delimited (Span Protected)

 theorem measureStep_owned (writes : List Span) (original : ArmState)
    (shape : Desc) (logical : Value) (arena : SszNative.Delimited.ArenaState)
    (retain : Bool) (visit : Visit logical.children)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (schema : DescSource writes original shape) (value : ValueSource writes original logical)
    (visitOwned : ∀ child member desc arena retain, DescSource writes original desc →
      arena.base + arena.capacity ≤ 2^64 →
      Protected writes (arena.base + arena.used) (arena.capacity - arena.used) →
      ResultOwned writes (Storage.PlanBackingsProtected writes)
        (visit child member desc arena retain).result)
    (visitMono : ∀ child member desc arena retain,
      CursorSafe arena (visit child member desc arena retain).used) :
    ResultOwned writes (Storage.PlanBackingsProtected writes)
      (measureStep shape logical arena retain visit).result := by
  obtain ⟨descAddress, descAt⟩ := schema
  obtain ⟨valueAddress, valueAt⟩ := value
  cases shape with
  | primitive shape =>
      exact primitive_owned writes arena shape logical storage free
        (Storage.descriptor_operands_owned descAt)
  | vector child count =>
      cases logical with
      | seq children =>
          obtain ⟨pointer, _, childAt⟩ := Storage.vector_child descAt
          simp only [measureStep]
          apply bind_owned (fun _ => True)
          · exact exactCount_owned writes count _ _ (Storage.operand_owned descAt.2.2.1)
          · intro _ _
            apply measureParts_owned writes (DescSource writes original) _ children visit _ retain storage
            · simpa only [(exactCount_resources count children.length arena.used).1] using free
            · exact ⟨pointer, childAt⟩
            · exact visitOwned
            · exact visitMono
      | _ => exact ⟨True.intro, True.intro⟩
  | list child limit =>
      cases logical with
      | seq children =>
          obtain ⟨pointer, _, childAt⟩ := Storage.list_child descAt
          simp only [measureStep]
          apply bind_owned (fun _ => True)
          · apply bounded_owned writes (some limit) _ _ True.intro
            intro number same
            cases same
            exact Storage.operand_owned descAt.2.2.1
          · intro _ _
            apply measureParts_owned writes (DescSource writes original) _ children visit _ retain storage
            · simpa only [(bounded_resources (some limit) (SszNative.Serialize.count children.length) arena.used).1] using free
            · exact ⟨pointer, childAt⟩
            · exact visitOwned
            · exact visitMono
      | _ => exact ⟨True.intro, True.intro⟩
  | progressiveList child limit =>
      cases logical with
      | seq children =>
          obtain ⟨pointer, _, childAt⟩ := Storage.progressiveList_child descAt
          simp only [measureStep]
          apply bind_owned (fun _ => True)
          · apply bounded_owned writes limit _ _ True.intro
            intro number same
            cases same
            exact Storage.operand_owned descAt.2.2.1.2
          · intro _ _
            apply measureParts_owned writes (DescSource writes original) _ children visit _ retain storage
            · simpa only [(bounded_resources limit (SszNative.Serialize.count children.length) arena.used).1] using free
            · exact ⟨pointer, childAt⟩
            · exact visitOwned
            · exact visitMono
      | _ => exact ⟨True.intro, True.intro⟩
  | container fields =>
      cases logical with
      | seq children =>
          obtain ⟨pointer, _, _, _, fieldsAt⟩ := Storage.container_fields descAt
          exact measureParts_owned writes (DescSource writes original) (.fields fields) children visit
            arena retain storage free (field_sources fields fieldsAt) visitOwned visitMono
      | _ => exact ⟨True.intro, True.intro⟩
  | progressiveContainer active fields =>
      cases logical with
      | seq children =>
          obtain ⟨pointer, _, _, _, fieldsAt⟩ := Storage.progressiveContainer_fields descAt
          exact measureParts_owned writes (DescSource writes original) (.fields fields) children visit
            arena retain storage free (field_sources fields fieldsAt) visitOwned visitMono
      | _ => exact ⟨True.intro, True.intro⟩
  | compatibleUnion variants =>
      cases logical with
      | union selector child =>
          obtain ⟨pointer, _, _, _, variantsAt⟩ := Storage.compatibleUnion_variants descAt
          simp only [measureStep]
          apply bind_owned (DescSource writes original)
          · exact option_source variants selector (Storage.operand_owned valueAt.2.2.1)
              (variant_sources variants variantsAt)
          · intro chosen source
            apply bind_owned (Storage.PlanBackingsProtected writes)
            · exact visitOwned child _ chosen arena retain source storage free
            · intro planned planOwned
              apply unionPlan_owned writes _ planned retain storage
              · exact Serialize.free_protected_after arena free _ (visitMono child _ chosen arena retain).1
              · exact planOwned
      | _ => exact ⟨True.intro, True.intro⟩

end SszArm.Codec.Measure.Provenance
