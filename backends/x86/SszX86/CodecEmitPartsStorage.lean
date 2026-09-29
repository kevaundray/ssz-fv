import SszX86.CodecStorage

set_option autoImplicit false

namespace SszX86.CodecEmitParts
open SszNative

/-- Actual niche ABI read by emit_parts: zero in word zero selects a repeated
Desc pointer in word one; a nonzero fields pointer selects the slice case. -/
inductive PartsAt (m : DataMem) (r : SszX86.Codec.Footprint) (p : BitVec 64) :
    SszNative.CodecMeasure.Parts → Prop where
  | repeated {child : BitVec 64} {desc : SszNative.Codec.Desc} :
      SszX86.Codec.Span r p 16 8 → SszX86.Codec.LoadAt m r p 8 0 →
      SszX86.Codec.LoadAt m r (p + 8) 8 (child.toNat : Int) →
      SszX86.Codec.DescAt m r child desc → PartsAt m r p (.repeated desc)
  | fields {buffer : BitVec 64} {fields : List (String × SszNative.Codec.Desc)} :
      SszX86.Codec.Span r p 16 8 →
      SszX86.Codec.SliceAt m r p buffer fields.length 24 8 →
      SszX86.Codec.FieldsAt m r buffer fields → PartsAt m r p (.fields fields)

theorem PartsAt.frame {m n : DataMem} {r w : SszX86.Codec.Footprint} {p : BitVec 64}
    {parts : SszNative.CodecMeasure.Parts} (h : PartsAt m r p parts)
    (frame : SszX86.Codec.MemoryFrame m n w) (apart : ∀ a, r a → ¬ w a) :
    PartsAt n r p parts := by
  cases h with
  | repeated span tag pointer desc =>
    exact .repeated span (tag.frame frame apart) (pointer.frame frame apart)
      (desc.frame frame apart)
  | fields span slice fields =>
    exact .fields span (slice.frame frame apart) (fields.frame frame apart)

/-- Option<&Plan> uses the null-pointer niche; absent plans impose no memory
observation and retained children are represented recursively when present. -/
inductive OptionPlanAt (m : DataMem) (r : SszX86.Codec.Footprint) :
    BitVec 64 → Option SszNative.CodecMeasure.Plan → Prop where
  | none : OptionPlanAt m r 0 none
  | some {p : BitVec 64} {plan : SszNative.CodecMeasure.Plan} :
      SszX86.Codec.PlanAt m r p plan → OptionPlanAt m r p (some plan)

theorem OptionPlanAt.frame {m n : DataMem} {r w : SszX86.Codec.Footprint}
    {p : BitVec 64} {plan : Option SszNative.CodecMeasure.Plan}
    (h : OptionPlanAt m r p plan) (frame : SszX86.Codec.MemoryFrame m n w)
    (apart : ∀ a, r a → ¬ w a) : OptionPlanAt n r p plan := by
  cases h with
  | none => exact .none
  | some stored => exact .some (stored.frame frame apart)

theorem OptionPlanAt.null_iff {m : DataMem} {r : SszX86.Codec.Footprint}
    {p : BitVec 64} {plan : Option SszNative.CodecMeasure.Plan}
    (h : OptionPlanAt m r p plan) : p = 0 ↔ plan = none := by
  cases h with
  | none => simp
  | some stored =>
    cases stored with
    | plan span bound slice size leading children =>
      have nonzero : p ≠ 0 := by
        intro zero
        have positive := span.nonnull
        simp only [zero, BitVec.toNat_zero] at positive
        omega
      simp only [nonzero, Option.some_ne_none]

private theorem slot_succ (p : BitVec 64) (stride index : Nat) :
    p + BitVec.ofNat 64 (stride * (index + 1)) =
      (p + BitVec.ofNat 64 stride) + BitVec.ofNat 64 (stride * index) := by
  rw [Nat.mul_succ, BitVec.ofNat_add]
  ac_rfl

/-- The native 48-byte value stride reaches the full recursive child storage,
not just a root tag. Readonly aliasing among children remains unrestricted. -/
theorem value_at_index {m : DataMem} {r : SszX86.Codec.Footprint}
    {p : BitVec 64} {values : List SszNative.Codec.Value}
    (h : SszX86.Codec.ValuesAt m r p values) (index : Nat)
    (value : SszNative.Codec.Value) (found : values[index]? = some value) :
    SszX86.Codec.ValueAt m r (p + BitVec.ofNat 64 (48 * index)) value := by
  induction index generalizing p values with
  | zero =>
    cases h with
    | valuesNil => simp at found
    | valuesCons first rest =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst value
      simpa only [Nat.mul_zero, BitVec.ofNat_zero, BitVec.add_zero] using first
  | succ index ih =>
    cases h with
    | valuesNil => simp at found
    | valuesCons first rest =>
      simp only [List.getElem?_cons_succ] at found
      rw [slot_succ]
      exact ih rest found

/-- Retained plans use their actual 40-byte array stride and retain the original
Nat representation, child slice, and leading usize observations. -/
theorem plan_at_index {m : DataMem} {r : SszX86.Codec.Footprint}
    {p : BitVec 64} {plans : List SszNative.CodecMeasure.Plan}
    (h : SszX86.Codec.PlansAt m r p plans) (index : Nat)
    (plan : SszNative.CodecMeasure.Plan) (found : plans[index]? = some plan) :
    SszX86.Codec.PlanAt m r (p + BitVec.ofNat 64 (40 * index)) plan := by
  induction index generalizing p plans with
  | zero =>
    cases h with
    | plansNil => simp at found
    | plansCons first rest =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst plan
      simpa only [Nat.mul_zero, BitVec.ofNat_zero, BitVec.add_zero] using first
  | succ index ih =>
    cases h with
    | plansNil => simp at found
    | plansCons first rest =>
      simp only [List.getElem?_cons_succ] at found
      rw [slot_succ]
      exact ih rest found

/-- Fields are indexed at stride 24, with the descriptor pointer at byte 16.
Names remain borrowed storage but are never interpreted by the emitter. -/
theorem field_at_index {m : DataMem} {r : SszX86.Codec.Footprint}
    {p : BitVec 64} {fields : List (String × SszNative.Codec.Desc)}
    (h : SszX86.Codec.FieldsAt m r p fields) (index : Nat)
    (name : String) (desc : SszNative.Codec.Desc)
    (found : fields[index]? = some (name, desc)) :
    ∃ child, SszX86.Codec.LoadAt m r (p + BitVec.ofNat 64 (24 * index) + 16)
        8 (child.toNat : Int) ∧ SszX86.Codec.DescAt m r child desc := by
  induction index generalizing p fields with
  | zero =>
    cases h with
    | fieldsNil => simp at found
    | fieldsCons span nameSlice nameBytes pointer descriptor rest =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
      rcases found with ⟨rfl, rfl⟩
      refine ⟨_, ?_, descriptor⟩
      simpa only [Nat.mul_zero, BitVec.ofNat_zero, BitVec.add_zero] using pointer
  | succ index ih =>
    cases h with
    | fieldsNil => simp at found
    | fieldsCons span nameSlice nameBytes pointer descriptor rest =>
      simp only [List.getElem?_cons_succ] at found
      rw [slot_succ]
      exact ih rest found

end SszX86.CodecEmitParts
