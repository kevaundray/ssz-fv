import SszCodecMeasure
import SszSerializeResources
import SszFixedSizeResources

set_option autoImplicit false

namespace SszNative.CodecMeasure

open Codec (Desc Value Error)

/-- A cursor never retreats; a valid caller arena remains valid, on errors too. -/
def CursorSafe (arena : Delimited.ArenaState) (used : Nat) : Prop :=
  arena.used ≤ used ∧
    (Arena.Valid arena.base arena.capacity arena.used →
      Arena.Valid arena.base arena.capacity used)

theorem cursorSafe_refl (arena : Delimited.ArenaState) : CursorSafe arena arena.used :=
  ⟨Nat.le_refl _, fun valid => valid⟩

theorem cursorSafe_trans (arena : Delimited.ArenaState) (middle used : Nat)
    (first : CursorSafe arena middle)
    (second : CursorSafe { arena with used := middle } used) : CursorSafe arena used :=
  ⟨Nat.le_trans first.1 second.1, fun valid => second.2 (first.2 valid)⟩

theorem reserve_cursorSafe (arena : Delimited.ArenaState) (words : Nat)
    (reservation : Arena.Reservation)
    (reserved : Arena.reserve arena.base arena.capacity arena.used words = some reservation) :
    CursorSafe arena reservation.used := by
  refine ⟨?_, fun valid => Arena.valid_after_success _ _ _ _ valid reservation reserved⟩
  by_cases zero : words = 0
  · subst words
    rw [(Arena.reserve_zero_properties _ _ _ reservation reserved).2.2.2]
    exact Nat.le_refl _
  · obtain ⟨_, shape⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega) reservation).1 reserved
    rw [shape]
    have start := Arena.used_le_start arena.base arena.used
    dsimp only [Arena.finish]
    omega

theorem bind_cursorSafe {α β : Type} (arena : Delimited.ArenaState)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (safeFirst : CursorSafe arena first.used)
    (safeNext : ∀ value used, CursorSafe { arena with used := used } (next value used).used) :
    CursorSafe arena (bind first next).used := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using safeFirst
  | ok value =>
    simpa only [bind, result] using
      cursorSafe_trans arena first.used _ safeFirst (safeNext value first.used)

private theorem serialize_bind_cursorSafe {α β : Type} (arena : Delimited.ArenaState)
    (first : Serialize.Outcome α) (next : α → Nat → Serialize.Outcome β)
    (safeFirst : CursorSafe arena first.used)
    (safeNext : ∀ value used, CursorSafe { arena with used := used } (next value used).used) :
    CursorSafe arena (Serialize.bind first next).used := by
  cases result : first.result with
  | error reason => simpa only [Serialize.bind, result] using safeFirst
  | ok value =>
    simpa only [Serialize.bind, result] using
      cursorSafe_trans arena first.used _ safeFirst (safeNext value first.used)

private theorem fromWide_cursorSafe (arena : Delimited.ArenaState) (wide : BitVec 128) :
    CursorSafe arena (Serialize.fromWide arena wide).used := by
  unfold Serialize.fromWide NatArithmetic.fromWide
  split
  · exact cursorSafe_refl arena
  · split
    · exact cursorSafe_refl arena
    · rename_i reservation reserved
      exact reserve_cursorSafe arena 2 reservation reserved

private theorem serialize_bounded_cursorSafe (arena : Delimited.ArenaState)
    (limit : Option NatOperand) (actual : NatOperand) :
    CursorSafe arena (Serialize.bounded limit actual arena.used).used := by
  rw [(Serialize.bounded_resources limit actual arena.used).1]
  exact cursorSafe_refl arena

private theorem serialize_measureList_cursorSafe (limit : Option NatOperand)
    (bits : Serialize.Packed) (arena : Delimited.ArenaState) :
    CursorSafe arena (Serialize.measureList limit bits arena).used := by
  unfold Serialize.measureList
  apply serialize_bind_cursorSafe _ _ _ (fromWide_cursorSafe arena bits.count)
  intro actual used
  apply serialize_bind_cursorSafe _ _ _
    (serialize_bounded_cursorSafe { arena with used := used } limit actual)
  intro _checked used
  exact fromWide_cursorSafe { arena with used := used } _

theorem primitive_cursorSafe (shape : Serialize.Desc) (value : Value)
    (arena : Delimited.ArenaState) : CursorSafe arena (primitive shape value arena).used := by
  change CursorSafe arena (Serialize.measure shape value.toPrimitive arena).used
  generalize value.toPrimitive = actual
  cases shape <;> cases actual <;> simp only [Serialize.measure]
  all_goals first
    | exact cursorSafe_refl arena
    | exact serialize_measureList_cursorSafe _ _ arena
    | (split <;> exact cursorSafe_refl arena)
    | (apply serialize_bind_cursorSafe _ _ _ (serialize_bounded_cursorSafe arena _ _)
       intro _checked used
       exact cursorSafe_refl { arena with used := used })
    | (split
       · exact cursorSafe_refl arena
       · apply serialize_bind_cursorSafe _ _ _ (fromWide_cursorSafe arena _)
         intro actual used
         exact cursorSafe_refl { arena with used := used })

theorem add_cursorSafe (left right : NatOperand) (arena : Delimited.ArenaState) :
    CursorSafe arena (add left right arena).used := by
  refine ⟨FixedSize.add_used_mono left right arena, ?_⟩
  intro valid
  change Arena.Valid arena.base arena.capacity
    (NatAdd.run left right arena.base arena.capacity arena.used).used
  cases allocated : (NatAdd.run left right arena.base arena.capacity arena.used).allocation with
  | none =>
    rw [(NatAdd.no_allocation_resources _ _ _ _ _ allocated).1]
    exact valid
  | some reservation =>
    obtain ⟨cursor, _, branches⟩ := NatAdd.allocation_exact _ _ _ _ _ reservation allocated
    rw [cursor]
    rcases branches with small | large
    · exact Arena.valid_after_success _ _ _ _ valid reservation small.2.2.2.1
    · exact Arena.valid_after_success _ _ _ _ valid reservation large.2.2.1

theorem exactCount_resources (expected : NatOperand) (actual used : Nat) :
    (exactCount expected actual used).used = used ∧ (exactCount expected actual used).effects = [] := by
  unfold exactCount
  split <;> exact ⟨rfl, rfl⟩

theorem bounded_resources (limit : Option NatOperand) (actual : NatOperand) (used : Nat) :
    (bounded limit actual used).used = used ∧ (bounded limit actual used).effects = [] :=
  ⟨(Serialize.bounded_resources limit actual used).1, rfl⟩

theorem hostSize_resources (size : NatOperand) (used : Nat) :
    (hostSize size used).used = used ∧ (hostSize size used).effects = [] := by
  unfold hostSize Serialize.hostSize
  split <;> exact ⟨rfl, rfl⟩

theorem compositeSize_resources (size : NatOperand) (used : Nat) :
    (compositeSize size used).used = used ∧ (compositeSize size used).effects = [] := by
  unfold compositeSize
  split <;> exact ⟨rfl, rfl⟩

theorem reservePlans_cursorSafe (count : Nat) (arena : Delimited.ArenaState) :
    CursorSafe arena (reservePlans count arena).used := by
  unfold reservePlans
  dsimp only
  split
  · exact cursorSafe_refl arena
  · rename_i reservation reserved
    exact reserve_cursorSafe arena (5 * count) reservation reserved

theorem writePlan_used (allocation : Option Arena.Reservation) (index : Nat)
    (plan : Plan) (used : Nat) : (writePlan allocation index plan used).used = used := by
  cases allocation <;> rfl

theorem accumulate_cursorSafe (inline : Bool) (child : Plan) (totals : Partial)
    (arena : Delimited.ArenaState) : CursorSafe arena (accumulate inline child totals arena).used := by
  unfold accumulate
  apply bind_cursorSafe _ _ _ (add_cursorSafe _ _ arena)
  intro leading used
  split
  · exact cursorSafe_refl { arena with used := used }
  · apply bind_cursorSafe _ _ _ (add_cursorSafe _ _ { arena with used := used })
    intro bodies used
    exact cursorSafe_refl { arena with used := used }

/-- Callback induction includes every raw schema and every child result. -/
theorem measureLoop_cursorSafe (parts : Parts) (values : List Value) (visit : Visit values)
    (keep : Bool) (allocation : Option Arena.Reservation) (index : Nat)
    (totals : Partial) (arena : Delimited.ArenaState)
    (safeVisit : ∀ value member desc arena keep,
      CursorSafe arena (visit value member desc arena keep).used) :
    CursorSafe arena (measureLoop parts values visit keep allocation index totals arena).used := by
  induction values generalizing parts index totals arena with
  | nil =>
    rw [measureLoop]
    exact cursorSafe_refl arena
  | cons value rest ih =>
    cases parts with
    | repeated element =>
      simp only [measureLoop]
      apply bind_cursorSafe _ _ _ (safeVisit value _ element arena keep)
      intro child used
      apply bind_cursorSafe _ _ _ (accumulate_cursorSafe _ _ _ { arena with used := used })
      intro next used
      apply bind_cursorSafe _ _ _
        (by rw [writePlan_used]; exact cursorSafe_refl { arena with used := used })
      intro _checked used
      apply ih
      intro value member desc arena keep
      exact safeVisit value (List.mem_cons_of_mem _ member) desc arena keep
    | fields fields =>
      cases fields with
      | nil =>
        rw [measureLoop]
        exact cursorSafe_refl arena
      | cons field fields =>
        rcases field with ⟨name, desc⟩
        simp only [measureLoop]
        apply bind_cursorSafe _ _ _ (safeVisit value _ desc arena keep)
        intro child used
        apply bind_cursorSafe _ _ _ (accumulate_cursorSafe _ _ _ { arena with used := used })
        intro next used
        apply bind_cursorSafe _ _ _
          (by rw [writePlan_used]; exact cursorSafe_refl { arena with used := used })
        intro _checked used
        apply ih
        intro value member desc arena keep
        exact safeVisit value (List.mem_cons_of_mem _ member) desc arena keep

theorem finishParts_cursorSafe (parts : Parts) (values : List Value) (totals : Partial)
    (allocation : Option Arena.Reservation) (arena : Delimited.ArenaState) :
    CursorSafe arena (finishParts parts values totals allocation arena).used := by
  unfold finishParts
  split
  · apply bind_cursorSafe _ _ _ (add_cursorSafe _ _ arena)
    intro size used
    apply bind_cursorSafe _ _ _
      (by rw [(compositeSize_resources size used).1]; exact cursorSafe_refl _)
    intro _checked used
    apply bind_cursorSafe _ _ _
      (by rw [(hostSize_resources totals.leading used).1]; exact cursorSafe_refl _)
    intro leading used
    exact cursorSafe_refl _
  · exact cursorSafe_refl arena

theorem measureParts_cursorSafe (parts : Parts) (values : List Value) (visit : Visit values)
    (arena : Delimited.ArenaState) (retain : Bool)
    (safeVisit : ∀ value member desc arena keep,
      CursorSafe arena (visit value member desc arena keep).used) :
    CursorSafe arena (measureParts parts values visit arena retain).used := by
  unfold measureParts
  dsimp only
  split
  · apply bind_cursorSafe _ _ _ (reservePlans_cursorSafe _ arena)
    intro allocation used
    apply bind_cursorSafe _ _ _ (measureLoop_cursorSafe _ _ _ _ _ _ _ _ safeVisit)
    intro totals used
    exact finishParts_cursorSafe _ _ _ _ _
  · apply bind_cursorSafe _ _ _ (measureLoop_cursorSafe _ _ _ _ _ _ _ _ safeVisit)
    intro totals used
    exact finishParts_cursorSafe _ _ _ _ _

theorem unionPlan_cursorSafe (child : Plan) (arena : Delimited.ArenaState) (retain : Bool) :
    CursorSafe arena (unionPlan child arena retain).used := by
  unfold unionPlan
  apply bind_cursorSafe _ _ _ (add_cursorSafe _ _ arena)
  intro size used
  split
  · apply bind_cursorSafe _ _ _ (reservePlans_cursorSafe _ { arena with used := used })
    intro allocation used
    apply bind_cursorSafe _ _ _
      (by rw [writePlan_used]; exact cursorSafe_refl { arena with used := used })
    intro _checked used
    exact cursorSafe_refl _
  · exact cursorSafe_refl _

theorem measureStep_cursorSafe (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) (visit : Visit value.children)
    (safeVisit : ∀ child member desc arena keep,
      CursorSafe arena (visit child member desc arena keep).used) :
    CursorSafe arena (measureStep desc value arena retain visit).used := by
  cases desc <;> cases value <;> simp only [measureStep]
  all_goals first
    | exact primitive_cursorSafe _ _ arena
    | exact cursorSafe_refl arena
    | exact measureParts_cursorSafe _ _ _ _ _ safeVisit
    | (apply bind_cursorSafe _ _ _
         (by rw [(exactCount_resources _ _ _).1]; exact cursorSafe_refl arena)
       intro _checked used
       exact measureParts_cursorSafe _ _ _ _ _ safeVisit)
    | (apply bind_cursorSafe _ _ _
         (by rw [(bounded_resources _ _ _).1]; exact cursorSafe_refl arena)
       intro _checked used
       exact measureParts_cursorSafe _ _ _ _ _ safeVisit)
    | (apply bind_cursorSafe _ _ _ (cursorSafe_refl arena)
       intro chosen used
       apply bind_cursorSafe _ _ _ (safeVisit _ _ chosen { arena with used := used } retain)
       intro child used
       exact unionPlan_cursorSafe child { arena with used := used } retain)

/-- Full recursive resource safety, with no success or physical-value premise. -/
theorem measure_cursorSafe (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) : CursorSafe arena (measure desc value arena retain).used := by
  rw [measure]
  apply measureStep_cursorSafe
  intro child _member desc arena keep
  exact measure_cursorSafe desc child arena keep
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

theorem measure_used_mono (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) : arena.used ≤ (measure desc value arena retain).used :=
  (measure_cursorSafe desc value arena retain).1

theorem measure_valid (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) (valid : Arena.Valid arena.base arena.capacity arena.used) :
    Arena.Valid arena.base arena.capacity (measure desc value arena retain).used :=
  (measure_cursorSafe desc value arena retain).2 valid

theorem measure_used_le_capacity (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) (valid : Arena.Valid arena.base arena.capacity arena.used) :
    (measure desc value arena retain).used ≤ arena.capacity :=
  (measure_valid desc value arena retain valid).2.2.2

/-- Host narrowing adds no effects or cursor movement, including rejection. -/
theorem encodedSize_resources (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    (encodedSize desc value arena).used = (measure desc value arena false).used ∧
      (encodedSize desc value arena).effects = (measure desc value arena false).effects := by
  cases measured : (measure desc value arena false).result with
  | error reason => simp only [encodedSize, bind, measured, and_self]
  | ok plan =>
    simp only [encodedSize, bind, measured, (hostSize_resources plan.size _).1,
      (hostSize_resources plan.size _).2, List.append_nil, and_self]

theorem encodedSize_cursorSafe (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    CursorSafe arena (encodedSize desc value arena).used := by
  rw [(encodedSize_resources desc value arena).1]
  exact measure_cursorSafe desc value arena false

theorem encodedSize_used_mono (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    arena.used ≤ (encodedSize desc value arena).used :=
  (encodedSize_cursorSafe desc value arena).1

theorem encodedSize_valid (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (valid : Arena.Valid arena.base arena.capacity arena.used) :
    Arena.Valid arena.base arena.capacity (encodedSize desc value arena).used :=
  (encodedSize_cursorSafe desc value arena).2 valid

theorem encodedSize_used_le_capacity (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (valid : Arena.Valid arena.base arena.capacity arena.used) :
    (encodedSize desc value arena).used ≤ arena.capacity :=
  (encodedSize_valid desc value arena valid).2.2.2

end SszNative.CodecMeasure
