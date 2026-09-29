import SszCodecDecodeResourcesCore

set_option autoImplicit false

namespace SszNative.CodecDecode


theorem bind_used_eq {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (used : Nat) (same : first.used = used)
    (nextSame : ∀ value cursor, (next value cursor).used = cursor) :
    (bind first next).used = used := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using same
  | ok value => simpa only [bind, result, nextSame] using same
open Codec (Desc)

theorem decodeWindows_cursorSafe (visit : Input → Delimited.ArenaState → Outcome Node)
    (windows : List Window) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState)
    (safeVisit : ∀ input arena, CursorSafe arena (visit input arena).used) :
    CursorSafe arena (decodeWindows visit windows input allocation index arena).used := by
  induction windows generalizing index arena with
  | nil => exact cursorSafe_refl arena
  | cons window rest ih =>
    rw [decodeWindows]
    apply bind_cursorSafe _ _ _ (safeVisit _ arena)
    intro child used
    apply bind_cursorSafe _ _ _ (cursorSafe_refl _)
    intro checked used
    apply bind_cursorSafe _ _ _ (ih _ _)
    intro children used
    exact cursorSafe_refl _

theorem decodeArray_cursorSafe (visit : Input → Delimited.ArenaState → Outcome Node)
    (windows : List Window) (input : Input) (arena : Delimited.ArenaState)
    (safeVisit : ∀ input arena, CursorSafe arena (visit input arena).used) :
    CursorSafe arena (decodeArray visit windows input arena).used := by
  unfold decodeArray
  apply bind_cursorSafe _ _ _ (reserve_cursorSafe _ _ arena)
  intro allocation used
  apply bind_cursorSafe _ _ _ (decodeWindows_cursorSafe _ _ _ _ _ _ safeVisit)
  intro children used
  exact cursorSafe_refl _

theorem decodeFixed_cursorSafe (visit : Input → Delimited.ArenaState → Outcome Node)
    (count width : Nat) (input : Input) (arena : Delimited.ArenaState)
    (safeVisit : ∀ input arena, CursorSafe arena (visit input arena).used) :
    CursorSafe arena (decodeFixed visit count width input arena).used := by
  rw [decodeFixed_eq_decodeArray]
  exact decodeArray_cursorSafe _ _ _ _ safeVisit

theorem decodeOffsets_cursorSafe (visit : Input → Delimited.ArenaState → Outcome Node)
    (count : Nat) (input : Input) (arena : Delimited.ArenaState)
    (safeVisit : ∀ input arena, CursorSafe arena (visit input arena).used) :
    CursorSafe arena (decodeOffsets visit count input arena).used := by
  unfold decodeOffsets
  apply bind_cursorSafe _ _ _ (cursorSafe_refl arena)
  intro checked used
  exact decodeArray_cursorSafe _ _ _ _ safeVisit

theorem vector_cursorSafe (element : Desc) (length : NatOperand)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (input : Input) (arena : Delimited.ArenaState)
    (safeVisit : ∀ input arena, CursorSafe arena (visit input arena).used) :
    CursorSafe arena (vector element length visit input arena).used := by
  unfold vector
  apply bind_cursorSafe _ _ _
    (by rw [(compositeSize_resources _ _).1]; exact cursorSafe_refl arena)
  intro checked used
  apply bind_cursorSafe _ _ _ (fixedSize_cursorSafe _ _)
  intro width used
  cases width with
  | some width =>
    apply bind_cursorSafe _ _ _ (mul_cursorSafe _ _ _)
    intro expected used
    apply bind_cursorSafe _ _ _
      (by rw [(exact_resources _ _ _).1]; exact cursorSafe_refl _)
    intro checked used
    split
    · exact cursorSafe_refl _
    · apply bind_cursorSafe _ _ _
        (by rw [(narrow_resources _ _ _).1]; exact cursorSafe_refl _)
      intro count used
      apply bind_cursorSafe _ _ _
        (by rw [(narrow_resources _ _ _).1]; exact cursorSafe_refl _)
      intro width used
      exact decodeFixed_cursorSafe _ _ _ _ _ safeVisit
  | none =>
    apply bind_cursorSafe _ _ _ (mul_cursorSafe _ _ _)
    intro leading used
    split
    · exact cursorSafe_refl _
    · split
      · exact cursorSafe_refl _
      · apply bind_cursorSafe _ _ _
          (by rw [(narrow_resources _ _ _).1]; exact cursorSafe_refl _)
        intro count used
        dsimp only
        split
        · exact cursorSafe_refl _
        · exact decodeOffsets_cursorSafe _ _ _ _ safeVisit

theorem list_cursorSafe (element : Desc) (limit : Option NatOperand)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (input : Input) (arena : Delimited.ArenaState)
    (safeVisit : ∀ input arena, CursorSafe arena (visit input arena).used) :
    CursorSafe arena (list element limit visit input arena).used := by
  unfold list
  apply bind_cursorSafe _ _ _
    (by rw [(compositeSize_resources _ _).1]; exact cursorSafe_refl arena)
  intro checked used
  split
  · exact cursorSafe_refl _
  · apply bind_cursorSafe _ _ _ (fixedSize_cursorSafe _ _)
    intro width used
    cases width with
    | some width =>
      dsimp only
      split
      · exact cursorSafe_refl _
      · split
        · exact cursorSafe_refl _
        · apply bind_cursorSafe _ _ _
            (by rw [(narrow_resources _ _ _).1]; exact cursorSafe_refl _)
          intro width used
          split
          · exact cursorSafe_refl _
          · apply bind_cursorSafe _ _ _
              (by rw [(bounded_resources _ _ _).1]; exact cursorSafe_refl _)
            intro checked used
            exact decodeFixed_cursorSafe _ _ _ _ _ safeVisit
    | none =>
      dsimp only
      split
      · exact cursorSafe_refl _
      · split
        · exact cursorSafe_refl _
        · split
          · exact cursorSafe_refl _
          · split
            · exact cursorSafe_refl _
            · apply bind_cursorSafe _ _ _
                (by rw [(bounded_resources _ _ _).1]; exact cursorSafe_refl _)
              intro checked used
              exact decodeOffsets_cursorSafe _ _ _ _ safeVisit

theorem measureSlots_cursorSafe {children : List Desc} (entries : List (Entry children))
    (allocation : Arena.Reservation) (index : Nat) (leading : NatOperand) (allFixed : Bool)
    (arena : Delimited.ArenaState) :
    CursorSafe arena (measureSlots entries allocation index leading allFixed arena).used := by
  induction entries generalizing index leading allFixed arena with
  | nil => exact cursorSafe_refl arena
  | cons entry rest ih =>
    rw [measureSlots]
    apply bind_cursorSafe _ _ _ (fixedSize_cursorSafe _ _)
    intro width used
    apply bind_cursorSafe _ _ _ (cursorSafe_refl _)
    intro checked used
    apply bind_cursorSafe _ _ _ (add_cursorSafe _ _ _)
    intro leading used
    apply bind_cursorSafe _ _ _ (ih _ _ _ _)
    intro measured used
    exact cursorSafe_refl _

theorem positionSlots_used {children : List Desc} (entries : List (Entry children))
    (input : Input) (allocation : Arena.Reservation) (index position used : Nat) :
    (positionSlots entries input allocation index position used).used = used := by
  induction entries generalizing index position used with
  | nil => rfl
  | cons entry rest ih =>
    rw [positionSlots]
    have widthUsed : (match entry.slot.width with
        | none => unchanged used (.ok 4)
        | some width => narrow width .truncated used).used = used := by
      cases entry.slot.width
      · rfl
      · exact (narrow_resources _ _ _).1
    apply bind_used_eq _ _ _ widthUsed
    intro width cursor
    dsimp only
    split
    · rfl
    · apply bind_used_eq _ _ _ rfl
      intro checked cursor
      apply bind_used_eq _ _ _ (ih _ _ _)
      intro result cursor
      rfl

theorem validateSlots_used {children : List Desc} (entries : List (Entry children))
    (allocation : Arena.Reservation) (index leading scope : Nat)
    (previous : Option (Nat × Slot)) (used : Nat) :
    (validateSlots entries allocation index leading scope previous used).used = used := by
  induction entries generalizing index previous used with
  | nil =>
    rw [validateSlots.eq_def]
    cases previous with
    | none => exact (exact_resources _ _ _).1
    | some previous =>
      rcases previous with ⟨previousIndex, slot⟩
      dsimp only
      split <;> rfl
  | cons entry rest ih =>
    rw [validateSlots.eq_def]
    cases width : entry.slot.width with
    | some value =>
      simp only [width]
      exact ih _ _ _
    | none =>
      simp only [width]
      cases previous with
      | none =>
        dsimp only
        split
        · rfl
        · exact ih _ _ _
      | some previous =>
        rcases previous with ⟨previousIndex, previousSlot⟩
        dsimp only
        split
        · rfl
        · simpa only [bind, writeSlot] using ih (index + 1) (some (index, entry.slot)) used

theorem decodeEntries_cursorSafe {children : List Desc} (entries : List (Entry children))
    (visit : Visit children) (input : Input) (allocation : Arena.Reservation) (index : Nat)
    (arena : Delimited.ArenaState)
    (safeVisit : ∀ child member input arena, CursorSafe arena (visit child member input arena).used) :
    CursorSafe arena (decodeEntries entries visit input allocation index arena).used := by
  induction entries generalizing index arena with
  | nil => exact cursorSafe_refl arena
  | cons entry rest ih =>
    rw [decodeEntries]
    apply bind_cursorSafe _ _ _ (safeVisit _ _ _ _)
    intro child used
    apply bind_cursorSafe _ _ _ (cursorSafe_refl _)
    intro checked used
    apply bind_cursorSafe _ _ _ (ih _ _)
    intro decoded used
    exact cursorSafe_refl _

theorem structureValue_cursorSafe (children : List Desc) (visit : Visit children)
    (input : Input) (arena : Delimited.ArenaState)
    (safeVisit : ∀ child member input arena, CursorSafe arena (visit child member input arena).used) :
    CursorSafe arena (structureValue children visit input arena).used := by
  unfold structureValue
  apply bind_cursorSafe _ _ _
    (by rw [(compositeSize_resources _ _).1]; exact cursorSafe_refl arena)
  intro checked used
  apply bind_cursorSafe _ _ _ (reserve_cursorSafe _ _ _)
  intro slots used
  apply bind_cursorSafe _ _ _ (cursorSafe_refl _)
  intro checked used
  apply bind_cursorSafe _ _ _ (measureSlots_cursorSafe _ _ _ _ _ _)
  intro measured used
  dsimp only
  refine bind_cursorSafe _ _ _ ?_ ?_
  · split
    · rw [(exact_resources _ _ _).1]
      exact cursorSafe_refl _
    · split <;> exact cursorSafe_refl _
  · intro checked used
    apply bind_cursorSafe _ _ _
      (by rw [positionSlots_used]; exact cursorSafe_refl _)
    intro positioned used
    apply bind_cursorSafe _ _ _
      (by rw [validateSlots_used]; exact cursorSafe_refl _)
    intro checked used
    apply bind_cursorSafe _ _ _ (reserve_cursorSafe _ _ _)
    intro values used
    apply bind_cursorSafe _ _ _ (decodeEntries_cursorSafe _ _ _ _ _ _ safeVisit)
    intro decoded used
    exact cursorSafe_refl _

theorem unionOption_cursorSafe (variants : List (NatOperand × Desc))
    (visit : Visit (variants.map Prod.snd)) (selector : NatOperand)
    (input : Input) (arena : Delimited.ArenaState)
    (safeVisit : ∀ child member input arena, CursorSafe arena (visit child member input arena).used) :
    CursorSafe arena (unionOption variants visit selector input arena).used := by
  induction variants generalizing arena with
  | nil => exact cursorSafe_refl arena
  | cons variant rest ih =>
    rcases variant with ⟨chosen, desc⟩
    rw [unionOption]
    split
    · apply bind_cursorSafe _ _ _ (safeVisit _ _ _ _)
      intro child used
      apply bind_cursorSafe _ _ _ (reserve_cursorSafe _ _ _)
      intro allocation used
      apply bind_cursorSafe _ _ _ (cursorSafe_refl _)
      intro checked used
      exact cursorSafe_refl _
    · apply ih
      intro child member input arena
      exact safeVisit _ _ _ _

theorem decodeStep_cursorSafe (desc : Desc) (input : Input) (arena : Delimited.ArenaState)
    (visit : Visit desc.children)
    (safeVisit : ∀ child member input arena, CursorSafe arena (visit child member input arena).used) :
    CursorSafe arena (decodeStep desc input arena visit).used := by
  cases desc with
  | primitive shape => exact primitive_cursorSafe shape input arena
  | vector element length =>
    exact vector_cursorSafe _ _ _ _ _ (safeVisit element _)
  | list element limit =>
    exact list_cursorSafe _ _ _ _ _ (safeVisit element _)
  | progressiveList element limit =>
    exact list_cursorSafe _ _ _ _ _ (safeVisit element _)
  | container fields => exact structureValue_cursorSafe _ _ _ _ safeVisit
  | progressiveContainer active fields => exact structureValue_cursorSafe _ _ _ _ safeVisit
  | compatibleUnion variants =>
    dsimp only [decodeStep]
    split
    · exact cursorSafe_refl arena
    · exact unionOption_cursorSafe _ _ _ _ _ safeVisit

/-- Every raw descriptor and every error branch retain committed resources.
No schema, successful future execution, or physical-input premise is required. -/
theorem decode_cursorSafe (desc : Desc) (input : Input) (arena : Delimited.ArenaState) :
    CursorSafe arena (decode desc input arena).used := by
  rw [decode]
  apply decodeStep_cursorSafe
  intro child member input arena
  exact decode_cursorSafe child input arena
termination_by desc.nesting
decreasing_by exact Desc.child_nesting_lt _ _ (by assumption)

theorem decode_used_mono (desc : Desc) (input : Input) (arena : Delimited.ArenaState) :
    arena.used ≤ (decode desc input arena).used :=
  (decode_cursorSafe desc input arena).1

theorem decode_valid (desc : Desc) (input : Input) (arena : Delimited.ArenaState)
    (valid : Arena.Valid arena.base arena.capacity arena.used) :
    Arena.Valid arena.base arena.capacity (decode desc input arena).used :=
  (decode_cursorSafe desc input arena).2 valid

theorem decode_used_le_capacity (desc : Desc) (input : Input) (arena : Delimited.ArenaState)
    (valid : Arena.Valid arena.base arena.capacity arena.used) :
    (decode desc input arena).used ≤ arena.capacity :=
  (decode_valid desc input arena valid).2.2.2

theorem run_cursorSafe (desc : Desc) (bytes : Ssz.Bytes) (arena : Delimited.ArenaState) :
    CursorSafe arena (run desc bytes arena).used := decode_cursorSafe desc ⟨0, bytes⟩ arena

theorem run_used_mono (desc : Desc) (bytes : Ssz.Bytes) (arena : Delimited.ArenaState) :
    arena.used ≤ (run desc bytes arena).used := (run_cursorSafe desc bytes arena).1

theorem run_valid (desc : Desc) (bytes : Ssz.Bytes) (arena : Delimited.ArenaState)
    (valid : Arena.Valid arena.base arena.capacity arena.used) :
    Arena.Valid arena.base arena.capacity (run desc bytes arena).used :=
  (run_cursorSafe desc bytes arena).2 valid

theorem run_used_le_capacity (desc : Desc) (bytes : Ssz.Bytes) (arena : Delimited.ArenaState)
    (valid : Arena.Valid arena.base arena.capacity arena.used) :
    (run desc bytes arena).used ≤ arena.capacity := (run_valid desc bytes arena valid).2.2.2

end SszNative.CodecDecode
