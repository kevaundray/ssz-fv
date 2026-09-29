import SszCodecDecodeResourcesWrites

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc)

/-- All logical Value stores are above a cursor. Arithmetic limb and Slot events
have their own typed payloads and are not Value initializers. -/
def WritesAbove (floor : Nat) (effects : List Effect) : Prop :=
  ∀ address index node, Effect.writeValue address index node ∈ effects → floor ≤ address

def NoValueWrites (effects : List Effect) : Prop := ∀ floor, WritesAbove floor effects

theorem writesAbove_nil (floor : Nat) : WritesAbove floor [] := by
  intro address index node member
  cases member

theorem writesAbove_append (floor : Nat) (first second : List Effect)
    (left : WritesAbove floor first) (right : WritesAbove floor second) :
    WritesAbove floor (first ++ second) := by
  intro address index node member
  rcases List.mem_append.mp member with member | member
  · exact left _ _ _ member
  · exact right _ _ _ member

theorem writesAbove_mono {lower upper : Nat} {effects : List Effect}
    (bound : lower ≤ upper) (writes : WritesAbove upper effects) : WritesAbove lower effects := by
  intro address index node member
  exact Nat.le_trans bound (writes _ _ _ member)

theorem bind_writesAbove {α β : Type} (floor : Nat) (first : Outcome α)
    (next : α → Nat → Outcome β) (firstWrites : WritesAbove floor first.effects)
    (nextWrites : ∀ value, first.result = .ok value →
      WritesAbove floor (next value first.used).effects) :
    WritesAbove floor (bind first next).effects := by
  cases returned : first.result with
  | error reason => simpa only [bind, returned] using firstWrites
  | ok value =>
    simpa only [bind, returned] using
      writesAbove_append floor _ _ firstWrites (nextWrites value returned)

theorem bind_noValueWrites {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (firstWrites : NoValueWrites first.effects)
    (nextWrites : ∀ value used, NoValueWrites (next value used).effects) :
    NoValueWrites (bind first next).effects := by
  intro floor
  exact bind_writesAbove floor first next (firstWrites floor)
    (fun value _ => nextWrites value first.used floor)

theorem bind_return_effects {α β : Type} (first : Outcome α) (f : α → β) :
    (bind first (fun value used => unchanged used (.ok (f value)))).effects = first.effects := by
  cases returned : first.result <;> simp only [bind, returned, unchanged, List.append_nil]

theorem writeValue_bind_effects {α : Type} (allocation : Arena.Reservation)
    (index : Nat) (node : Node) (used : Nat) (next : Unit → Nat → Outcome α) :
    (bind (writeValue allocation index node used) next).effects =
      [.writeValue (allocation.pointer + valueLayout.size * index) index node] ++
        (next () used).effects := rfl

theorem reserve_noValueWrites (layout : TypedArena.Layout) (count : Nat)
    (arena : Delimited.ArenaState) : NoValueWrites (reserve layout count arena).effects := by
  intro floor address index node member
  unfold reserve at member
  dsimp only at member
  split at member <;> cases List.mem_singleton.mp member

theorem fixedSize_noValueWrites (desc : Desc) (arena : Delimited.ArenaState) :
    NoValueWrites (fixedSize desc arena).effects := by
  intro floor address index node member
  cases List.mem_singleton.mp member

theorem add_noValueWrites (left right : NatOperand) (arena : Delimited.ArenaState) :
    NoValueWrites (add left right arena).effects := by
  intro floor address index node member
  cases List.mem_singleton.mp member

theorem mul_noValueWrites (left right : NatOperand) (arena : Delimited.ArenaState) :
    NoValueWrites (mul left right arena).effects := by
  intro floor address index node member
  cases List.mem_singleton.mp member

theorem writeSlot_noValueWrites (allocation : Arena.Reservation) (index : Nat)
    (slot : Slot) (used : Nat) : NoValueWrites (writeSlot allocation index slot used).effects := by
  intro floor address target node member
  cases List.mem_singleton.mp member

theorem unsigned_noValueWrites (input : Input) (arena : Delimited.ArenaState) :
    NoValueWrites (unsigned input arena).effects := by
  intro floor address index node member
  unfold unsigned at member
  dsimp only at member
  split at member
  · cases List.mem_singleton.mp member
  · split at member <;> cases List.mem_singleton.mp member

theorem primitive_noValueWrites (shape : Serialize.Desc) (input : Input)
    (arena : Delimited.ArenaState) : NoValueWrites (primitive shape input arena).effects := by
  cases shape with
  | bool =>
    unfold primitive
    apply bind_noValueWrites
    · rw [(exact_resources _ _ _).2]
      exact writesAbove_nil
    · intro checked used
      dsimp only
      split
      · exact writesAbove_nil
      · split <;> exact writesAbove_nil
  | uint width =>
    unfold primitive
    apply bind_noValueWrites
    · rw [(exact_resources _ _ _).2]
      exact writesAbove_nil
    · intro checked used
      exact unsigned_noValueWrites _ _
  | byteVector length =>
    unfold primitive
    apply bind_noValueWrites
    · rw [(exact_resources _ _ _).2]
      exact writesAbove_nil
    · intro checked used
      exact writesAbove_nil
  | byteList limit =>
    unfold primitive
    apply bind_noValueWrites
    · rw [(bounded_resources _ _ _).2]
      exact writesAbove_nil
    · intro checked used
      exact writesAbove_nil
  | bitVector length =>
    unfold primitive bitVector
    apply bind_noValueWrites
    · intro floor address index node member
      cases List.mem_singleton.mp member
    · intro count used
      rw [(packed_resources _ _ _ _).2]
      exact writesAbove_nil
  | bitList limit =>
    intro floor address index node member
    cases List.mem_singleton.mp member
  | progressiveBitList limit =>
    intro floor address index node member
    cases List.mem_singleton.mp member

def FreshWrites {α : Type} (arena : Delimited.ArenaState) (outcome : Outcome α) : Prop :=
  WritesAbove (arena.base + arena.used) outcome.effects

theorem bind_freshWrites {α β : Type} (arena : Delimited.ArenaState)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (safeFirst : CursorSafe arena first.used) (firstWrites : FreshWrites arena first)
    (nextWrites : ∀ value, first.result = .ok value →
      FreshWrites { arena with used := first.used } (next value first.used)) :
    FreshWrites arena (bind first next) := by
  apply bind_writesAbove _ _ _ firstWrites
  intro value returned
  exact writesAbove_mono (Nat.add_le_add_left safeFirst.1 arena.base) (nextWrites value returned)

theorem bind_freshWrites_all {α β : Type} (arena : Delimited.ArenaState)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (safeFirst : CursorSafe arena first.used) (firstWrites : FreshWrites arena first)
    (nextWrites : ∀ value used, FreshWrites { arena with used := used } (next value used)) :
    FreshWrites arena (bind first next) :=
  bind_freshWrites arena first next safeFirst firstWrites
    (fun value _ => nextWrites value first.used)

theorem reserve_success (layout : TypedArena.Layout) (count : Nat) (arena : Delimited.ArenaState)
    (allocation : Arena.Reservation) (success : (reserve layout count arena).result = .ok allocation) :
    TypedArena.reserve layout arena.base arena.capacity arena.used count = some allocation ∧
      (reserve layout count arena).used = allocation.used := by
  unfold reserve at success ⊢
  dsimp only at success ⊢
  split at success
  · cases success
  · rename_i found reserved
    cases success
    simp only [reserved, and_self]

theorem decodeWindows_writesAbove (visit : Input → Delimited.ArenaState → Outcome Node)
    (windows : List Window) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState) (floor : Nat)
    (pointer : floor ≤ allocation.pointer) (cursor : floor ≤ arena.base + arena.used)
    (safeVisit : ∀ input arena, CursorSafe arena (visit input arena).used)
    (freshVisit : ∀ input arena, FreshWrites arena (visit input arena)) :
    WritesAbove floor (decodeWindows visit windows input allocation index arena).effects := by
  induction windows generalizing index arena with
  | nil => exact writesAbove_nil floor
  | cons window rest ih =>
    rw [decodeWindows]
    apply bind_writesAbove _ _ _ (writesAbove_mono cursor (freshVisit _ _))
    intro child returned
    rw [writeValue_bind_effects, bind_return_effects]
    apply writesAbove_append
    · intro address target node member
      have same := List.mem_singleton.mp member
      cases same
      omega
    · apply ih
      exact Nat.le_trans cursor (Nat.add_le_add_left (safeVisit _ _).1 arena.base)

theorem decodeEntries_writesAbove {children : List Desc} (entries : List (Entry children))
    (visit : Visit children) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState) (floor : Nat)
    (pointer : floor ≤ allocation.pointer) (cursor : floor ≤ arena.base + arena.used)
    (safeVisit : ∀ child member input arena, CursorSafe arena (visit child member input arena).used)
    (freshVisit : ∀ child member input arena, FreshWrites arena (visit child member input arena)) :
    WritesAbove floor (decodeEntries entries visit input allocation index arena).effects := by
  induction entries generalizing index arena with
  | nil => exact writesAbove_nil floor
  | cons entry rest ih =>
    rw [decodeEntries]
    apply bind_writesAbove _ _ _ (writesAbove_mono cursor (freshVisit _ _ _ _))
    intro child returned
    rw [writeValue_bind_effects, bind_return_effects]
    apply writesAbove_append
    · intro address target node member
      have same := List.mem_singleton.mp member
      cases same
      omega
    · apply ih
      exact Nat.le_trans cursor (Nat.add_le_add_left (safeVisit _ _ _ _).1 arena.base)

theorem decodeArray_freshWrites (visit : Input → Delimited.ArenaState → Outcome Node)
    (windows : List Window) (input : Input) (arena : Delimited.ArenaState)
    (safeVisit : ∀ input arena, CursorSafe arena (visit input arena).used)
    (freshVisit : ∀ input arena, FreshWrites arena (visit input arena)) :
    FreshWrites arena (decodeArray visit windows input arena) := by
  unfold decodeArray
  apply bind_writesAbove _ _ _ (reserve_noValueWrites _ _ _ _)
  intro allocation success
  obtain ⟨reserved, cursor⟩ := reserve_success _ _ _ _ success
  rw [bind_return_effects, cursor]
  cases windows with
  | nil => exact writesAbove_nil _
  | cons window rest =>
    apply decodeWindows_writesAbove _ _ _ _ _ _ _
      (typedReserve_geometry valueLayout _ arena allocation (by simp) (by decide) reserved).1
      (Nat.add_le_add_left (typedReserve_cursorSafe _ _ _ _ reserved).1 arena.base)
      safeVisit freshVisit

theorem decodeOffsets_freshWrites (visit : Input → Delimited.ArenaState → Outcome Node)
    (count : Nat) (input : Input) (arena : Delimited.ArenaState)
    (safeVisit : ∀ input arena, CursorSafe arena (visit input arena).used)
    (freshVisit : ∀ input arena, FreshWrites arena (visit input arena)) :
    FreshWrites arena (decodeOffsets visit count input arena) := by
  unfold decodeOffsets
  dsimp only
  refine bind_freshWrites_all arena _ _ (cursorSafe_refl arena) ?_ ?_
  · exact writesAbove_nil _
  · intro checked used
    exact decodeArray_freshWrites _ _ _ _ safeVisit freshVisit

theorem vector_freshWrites (element : Desc) (length : NatOperand)
    (visit : Input → Delimited.ArenaState → Outcome Node) (input : Input)
    (arena : Delimited.ArenaState)
    (safeVisit : ∀ input arena, CursorSafe arena (visit input arena).used)
    (freshVisit : ∀ input arena, FreshWrites arena (visit input arena)) :
    FreshWrites arena (vector element length visit input arena) := by
  unfold vector
  apply bind_freshWrites_all _ _ _
    (by rw [(compositeSize_resources _ _).1]; exact cursorSafe_refl _)
    (by rw [FreshWrites, (compositeSize_resources _ _).2]; exact writesAbove_nil _)
  intro checked used
  apply bind_freshWrites_all _ _ _ (fixedSize_cursorSafe _ _) (fixedSize_noValueWrites _ _ _)
  intro width used
  cases width with
  | some width =>
    dsimp only
    apply bind_freshWrites_all _ _ _ (mul_cursorSafe _ _ _) (mul_noValueWrites _ _ _ _)
    intro expected used
    apply bind_freshWrites_all _ _ _
      (by rw [(exact_resources _ _ _).1]; exact cursorSafe_refl _)
      (by rw [FreshWrites, (exact_resources _ _ _).2]; exact writesAbove_nil _)
    intro checked used
    split
    · exact writesAbove_nil _
    · apply bind_freshWrites_all _ _ _
        (by rw [(narrow_resources _ _ _).1]; exact cursorSafe_refl _)
        (by rw [FreshWrites, (narrow_resources _ _ _).2]; exact writesAbove_nil _)
      intro count used
      apply bind_freshWrites_all _ _ _
        (by rw [(narrow_resources _ _ _).1]; exact cursorSafe_refl _)
        (by rw [FreshWrites, (narrow_resources _ _ _).2]; exact writesAbove_nil _)
      intro width used
      rw [decodeFixed_eq_decodeArray]
      exact decodeArray_freshWrites _ _ _ _ safeVisit freshVisit
  | none =>
    dsimp only
    apply bind_freshWrites_all _ _ _ (mul_cursorSafe _ _ _) (mul_noValueWrites _ _ _ _)
    intro leading used
    split
    · exact writesAbove_nil _
    · split
      · exact writesAbove_nil _
      · apply bind_freshWrites_all _ _ _
          (by rw [(narrow_resources _ _ _).1]; exact cursorSafe_refl _)
          (by rw [FreshWrites, (narrow_resources _ _ _).2]; exact writesAbove_nil _)
        intro count used
        dsimp only
        split
        · exact writesAbove_nil _
        · exact decodeOffsets_freshWrites _ _ _ _ safeVisit freshVisit

theorem list_freshWrites (element : Desc) (limit : Option NatOperand)
    (visit : Input → Delimited.ArenaState → Outcome Node) (input : Input)
    (arena : Delimited.ArenaState)
    (safeVisit : ∀ input arena, CursorSafe arena (visit input arena).used)
    (freshVisit : ∀ input arena, FreshWrites arena (visit input arena)) :
    FreshWrites arena (list element limit visit input arena) := by
  unfold list
  apply bind_freshWrites_all _ _ _
    (by rw [(compositeSize_resources _ _).1]; exact cursorSafe_refl _)
    (by rw [FreshWrites, (compositeSize_resources _ _).2]; exact writesAbove_nil _)
  intro checked used
  split
  · exact writesAbove_nil _
  · apply bind_freshWrites_all _ _ _ (fixedSize_cursorSafe _ _) (fixedSize_noValueWrites _ _ _)
    intro width used
    cases width with
    | some width =>
      dsimp only
      split
      · exact writesAbove_nil _
      · split
        · exact writesAbove_nil _
        · apply bind_freshWrites_all _ _ _
            (by rw [(narrow_resources _ _ _).1]; exact cursorSafe_refl _)
            (by rw [FreshWrites, (narrow_resources _ _ _).2]; exact writesAbove_nil _)
          intro width used
          dsimp only
          split
          · exact writesAbove_nil _
          · apply bind_freshWrites_all _ _ _
              (by rw [(bounded_resources _ _ _).1]; exact cursorSafe_refl _)
              (by rw [FreshWrites, (bounded_resources _ _ _).2]; exact writesAbove_nil _)
            intro checked used
            rw [decodeFixed_eq_decodeArray]
            exact decodeArray_freshWrites _ _ _ _ safeVisit freshVisit
    | none =>
      dsimp only
      split
      · exact writesAbove_nil _
      · split
        · exact writesAbove_nil _
        · split
          · exact writesAbove_nil _
          · split
            · exact writesAbove_nil _
            · apply bind_freshWrites_all _ _ _
                (by rw [(bounded_resources _ _ _).1]; exact cursorSafe_refl _)
                (by rw [FreshWrites, (bounded_resources _ _ _).2]; exact writesAbove_nil _)
              intro checked used
              exact decodeOffsets_freshWrites _ _ _ _ safeVisit freshVisit

theorem initializeSlots_noValueWrites (count : Nat) (allocation : Arena.Reservation)
    (used : Nat) : NoValueWrites (initializeSlots count allocation used).effects := by
  intro floor address index node member
  obtain ⟨target, member, same⟩ := List.mem_map.mp member
  cases same

theorem measureSlots_noValueWrites {children : List Desc} (entries : List (Entry children))
    (allocation : Arena.Reservation) (index : Nat) (leading : NatOperand) (allFixed : Bool)
    (arena : Delimited.ArenaState) :
    NoValueWrites (measureSlots entries allocation index leading allFixed arena).effects := by
  induction entries generalizing index leading allFixed arena with
  | nil => exact writesAbove_nil
  | cons entry rest ih =>
    rw [measureSlots]
    apply bind_noValueWrites _ _ (fixedSize_noValueWrites _ _)
    intro width used
    apply bind_noValueWrites _ _ (writeSlot_noValueWrites _ _ _ _)
    intro checked used
    apply bind_noValueWrites _ _ (add_noValueWrites _ _ _)
    intro leading used
    rw [bind_return_effects]
    exact ih _ _ _ _

theorem positionSlots_noValueWrites {children : List Desc} (entries : List (Entry children))
    (input : Input) (allocation : Arena.Reservation) (index position used : Nat) :
    NoValueWrites (positionSlots entries input allocation index position used).effects := by
  induction entries generalizing index position used with
  | nil => exact writesAbove_nil
  | cons entry rest ih =>
    rw [positionSlots]
    apply bind_noValueWrites
    · cases entry.slot.width with
      | none => exact writesAbove_nil
      | some width => rw [(narrow_resources _ _ _).2]; exact writesAbove_nil
    · intro width used
      dsimp only
      split
      · exact writesAbove_nil
      · apply bind_noValueWrites _ _ (writeSlot_noValueWrites _ _ _ _)
        intro checked used
        rw [bind_return_effects]
        exact ih _ _ _

theorem validateSlots_noValueWrites {children : List Desc} (entries : List (Entry children))
    (allocation : Arena.Reservation) (index leading scope : Nat)
    (previous : Option (Nat × Slot)) (used : Nat) :
    NoValueWrites (validateSlots entries allocation index leading scope previous used).effects := by
  induction entries generalizing index previous used with
  | nil =>
    rw [validateSlots.eq_def]
    cases previous with
    | none => rw [(exact_resources _ _ _).2]; exact writesAbove_nil
    | some previous =>
      rcases previous with ⟨previousIndex, slot⟩
      dsimp only
      split
      · exact writesAbove_nil
      · exact writeSlot_noValueWrites _ _ _ _
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
        · exact writesAbove_nil
        · exact ih _ _ _
      | some previous =>
        rcases previous with ⟨previousIndex, previousSlot⟩
        dsimp only
        split
        · exact writesAbove_nil
        · apply bind_noValueWrites _ _ (writeSlot_noValueWrites _ _ _ _)
          intro checked used
          exact ih _ _ _

theorem decodeEntries_empty_noValueWrites (entries : List (Entry []))
    (visit : Visit []) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState) :
    NoValueWrites (decodeEntries entries visit input allocation index arena).effects := by
  cases entries with
  | nil => exact writesAbove_nil
  | cons entry rest => cases entry.member

theorem structureValue_freshWrites (children : List Desc) (visit : Visit children)
    (input : Input) (arena : Delimited.ArenaState)
    (safeVisit : ∀ child member input arena, CursorSafe arena (visit child member input arena).used)
    (freshVisit : ∀ child member input arena, FreshWrites arena (visit child member input arena)) :
    FreshWrites arena (structureValue children visit input arena) := by
  unfold structureValue
  apply bind_freshWrites_all _ _ _
    (by rw [(compositeSize_resources _ _).1]; exact cursorSafe_refl _)
    (by rw [FreshWrites, (compositeSize_resources _ _).2]; exact writesAbove_nil _)
  intro checked used
  apply bind_freshWrites_all _ _ _ (reserve_cursorSafe _ _ _) (reserve_noValueWrites _ _ _ _)
  intro slots used
  refine bind_freshWrites_all _ _ _ (cursorSafe_refl _) ?_ ?_
  · exact initializeSlots_noValueWrites _ _ _ _
  · intro checked used
    apply bind_freshWrites_all _ _ _ (measureSlots_cursorSafe _ _ _ _ _ _)
      (measureSlots_noValueWrites _ _ _ _ _ _ _)
    intro measured used
    dsimp only
    refine bind_freshWrites_all _ _ _ ?_ ?_ ?_
    · split
      · rw [(exact_resources _ _ _).1]
        exact cursorSafe_refl _
      · split <;> exact cursorSafe_refl _
    · split
      · rw [FreshWrites, (exact_resources _ _ _).2]
        exact writesAbove_nil _
      · split <;> exact writesAbove_nil _
    · intro checked used
      apply bind_freshWrites_all _ _ _
        (by rw [positionSlots_used]; exact cursorSafe_refl _)
        (positionSlots_noValueWrites _ _ _ _ _ _ _)
      intro positioned used
      apply bind_freshWrites_all _ _ _
        (by rw [validateSlots_used]; exact cursorSafe_refl _)
        (validateSlots_noValueWrites _ _ _ _ _ _ _ _)
      intro checked used
      dsimp only
      apply bind_writesAbove _ _ _ (reserve_noValueWrites _ _ _ _)
      intro values success
      obtain ⟨reserved, cursor⟩ := reserve_success _ _ _ _ success
      rw [bind_return_effects, cursor]
      cases children with
      | nil => exact decodeEntries_empty_noValueWrites _ _ _ _ _ _ _
      | cons child children =>
        apply decodeEntries_writesAbove _ _ _ _ _ _ _
          (typedReserve_geometry valueLayout _ _ values (by simp) (by decide) reserved).1
          (Nat.add_le_add_left (typedReserve_cursorSafe _ _ _ _ reserved).1 _)
          safeVisit freshVisit

theorem unionOption_freshWrites (variants : List (NatOperand × Desc))
    (visit : Visit (variants.map Prod.snd)) (selector : NatOperand)
    (input : Input) (arena : Delimited.ArenaState)
    (safeVisit : ∀ child member input arena, CursorSafe arena (visit child member input arena).used)
    (freshVisit : ∀ child member input arena, FreshWrites arena (visit child member input arena)) :
    FreshWrites arena (unionOption variants visit selector input arena) := by
  induction variants generalizing arena with
  | nil => exact writesAbove_nil _
  | cons variant rest ih =>
    rcases variant with ⟨chosen, desc⟩
    rw [unionOption]
    split
    · apply bind_freshWrites_all _ _ _ (safeVisit _ _ _ _) (freshVisit _ _ _ _)
      intro child used
      apply bind_writesAbove _ _ _ (reserve_noValueWrites _ _ _ _)
      intro allocation success
      obtain ⟨reserved, cursor⟩ := reserve_success _ _ _ _ success
      rw [bind_return_effects]
      intro address index node member
      have same := List.mem_singleton.mp member
      cases same
      simpa only [Nat.mul_zero, Nat.add_zero] using
        (typedReserve_geometry valueLayout 1 _ allocation (by decide) (by decide) reserved).1
    · apply ih
      · intro child member input arena
        exact safeVisit _ _ _ _
      · intro child member input arena
        exact freshVisit _ _ _ _

theorem decodeStep_freshWrites (desc : Desc) (input : Input) (arena : Delimited.ArenaState)
    (visit : Visit desc.children)
    (safeVisit : ∀ child member input arena, CursorSafe arena (visit child member input arena).used)
    (freshVisit : ∀ child member input arena, FreshWrites arena (visit child member input arena)) :
    FreshWrites arena (decodeStep desc input arena visit) := by
  cases desc with
  | primitive shape => exact primitive_noValueWrites _ _ _ _
  | vector element length => exact vector_freshWrites _ _ _ _ _ (safeVisit _ _) (freshVisit _ _)
  | list element limit => exact list_freshWrites _ _ _ _ _ (safeVisit _ _) (freshVisit _ _)
  | progressiveList element limit => exact list_freshWrites _ _ _ _ _ (safeVisit _ _) (freshVisit _ _)
  | container fields => exact structureValue_freshWrites _ _ _ _ safeVisit freshVisit
  | progressiveContainer active fields => exact structureValue_freshWrites _ _ _ _ safeVisit freshVisit
  | compatibleUnion variants =>
    dsimp only [decodeStep]
    split
    · exact writesAbove_nil _
    · exact unionOption_freshWrites _ _ _ _ _ safeVisit freshVisit

/-- Recursive decoders never initialize a Value below their incoming arena
cursor. This includes every error branch and requires no successful future call. -/
theorem decode_freshWrites (desc : Desc) (input : Input) (arena : Delimited.ArenaState) :
    FreshWrites arena (decode desc input arena) := by
  rw [decode]
  apply decodeStep_freshWrites
  · intro child member input arena
    exact decode_cursorSafe child input arena
  · intro child member input arena
    exact decode_freshWrites child input arena
termination_by desc.nesting
decreasing_by exact Desc.child_nesting_lt _ _ (by assumption)

theorem run_freshWrites (desc : Desc) (bytes : Ssz.Bytes) (arena : Delimited.ArenaState) :
    FreshWrites arena (run desc bytes arena) := decode_freshWrites desc ⟨0, bytes⟩ arena

theorem storeValues_untouched_below (floor : Nat) (effects : List Effect)
    (writes : WritesAbove floor effects) (memory : ValueMemory) (address : Nat)
    (before : address < floor) : storeValues effects memory address = memory address := by
  induction effects generalizing memory with
  | nil => rfl
  | cons effect rest ih =>
    change storeValues rest (effect.storeValue memory) address = memory address
    rw [ih (fun target index node member => writes target index node (List.mem_cons_of_mem _ member))]
    cases effect with
    | writeValue target index node =>
      have after := writes target index node (List.mem_cons_self)
      have different : address ≠ target := by omega
      simp only [Effect.storeValue, different, ↓reduceIte]
    | _ => rfl

theorem decode_preserves_earlier_values (desc : Desc) (input : Input)
    (arena : Delimited.ArenaState) (memory : ValueMemory) (address : Nat)
    (before : address < arena.base + arena.used) :
    storeValues (decode desc input arena).effects memory address = memory address :=
  storeValues_untouched_below _ _ (decode_freshWrites desc input arena) memory address before

theorem run_preserves_earlier_values (desc : Desc) (bytes : Ssz.Bytes)
    (arena : Delimited.ArenaState) (memory : ValueMemory) (address : Nat)
    (before : address < arena.base + arena.used) :
    storeValues (run desc bytes arena).effects memory address = memory address :=
  decode_preserves_earlier_values desc ⟨0, bytes⟩ arena memory address before

end SszNative.CodecDecode
