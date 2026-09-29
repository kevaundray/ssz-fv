import SszCodecDecodeResourcesFrame

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc Error)

/-- An exact failure decomposition, including a frame bound for every actual
child call. No bytes or padding of Value records are asserted initialized. -/
def FailingPrefix (allocation : Arena.Reservation) (index count floor : Nat)
    (outcome : Outcome (List Node)) (reason : Error) : Prop :=
  ∃ completed : List InitializedChild, ∃ failing : Outcome Node,
    completed.length < count ∧ failing.result = .error reason ∧
    outcome.used = failing.used ∧
    outcome.effects = initializedEffects allocation index completed ++ failing.effects ∧
    (∀ child ∈ completed, WritesAbove floor child.call.effects) ∧ WritesAbove floor failing.effects

theorem decodeWindows_failure_frame (visit : Input → Delimited.ArenaState → Outcome Node)
    (windows : List Window) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState) (floor : Nat)
    (cursor : floor ≤ arena.base + arena.used)
    (safeVisit : ∀ input arena, CursorSafe arena (visit input arena).used)
    (freshVisit : ∀ input arena, FreshWrites arena (visit input arena))
    (reason : Error) (failed : (decodeWindows visit windows input allocation index arena).result = .error reason) :
    FailingPrefix allocation index windows.length floor
      (decodeWindows visit windows input allocation index arena) reason := by
  induction windows generalizing index arena with
  | nil => cases failed
  | cons window rest ih =>
    let call := visit (input.slice window.start window.ending) arena
    have fresh : WritesAbove floor call.effects := writesAbove_mono cursor (freshVisit _ _)
    cases returned : call.result with
    | error failure =>
      have same : failure = reason := by
        simpa only [decodeWindows, bind, show visit (input.slice window.start window.ending) arena = call from rfl,
          returned, Except.error.injEq] using failed
      subst failure
      have immediate : FailingPrefix allocation index (rest.length + 1) floor
          ⟨.error reason, call.used, call.effects⟩ reason :=
        ⟨[], call, Nat.zero_lt_succ _, returned, rfl, rfl,
          (by intro child member; cases member), fresh⟩
      simpa only [decodeWindows, bind,
        show visit (input.slice window.start window.ending) arena = call from rfl,
        returned, List.length_cons] using immediate
    | ok node =>
      let suffix := decodeWindows visit rest input allocation (index + 1) { arena with used := call.used }
      have suffixFailed : suffix.result = .error reason := by
        cases result : suffix.result with
        | error failure =>
          simpa only [decodeWindows, bind, show visit (input.slice window.start window.ending) arena = call from rfl,
            returned, writeValue, show decodeWindows visit rest input allocation (index + 1)
              { arena with used := call.used } = suffix from rfl, result] using failed
        | ok nodes =>
          simp only [decodeWindows, bind, show visit (input.slice window.start window.ending) arena = call from rfl,
            returned, writeValue, show decodeWindows visit rest input allocation (index + 1)
              { arena with used := call.used } = suffix from rfl, result, unchanged] at failed
          cases failed
      obtain ⟨completed, failing, shorter, childFailed, used, effects, prefixFresh, failingFresh⟩ :=
        ih (index + 1) { arena with used := call.used }
          (Nat.le_trans cursor (Nat.add_le_add_left (safeVisit _ _).1 arena.base)) suffixFailed
      change suffix.effects =
        initializedEffects allocation (index + 1) completed ++ failing.effects at effects
      let child : InitializedChild := ⟨call, node, returned⟩
      refine ⟨child :: completed, failing, by simpa only [List.length_cons] using Nat.succ_lt_succ shorter,
        childFailed, ?_, ?_, ?_, failingFresh⟩
      · simpa only [decodeWindows, bind, show visit (input.slice window.start window.ending) arena = call from rfl,
          returned, writeValue, show decodeWindows visit rest input allocation (index + 1)
            { arena with used := call.used } = suffix from rfl, suffixFailed] using used
      · simp only [decodeWindows, bind, show visit (input.slice window.start window.ending) arena = call from rfl,
          returned, writeValue, show decodeWindows visit rest input allocation (index + 1)
            { arena with used := call.used } = suffix from rfl, suffixFailed,
          initializedEffects, child, effects, List.append_assoc]
      · intro frame member
        rcases List.mem_cons.mp member with same | member
        · subst frame
          exact fresh
        · exact prefixFresh frame member

theorem decodeEntries_failure_frame {children : List Desc} (entries : List (Entry children))
    (visit : Visit children) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState) (floor : Nat)
    (cursor : floor ≤ arena.base + arena.used)
    (safeVisit : ∀ child member input arena, CursorSafe arena (visit child member input arena).used)
    (freshVisit : ∀ child member input arena, FreshWrites arena (visit child member input arena))
    (reason : Error) (failed : (decodeEntries entries visit input allocation index arena).result = .error reason) :
    FailingPrefix allocation index entries.length floor
      (decodeEntries entries visit input allocation index arena) reason := by
  induction entries generalizing index arena with
  | nil => cases failed
  | cons entry rest ih =>
    let call := visit entry.desc entry.member (input.slice entry.slot.start entry.slot.ending) arena
    have fresh : WritesAbove floor call.effects := writesAbove_mono cursor (freshVisit _ _ _ _)
    cases returned : call.result with
    | error failure =>
      have same : failure = reason := by
        simpa only [decodeEntries, bind, show visit entry.desc entry.member
          (input.slice entry.slot.start entry.slot.ending) arena = call from rfl,
          returned, Except.error.injEq] using failed
      subst failure
      have immediate : FailingPrefix allocation index (rest.length + 1) floor
          ⟨.error reason, call.used, call.effects⟩ reason :=
        ⟨[], call, Nat.zero_lt_succ _, returned, rfl, rfl,
          (by intro child member; cases member), fresh⟩
      simpa only [decodeEntries, bind, show visit entry.desc entry.member
        (input.slice entry.slot.start entry.slot.ending) arena = call from rfl,
        returned, List.length_cons] using immediate
    | ok node =>
      let suffix := decodeEntries rest visit input allocation (index + 1) { arena with used := call.used }
      have suffixFailed : suffix.result = .error reason := by
        cases result : suffix.result with
        | error failure =>
          simpa only [decodeEntries, bind, show visit entry.desc entry.member
            (input.slice entry.slot.start entry.slot.ending) arena = call from rfl,
            returned, writeValue, show decodeEntries rest visit input allocation (index + 1)
              { arena with used := call.used } = suffix from rfl, result] using failed
        | ok nodes =>
          simp only [decodeEntries, bind, show visit entry.desc entry.member
            (input.slice entry.slot.start entry.slot.ending) arena = call from rfl,
            returned, writeValue, show decodeEntries rest visit input allocation (index + 1)
              { arena with used := call.used } = suffix from rfl, result, unchanged] at failed
          cases failed
      obtain ⟨completed, failing, shorter, childFailed, used, effects, prefixFresh, failingFresh⟩ :=
        ih (index + 1) { arena with used := call.used }
          (Nat.le_trans cursor (Nat.add_le_add_left (safeVisit _ _ _ _).1 arena.base)) suffixFailed
      change suffix.effects =
        initializedEffects allocation (index + 1) completed ++ failing.effects at effects
      let child : InitializedChild := ⟨call, node, returned⟩
      refine ⟨child :: completed, failing, by simpa only [List.length_cons] using Nat.succ_lt_succ shorter,
        childFailed, ?_, ?_, ?_, failingFresh⟩
      · simpa only [decodeEntries, bind, show visit entry.desc entry.member
          (input.slice entry.slot.start entry.slot.ending) arena = call from rfl,
          returned, writeValue, show decodeEntries rest visit input allocation (index + 1)
            { arena with used := call.used } = suffix from rfl, suffixFailed] using used
      · simp only [decodeEntries, bind, show visit entry.desc entry.member
          (input.slice entry.slot.start entry.slot.ending) arena = call from rfl,
          returned, writeValue, show decodeEntries rest visit input allocation (index + 1)
            { arena with used := call.used } = suffix from rfl, suffixFailed,
          initializedEffects, child, effects, List.append_assoc]
      · intro frame member
        rcases List.mem_cons.mp member with same | member
        · subst frame
          exact fresh
        · exact prefixFresh frame member

theorem storeValues_pointwise (effects : List Effect) (left right : ValueMemory)
    (address : Nat) (same : left address = right address) :
    storeValues effects left address = storeValues effects right address := by
  induction effects generalizing left right with
  | nil => exact same
  | cons effect rest ih =>
    apply ih
    cases effect with
    | writeValue target index node =>
      unfold Effect.storeValue
      dsimp only
      split
      · rfl
      · exact same
    | _ => exact same

theorem initializedEffects_frame (allocation : Arena.Reservation) (index : Nat)
    (completed : List InitializedChild) (floor : Nat)
    (fresh : ∀ child ∈ completed, WritesAbove floor child.call.effects)
    (memory : ValueMemory) (address : Nat) (before : address < floor) :
    storeValues (initializedEffects allocation index completed) memory address =
      storeValues (initializerEffects allocation index completed) memory address := by
  induction completed generalizing index memory with
  | nil => rfl
  | cons child rest ih =>
    simp only [initializedEffects, storeValues_append]
    rw [ih (index + 1) (fun frame member => fresh frame (List.mem_cons_of_mem _ member))]
    apply storeValues_pointwise
    apply storeValues_pointwise
    exact storeValues_untouched_below floor _ (fresh child List.mem_cons_self) memory address before

theorem initializerEffects_before (allocation : Arena.Reservation) (index : Nat)
    (completed : List InitializedChild) (memory : ValueMemory) (earlier : Nat)
    (before : earlier < index) :
    storeValues (initializerEffects allocation index completed) memory
      (allocation.pointer + valueLayout.size * earlier) =
      memory (allocation.pointer + valueLayout.size * earlier) := by
  induction completed generalizing index memory with
  | nil => rfl
  | cons child rest ih =>
    have different : allocation.pointer + valueLayout.size * earlier ≠
        allocation.pointer + valueLayout.size * index := by
      change allocation.pointer + 48 * earlier ≠ allocation.pointer + 48 * index
      omega
    change storeValues (initializerEffects allocation (index + 1) rest)
      ((Effect.writeValue (allocation.pointer + valueLayout.size * index) index child.node).storeValue memory)
      (allocation.pointer + valueLayout.size * earlier) = _
    rw [ih (index + 1) _ (by omega)]
    simp only [Effect.storeValue, different, ↓reduceIte]

theorem initializerEffects_initialized (allocation : Arena.Reservation) (index : Nat)
    (completed : List InitializedChild) (memory : ValueMemory) (ordinal : Nat)
    (child : InitializedChild) (atIndex : completed[ordinal]? = some child) :
    storeValues (initializerEffects allocation index completed) memory
      (allocation.pointer + valueLayout.size * (index + ordinal)) = some child.node := by
  induction completed generalizing index memory ordinal with
  | nil =>
    simp only [List.getElem?_nil] at atIndex
    cases atIndex
  | cons first rest ih =>
    cases ordinal with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atIndex
      subst child
      simp only [Nat.add_zero]
      change storeValues (initializerEffects allocation (index + 1) rest)
        ((Effect.writeValue (allocation.pointer + valueLayout.size * index) index first.node).storeValue memory)
        (allocation.pointer + valueLayout.size * index) = _
      rw [initializerEffects_before _ _ _ _ _ (by omega)]
      simp only [Effect.storeValue, ↓reduceIte]
    | succ ordinal =>
      simp only [List.getElem?_cons_succ] at atIndex
      have shifted : index + (ordinal + 1) = (index + 1) + ordinal := by omega
      change storeValues (initializerEffects allocation (index + 1) rest)
        ((Effect.writeValue (allocation.pointer + valueLayout.size * index) index first.node).storeValue memory)
        (allocation.pointer + valueLayout.size * (index + (ordinal + 1))) = _
      simpa only [shifted] using ih (index + 1)
        ((Effect.writeValue (allocation.pointer + valueLayout.size * index) index first.node).storeValue memory)
        ordinal atIndex

/-- Actual recursive child writes cannot spoil initialized prefix elements or
initialize a later element. Both statements concern semantic fields, not padding. -/
theorem FailingPrefix.memory {allocation : Arena.Reservation} {index count floor : Nat}
    {outcome : Outcome (List Node)} {reason : Error}
    (execution : FailingPrefix allocation index count floor outcome reason)
    (span : allocation.pointer + valueLayout.size * (index + count) ≤ floor) :
    ∃ completed : List InitializedChild, completed.length < count ∧
      (∀ memory ordinal child, completed[ordinal]? = some child →
        storeValues outcome.effects memory
          (allocation.pointer + valueLayout.size * (index + ordinal)) = some child.node) ∧
      (∀ memory later, index + completed.length ≤ later → later < index + count →
        storeValues outcome.effects memory (allocation.pointer + valueLayout.size * later) =
          memory (allocation.pointer + valueLayout.size * later)) := by
  obtain ⟨completed, failing, shorter, failed, cursor, effects, fresh, failingFresh⟩ := execution
  refine ⟨completed, shorter, ?_, ?_⟩
  · intro memory ordinal child atIndex
    have ordinalBound : ordinal < completed.length := by
      have bounded : ∀ (frames : List InitializedChild) (position : Nat),
          frames[position]? = some child → position < frames.length := by
        intro frames
        induction frames with
        | nil =>
          intro position found
          cases position <;> cases found
        | cons first rest ih =>
          intro position found
          cases position with
          | zero => exact Nat.zero_lt_succ _
          | succ position => exact Nat.succ_lt_succ (ih position found)
      exact bounded completed ordinal atIndex
    have before : allocation.pointer + valueLayout.size * (index + ordinal) < floor := by
      change allocation.pointer + 48 * (index + count) ≤ floor at span
      change allocation.pointer + 48 * (index + ordinal) < floor
      omega
    rw [effects, storeValues_append,
      storeValues_untouched_below floor _ failingFresh _ _ before,
      initializedEffects_frame _ _ _ _ fresh _ _ before]
    exact initializerEffects_initialized _ _ _ _ _ _ atIndex
  · intro memory later after bounded
    have before : allocation.pointer + valueLayout.size * later < floor := by
      change allocation.pointer + 48 * (index + count) ≤ floor at span
      change allocation.pointer + 48 * later < floor
      omega
    rw [effects, storeValues_append,
      storeValues_untouched_below floor _ failingFresh _ _ before,
      initializedEffects_frame _ _ _ _ fresh _ _ before]
    exact initializerEffects_untouched _ _ _ _ _ after

/-- Public recursive child instantiation: no callback frame hypotheses remain. -/
theorem decodeArray_failure_memory (element : Desc) (windows : List Window)
    (input : Input) (arena : Delimited.ArenaState) (allocation : Arena.Reservation)
    (reserved : TypedArena.reserve valueLayout arena.base arena.capacity arena.used windows.length =
      some allocation) (reason : Error)
    (failed : (decodeArray (decode element) windows input arena).result = .error reason) :
    ∃ completed : List InitializedChild, completed.length < windows.length ∧
      (∀ memory ordinal child, completed[ordinal]? = some child →
        storeValues (decodeArray (decode element) windows input arena).effects memory
          (allocation.pointer + valueLayout.size * ordinal) = some child.node) ∧
      (∀ memory later, completed.length ≤ later → later < windows.length →
        storeValues (decodeArray (decode element) windows input arena).effects memory
          (allocation.pointer + valueLayout.size * later) =
            memory (allocation.pointer + valueLayout.size * later)) := by
  let call := decodeWindows (decode element) windows input allocation 0
    { arena with used := allocation.used }
  have loopFailed : call.result = .error reason := by
    cases result : call.result with
    | error failure =>
      simpa only [decodeArray, reserve, reserved, bind,
        show decodeWindows (decode element) windows input allocation 0
          { arena with used := allocation.used } = call from rfl, result, Except.error.injEq] using failed
    | ok nodes =>
      simp only [decodeArray, reserve, reserved, bind,
        show decodeWindows (decode element) windows input allocation 0
          { arena with used := allocation.used } = call from rfl, result, unchanged] at failed
      cases failed
  have positive : 0 < windows.length := by
    cases windows with
    | nil => cases loopFailed
    | cons window rest => simp only [List.length_cons]; omega
  have frame := decodeWindows_failure_frame (decode element) windows input allocation 0
    { arena with used := allocation.used } (arena.base + allocation.used) (Nat.le_refl _)
    (decode_cursorSafe element) (decode_freshWrites element) reason loopFailed
  have span : allocation.pointer + valueLayout.size * (0 + windows.length) ≤
      arena.base + allocation.used := by
    simpa only [Nat.zero_add] using Nat.le_of_eq
      (typedReserve_geometry valueLayout _ arena allocation positive (by decide) reserved).2.2.1
  obtain ⟨completed, shorter, initialized, untouched⟩ := frame.memory span
  simp only [Nat.zero_add] at initialized untouched
  refine ⟨completed, shorter, ?_, ?_⟩
  · intro memory ordinal child atIndex
    rw [(decodeArray_reserved (decode element) windows input arena allocation reserved).1]
    change storeValues call.effects memory
      (allocation.pointer + valueLayout.size * ordinal) = _
    exact initialized memory ordinal child atIndex
  · intro memory later after bounded
    rw [(decodeArray_reserved (decode element) windows input arena allocation reserved).1]
    change storeValues call.effects memory
      (allocation.pointer + valueLayout.size * later) = _
    exact untouched memory later after bounded

theorem decodeEntries_recursive_failure_memory {children : List Desc}
    (entries : List (Entry children)) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState)
    (span : allocation.pointer + valueLayout.size * (index + entries.length) ≤
      arena.base + arena.used) (reason : Error)
    (failed : (decodeEntries entries (fun child _ => decode child) input allocation index arena).result =
      .error reason) :
    ∃ completed : List InitializedChild, completed.length < entries.length ∧
      (∀ memory ordinal child, completed[ordinal]? = some child →
        storeValues (decodeEntries entries (fun child _ => decode child) input allocation index arena).effects
          memory (allocation.pointer + valueLayout.size * (index + ordinal)) = some child.node) ∧
      (∀ memory later, index + completed.length ≤ later → later < index + entries.length →
        storeValues (decodeEntries entries (fun child _ => decode child) input allocation index arena).effects
          memory (allocation.pointer + valueLayout.size * later) =
            memory (allocation.pointer + valueLayout.size * later)) := by
  exact (decodeEntries_failure_frame entries (fun child _ => decode child) input allocation index arena
    (arena.base + arena.used) (Nat.le_refl _)
    (fun child _ => decode_cursorSafe child) (fun child _ => decode_freshWrites child)
    reason failed).memory span

end SszNative.CodecDecode
