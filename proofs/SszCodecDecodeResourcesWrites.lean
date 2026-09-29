import SszCodecDecodeResources

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc Error)

/-- Value memory is logical initialized values at addresses, not bytes or padding. -/
abbrev ValueMemory := Nat → Option Node

def Effect.storeValue (effect : Effect) (memory : ValueMemory) : ValueMemory :=
  match effect with
  | .writeValue address _ node => fun target => if target = address then some node else memory target
  | _ => memory

def storeValues (effects : List Effect) (memory : ValueMemory) : ValueMemory :=
  effects.foldl (fun memory effect => effect.storeValue memory) memory

theorem storeValues_append (first second : List Effect) (memory : ValueMemory) :
    storeValues (first ++ second) memory = storeValues second (storeValues first memory) := by
  simp only [storeValues, List.foldl_append]

/-- An event frame records an actual successful child, including its committed
cursor and every nested effect. It is not a promise that a future call succeeds. -/
structure InitializedChild where
  call : Outcome Node
  node : Node
  returned : call.result = .ok node

def initializedEffects (allocation : Arena.Reservation) : Nat → List InitializedChild → List Effect
  | _, [] => []
  | index, child :: rest => child.call.effects ++
      [.writeValue (allocation.pointer + valueLayout.size * index) index child.node] ++
      initializedEffects allocation (index + 1) rest

/-- Exact event certificate for a complete prefix and the first failing child.
The failed child's effects are last; its parent slot has no initializer event. -/
inductive PrefixExecution (allocation : Arena.Reservation) : Nat → Nat → Outcome (List Node) → Prop
  | done (index used : Nat) : PrefixExecution allocation index 0 (unchanged used (.ok []))
  | failed (index remaining : Nat) (call : Outcome Node) (reason : Error)
      (returned : call.result = .error reason) :
      PrefixExecution allocation index (remaining + 1) ⟨.error reason, call.used, call.effects⟩
  | initialized (index remaining : Nat) (child : InitializedChild) (rest : Outcome (List Node))
      (suffix : PrefixExecution allocation (index + 1) remaining rest) :
      PrefixExecution allocation index (remaining + 1)
        ⟨rest.result.map (fun nodes => child.node :: nodes), rest.used,
          child.call.effects ++
            [.writeValue (allocation.pointer + valueLayout.size * index) index child.node] ++
            rest.effects⟩

theorem decodeWindows_prefix (visit : Input → Delimited.ArenaState → Outcome Node)
    (windows : List Window) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState) :
    PrefixExecution allocation index windows.length
      (decodeWindows visit windows input allocation index arena) := by
  induction windows generalizing index arena with
  | nil => exact .done index arena.used
  | cons window rest ih =>
    cases returned : (visit (input.slice window.start window.ending) arena).result with
    | error reason =>
      simpa only [decodeWindows, bind, returned, List.length_cons] using
        PrefixExecution.failed (allocation := allocation) index rest.length
          (visit (input.slice window.start window.ending) arena) reason returned
    | ok node =>
      let child : InitializedChild := ⟨visit (input.slice window.start window.ending) arena, node, returned⟩
      have certified := PrefixExecution.initialized (allocation := allocation) index rest.length child
        (decodeWindows visit rest input allocation (index + 1)
          { arena with used := child.call.used }) (ih (index + 1) _)
      cases suffix : (decodeWindows visit rest input allocation (index + 1)
          { arena with used := child.call.used }).result <;>
        simpa only [decodeWindows, bind, returned, writeValue, suffix, child,
          Except.map, unchanged, List.length_cons, List.append_assoc, List.append_nil] using certified

theorem decodeEntries_prefix {children : List Desc} (entries : List (Entry children))
    (visit : Visit children) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState) :
    PrefixExecution allocation index entries.length
      (decodeEntries entries visit input allocation index arena) := by
  induction entries generalizing index arena with
  | nil => exact .done index arena.used
  | cons entry rest ih =>
    cases returned : (visit entry.desc entry.member
        (input.slice entry.slot.start entry.slot.ending) arena).result with
    | error reason =>
      simpa only [decodeEntries, bind, returned, List.length_cons] using
        PrefixExecution.failed (allocation := allocation) index rest.length
          (visit entry.desc entry.member (input.slice entry.slot.start entry.slot.ending) arena)
          reason returned
    | ok node =>
      let child : InitializedChild := ⟨visit entry.desc entry.member
        (input.slice entry.slot.start entry.slot.ending) arena, node, returned⟩
      have certified := PrefixExecution.initialized (allocation := allocation) index rest.length child
        (decodeEntries rest visit input allocation (index + 1)
          { arena with used := child.call.used }) (ih (index + 1) _)
      cases suffix : (decodeEntries rest visit input allocation (index + 1)
          { arena with used := child.call.used }).result <;>
        simpa only [decodeEntries, bind, returned, writeValue, suffix, child,
          Except.map, unchanged, List.length_cons, List.append_assoc, List.append_nil] using certified

/-- On failure the initialized prefix is strictly shorter than the array.
The entire failing child trace and cursor are retained verbatim. -/
theorem PrefixExecution.failure {allocation : Arena.Reservation} {index count : Nat}
    {outcome : Outcome (List Node)} (execution : PrefixExecution allocation index count outcome)
    (reason : Error) (failed : outcome.result = .error reason) :
    ∃ completed : List InitializedChild, ∃ failing : Outcome Node,
      completed.length < count ∧ failing.result = .error reason ∧
      outcome.used = failing.used ∧
      outcome.effects = initializedEffects allocation index completed ++ failing.effects := by
  induction execution with
  | done index used => cases failed
  | failed index remaining call failure returned =>
    cases failed
    exact ⟨[], call, Nat.zero_lt_succ _, returned, rfl, rfl⟩
  | initialized index remaining child rest suffix ih =>
    cases returned : rest.result with
    | ok nodes =>
      simp only [returned, Except.map] at failed
      cases failed
    | error failure =>
      have same : failure = reason := by simpa only [returned, Except.map, Except.error.injEq] using failed
      subst failure
      obtain ⟨completed, failing, shorter, failedChild, cursor, effects⟩ := ih returned
      refine ⟨child :: completed, failing, by simpa only [List.length_cons] using Nat.succ_lt_succ shorter,
        failedChild, cursor, ?_⟩
      simp only [initializedEffects, effects, List.append_assoc]

theorem PrefixExecution.success {allocation : Arena.Reservation} {index count : Nat}
    {outcome : Outcome (List Node)} (execution : PrefixExecution allocation index count outcome)
    (nodes : List Node) (success : outcome.result = .ok nodes) :
    nodes.length = count ∧ ∃ completed : List InitializedChild,
      completed.length = count ∧ completed.map InitializedChild.node = nodes ∧
      outcome.effects = initializedEffects allocation index completed := by
  induction execution generalizing nodes with
  | done index used =>
    cases success
    exact ⟨rfl, [], rfl, rfl, rfl⟩
  | failed index remaining call reason returned => cases success
  | initialized index remaining child rest suffix ih =>
    cases returned : rest.result with
    | error reason =>
      simp only [returned, Except.map] at success
      cases success
    | ok tail =>
      have same : child.node :: tail = nodes := by
        simpa only [returned, Except.map, Except.ok.injEq] using success
      subst nodes
      obtain ⟨length, completed, prefixLength, values, effects⟩ := ih tail returned
      refine ⟨by simp only [List.length_cons, length], child :: completed,
        by simp only [List.length_cons, prefixLength], ?_, ?_⟩
      · simp only [List.map_cons, values]
      · simp only [initializedEffects, effects]

/-- Parent initializer writes only. Nested effects stay separately identifiable
in `initializedEffects`; they are never erased from the execution certificate. -/
def initializerEffects (allocation : Arena.Reservation) : Nat → List InitializedChild → List Effect
  | _, [] => []
  | index, child :: rest =>
    .writeValue (allocation.pointer + valueLayout.size * index) index child.node ::
      initializerEffects allocation (index + 1) rest

theorem initializerEffects_untouched (allocation : Arena.Reservation) (index : Nat)
    (completed : List InitializedChild) (memory : ValueMemory) (later : Nat)
    (outside : index + completed.length ≤ later) :
    storeValues (initializerEffects allocation index completed) memory
      (allocation.pointer + valueLayout.size * later) =
      memory (allocation.pointer + valueLayout.size * later) := by
  induction completed generalizing index memory with
  | nil => rfl
  | cons child rest ih =>
    have different : allocation.pointer + valueLayout.size * later ≠
        allocation.pointer + valueLayout.size * index := by
      simp only [valueLayout] at *
      simp only [List.length_cons] at outside
      omega
    change storeValues (initializerEffects allocation (index + 1) rest)
      ((Effect.writeValue (allocation.pointer + valueLayout.size * index) index child.node).storeValue memory)
      (allocation.pointer + valueLayout.size * later) = _
    rw [ih (index + 1) _ (by simp only [List.length_cons] at outside; omega)]
    simp only [Effect.storeValue, different, ↓reduceIte]

theorem decodeArray_reservation_failure (visit : Input → Delimited.ArenaState → Outcome Node)
    (windows : List Window) (input : Input) (arena : Delimited.ArenaState)
    (failed : TypedArena.reserve valueLayout arena.base arena.capacity arena.used windows.length = none) :
    decodeArray visit windows input arena =
      ⟨.error scratch, arena.used, [.reserve valueLayout windows.length arena none]⟩ := by
  simp only [decodeArray, reserve, failed, bind]

/-- Committing the entire array precedes every child and initializer, on errors too. -/
theorem decodeArray_reserved (visit : Input → Delimited.ArenaState → Outcome Node)
    (windows : List Window) (input : Input) (arena : Delimited.ArenaState)
    (allocation : Arena.Reservation)
    (reserved : TypedArena.reserve valueLayout arena.base arena.capacity arena.used windows.length =
      some allocation) :
    (decodeArray visit windows input arena).effects =
      .reserve valueLayout windows.length arena (some allocation) ::
        (decodeWindows visit windows input allocation 0 { arena with used := allocation.used }).effects ∧
    (decodeArray visit windows input arena).used =
        (decodeWindows visit windows input allocation 0 { arena with used := allocation.used }).used := by
  cases result : (decodeWindows visit windows input allocation 0
      { arena with used := allocation.used }).result <;>
    simp only [decodeArray, reserve, reserved, bind, result, unchanged,
      List.append_nil, List.singleton_append, and_self]

theorem initializeSlots_complete (count : Nat) (allocation : Arena.Reservation) (used : Nat) :
    (initializeSlots count allocation used).result = .ok () ∧
    (initializeSlots count allocation used).used = used ∧
    (initializeSlots count allocation used).effects =
      (List.range count).map (fun index =>
        .writeSlot (allocation.pointer + 40 * index) index ⟨none, 0, 0⟩) := by
  exact ⟨rfl, rfl, rfl⟩

theorem valueLayout_native : valueLayout.size = 48 ∧ valueLayout.alignment = 16 := by
  exact ⟨rfl, rfl⟩

theorem slotLayout_native : slotLayout.size = 40 ∧ slotLayout.alignment = 8 := by
  exact ⟨rfl, rfl⟩

/-- The first matching union option parses its child before attempting its box. -/
theorem unionOption_child_failure (chosen selector : NatOperand) (desc : Desc)
    (rest : List (NatOperand × Desc)) (visit : Visit (((chosen, desc) :: rest).map Prod.snd))
    (input : Input) (arena : Delimited.ArenaState) (reason : Error)
    (selected : chosen.value = selector.value)
    (failed : (visit desc (by simp) input arena).result = .error reason) :
    unionOption ((chosen, desc) :: rest) visit selector input arena =
      ⟨.error reason, (visit desc (by simp) input arena).used,
        (visit desc (by simp) input arena).effects⟩ := by
  simp only [unionOption, selected, ↓reduceIte, bind, failed]

theorem unionOption_box_failure (chosen selector : NatOperand) (desc : Desc)
    (rest : List (NatOperand × Desc)) (visit : Visit (((chosen, desc) :: rest).map Prod.snd))
    (input : Input) (arena : Delimited.ArenaState) (child : Node)
    (selected : chosen.value = selector.value)
    (success : (visit desc (by simp) input arena).result = .ok child)
    (failed : TypedArena.reserve valueLayout arena.base arena.capacity
      (visit desc (by simp) input arena).used 1 = none) :
    unionOption ((chosen, desc) :: rest) visit selector input arena =
      ⟨.error scratch, (visit desc (by simp) input arena).used,
        (visit desc (by simp) input arena).effects ++
          [.reserve valueLayout 1 { arena with used := (visit desc (by simp) input arena).used } none]⟩ := by
  simp only [unionOption, selected, ↓reduceIte, bind, success, reserve, failed]

theorem unionOption_box_success (chosen selector : NatOperand) (desc : Desc)
    (rest : List (NatOperand × Desc)) (visit : Visit (((chosen, desc) :: rest).map Prod.snd))
    (input : Input) (arena : Delimited.ArenaState) (child : Node) (allocation : Arena.Reservation)
    (selected : chosen.value = selector.value)
    (success : (visit desc (by simp) input arena).result = .ok child)
    (reserved : TypedArena.reserve valueLayout arena.base arena.capacity
      (visit desc (by simp) input arena).used 1 = some allocation) :
    unionOption ((chosen, desc) :: rest) visit selector input arena =
      ⟨.ok (.union selector allocation child), allocation.used,
        (visit desc (by simp) input arena).effects ++
          [.reserve valueLayout 1 { arena with used := (visit desc (by simp) input arena).used }
            (some allocation), .writeValue allocation.pointer 0 child]⟩ := by
  simp only [unionOption, selected, ↓reduceIte, bind, success, reserve, reserved,
    writeValue, unchanged, Nat.mul_zero, Nat.add_zero, List.append_nil, List.singleton_append]

/-- Positive typed reservations expose the exact committed span and alignment.
The zero-length dangling case is deliberately excluded from pointer ownership. -/
theorem typedReserve_geometry (layout : TypedArena.Layout) (count : Nat)
    (arena : Delimited.ArenaState) (allocation : Arena.Reservation)
    (positive : 0 < count) (sizePositive : 0 < layout.size)
    (reserved : TypedArena.reserve layout arena.base arena.capacity arena.used count =
      some allocation) :
    arena.base + arena.used ≤ allocation.pointer ∧
    allocation.pointer % layout.alignment = 0 ∧
    allocation.pointer + layout.size * count = arena.base + allocation.used ∧
    allocation.used ≤ arena.capacity ∧ layout.size * count < 2 ^ 63 := by
  rw [TypedArena.reserve_positive _ _ _ _ _ positive sizePositive] at reserved
  split at reserved
  · rename_i checked
    cases reserved
    dsimp only
    refine ⟨?_, ?_, ?_, checked.2.2.2.2.2, checked.1⟩
    · unfold TypedArena.start
      omega
    · rw [TypedArena.start_pointer]
      exact TypedArena.aligned_mod _ _
    · simp only [TypedArena.finish, Nat.add_assoc]
  · cases reserved

theorem typedReserve_nonnull (layout : TypedArena.Layout) (count : Nat)
    (arena : Delimited.ArenaState) (allocation : Arena.Reservation)
    (valid : Arena.Valid arena.base arena.capacity arena.used)
    (reserved : TypedArena.reserve layout arena.base arena.capacity arena.used count =
      some allocation) : 0 < allocation.pointer := by
  unfold TypedArena.reserve at reserved
  split at reserved
  · cases reserved
    exact TypedArena.alignment_pos layout
  · split at reserved
    · cases reserved
      dsimp only
      have positive := valid.1
      omega
    · cases reserved

theorem valueReserve_count_lt (count : Nat) (arena : Delimited.ArenaState)
    (allocation : Arena.Reservation)
    (reserved : TypedArena.reserve valueLayout arena.base arena.capacity arena.used count =
      some allocation) : count < 2 ^ 64 := by
  by_cases zero : count = 0
  · subst count
    decide
  · have bound := (typedReserve_geometry valueLayout count arena allocation (by omega)
      (by decide) reserved).2.2.2.2
    change 48 * count < 2 ^ 63 at bound
    omega

/-- Slot commitment precedes the complete default-field initializer trace,
which in turn precedes every measurement or failing continuation effect. -/
theorem reserve_initializeSlots_success {α : Type} (count : Nat)
    (arena : Delimited.ArenaState) (allocation : Arena.Reservation)
    (next : Arena.Reservation → Nat → Outcome α)
    (reserved : TypedArena.reserve slotLayout arena.base arena.capacity arena.used count =
      some allocation) :
    bind (reserve slotLayout count arena) (fun slots used =>
      bind (initializeSlots count slots used) (fun _ used => next slots used)) =
      ⟨(next allocation allocation.used).result, (next allocation allocation.used).used,
        .reserve slotLayout count arena (some allocation) ::
          ((initializeSlots count allocation allocation.used).effects ++
            (next allocation allocation.used).effects)⟩ := by
  simp only [reserve, reserved, bind, initializeSlots, List.singleton_append]

theorem reserve_initializeSlots_failure {α : Type} (count : Nat)
    (arena : Delimited.ArenaState) (next : Arena.Reservation → Nat → Outcome α)
    (failed : TypedArena.reserve slotLayout arena.base arena.capacity arena.used count = none) :
    bind (reserve slotLayout count arena) (fun slots used =>
      bind (initializeSlots count slots used) (fun _ used => next slots used)) =
      ⟨.error scratch, arena.used, [.reserve slotLayout count arena none]⟩ := by
  simp only [reserve, failed, bind]

end SszNative.CodecDecode
