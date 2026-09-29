import SszCodecDecodeRefinementCore
import Ssz.Proofs.Codec.Table

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc Error)

/-- A local postcondition for stages which can fail only by exhausting scratch. -/
def StructSpec {α : Type} (outcome : Outcome α) (post : α → Prop) : Prop :=
  match outcome.result with
  | .ok value => post value
  | .error reason => reason = scratch

theorem structSpec_bind {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (pre : α → Prop) (post : β → Prop) (firstSpec : StructSpec first pre)
    (nextSpec : ∀ value used, pre value → StructSpec (next value used) post) :
    StructSpec (bind first next) post := by
  cases result : first.result with
  | error reason => simpa only [StructSpec, bind, result] using firstSpec
  | ok value =>
    have valid : pre value := by simpa only [StructSpec, result] using firstSpec
    simpa only [StructSpec, bind, result] using nextSpec value first.used valid

theorem structSpec_refines_bind {α β γ : Type} (first : Outcome α)
    (next : α → Nat → Outcome β) (pre : α → Prop) (erase : β → γ)
    (expected : Except Ssz.Err γ) (firstSpec : StructSpec first pre)
    (nextSpec : ∀ value used, pre value → Refines erase (next value used) expected) :
    Refines erase (bind first next) expected := by
  cases result : first.result with
  | error reason =>
    have exhausted : reason = scratch := by simpa only [StructSpec, result] using firstSpec
    exact Or.inr (by simp only [bind, result, exhausted])
  | ok value =>
    have valid : pre value := by simpa only [StructSpec, result] using firstSpec
    simpa only [Refines, bind, result] using nextSpec value first.used valid

theorem structSpec_reserve (layout : TypedArena.Layout) (count : Nat)
    (arena : Delimited.ArenaState) : StructSpec (reserve layout count arena) (fun _ => True) := by
  cases allocated : TypedArena.reserve layout arena.base arena.capacity arena.used count <;>
    simp [reserve, allocated, StructSpec]

theorem structSpec_fixedSize (desc : Desc) (arena : Delimited.ArenaState) :
    StructSpec (fixedSize desc arena)
      (fun width => width.map NatOperand.value = desc.erase.fixedSize) := by
  have spec := FixedSize.fixedSize_spec desc arena
  cases result : (FixedSize.fixedSize desc arena).result with
  | ok width =>
    simpa only [fixedSize, result, Except.mapError, StructSpec, FixedSize.ResultSpec] using spec
  | error reason =>
    have exhausted : reason = .arithmetic .scratchExhausted := by
      simpa only [FixedSize.ResultSpec, result] using spec
    simp only [fixedSize, result, Except.mapError, StructSpec, exhausted, scratch]

theorem structSpec_add (left right : NatOperand) (arena : Delimited.ArenaState) :
    StructSpec (add left right arena) (fun result => result.value = left.value + right.value) := by
  cases result : (NatAdd.run left right arena.base arena.capacity arena.used).result with
  | ok total =>
    simpa only [StructSpec, add, result, Except.mapError] using
      NatAdd.run_value left right arena.base arena.capacity arena.used total result
  | error reason =>
    cases reason with
    | scratchExhausted => simp only [StructSpec, add, result, Except.mapError, scratch]
    | badRepresentation =>
      exact False.elim (NatAdd.no_badRepresentation left right arena.base arena.capacity arena.used result)

def entryDescs {children : List Desc} (entries : List (Entry children)) : List Desc :=
  entries.map Entry.desc

def entryFields {children : List Desc} (entries : List (Entry children)) : List Ssz.Desc :=
  (entryDescs entries).map Desc.erase

def widthsCorrect {children : List Desc} (entries : List (Entry children)) : Prop :=
  ∀ entry ∈ entries, entry.slot.width.map NatOperand.value = entry.desc.erase.fixedSize

theorem fieldsFixedSize_isSome_cons (field : Ssz.Desc) (fields : List Ssz.Desc) :
    (Ssz.Desc.fieldsFixedSize (field :: fields)).isSome =
      (field.fixedSize.isSome && (Ssz.Desc.fieldsFixedSize fields).isSome) := by
  simp only [Ssz.Desc.fieldsFixedSize]
  cases field.fixedSize <;> cases Ssz.Desc.fieldsFixedSize fields <;> rfl

theorem fieldsFixedSize_leading (fields : List Ssz.Desc) (width : Nat)
    (fixed : Ssz.Desc.fieldsFixedSize fields = some width) :
    Ssz.Desc.leadingWidth fields = width := by
  induction fields generalizing width with
  | nil => simpa only [Ssz.Desc.fieldsFixedSize, Ssz.Desc.leadingWidth, Option.some.injEq] using fixed
  | cons field fields ih =>
    cases one : field.fixedSize <;> cases rest : Ssz.Desc.fieldsFixedSize fields <;>
      simp [Ssz.Desc.fieldsFixedSize, one, rest] at fixed
    rename_i head tail
    cases fixed
    simp only [Ssz.Desc.leadingWidth, one, Option.getD_some, ih tail rest]

/-- Every width is the pinned field width, and the accumulated header width and
fixedness retain all fields, including zero-width and noncanonical native Nats. -/
theorem measureSlots_spec {children : List Desc} (entries : List (Entry children))
    (allocation : Arena.Reservation) (index : Nat) (leading : NatOperand) (allFixed : Bool)
    (arena : Delimited.ArenaState) :
    StructSpec (measureSlots entries allocation index leading allFixed arena) (fun measured =>
      entryDescs measured.entries = entryDescs entries ∧
      widthsCorrect measured.entries ∧
      measured.leading.value = leading.value + Ssz.Desc.leadingWidth (entryFields entries) ∧
      measured.allFixed = (allFixed && (Ssz.Desc.fieldsFixedSize (entryFields entries)).isSome)) := by
  induction entries generalizing index leading allFixed arena with
  | nil => simp [measureSlots, unchanged, StructSpec, entryDescs, entryFields,
      widthsCorrect, Ssz.Desc.leadingWidth, Ssz.Desc.fieldsFixedSize]
  | cons entry rest ih =>
    simp only [measureSlots]
    apply structSpec_bind _ _ _ _ (structSpec_fixedSize entry.desc arena)
    intro width used measuredWidth
    have written : StructSpec
        (writeSlot allocation index { entry.slot with width := width } used) (fun _ => True) :=
      True.intro
    apply structSpec_bind _ _ _ _ written
    intro _ used _
    apply structSpec_bind _ _ _ _
      (structSpec_add leading (width.getD (.small 4)) { arena with used := used })
    intro total used totalValue
    apply structSpec_bind _ _ _ _
      (ih (index + 1) total (allFixed && width.isSome) { arena with used := used })
    intro measured used valid
    rcases valid with ⟨descs, widths, value, fixed⟩
    have widthValue : (width.getD (.small 4)).value = entry.desc.erase.fixedSize.getD 4 := by
      cases width <;> simp only [Option.map, Option.getD] at measuredWidth ⊢ <;>
        rw [← measuredWidth] <;> rfl
    have widthFixed : width.isSome = entry.desc.erase.fixedSize.isSome := by
      rw [← measuredWidth]
      cases width <;> rfl
    simp only [StructSpec, unchanged]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [entryDescs, List.map_cons] using congrArg (entry.desc :: ·) descs
    · intro next member
      rcases List.mem_cons.mp member with same | member
      · subst next; exact measuredWidth
      · exact widths next member
    · simp only [entryFields, entryDescs, List.map_cons, Ssz.Desc.leadingWidth]
      rw [value, totalValue, widthValue]
      exact Nat.add_assoc _ _ _
    · simp only [entryFields, entryDescs, List.map_cons, fieldsFixedSize_isSome_cons]
      rw [fixed, widthFixed, Bool.and_assoc]
      rfl

theorem initialEntries_descs (children : List Desc) :
    entryDescs (initialEntries children) = children := by
  simp [entryDescs, initialEntries, List.map_map]

theorem closeSlots_descs {children : List Desc} (entries : List (Entry children)) (scope : Nat) :
    entryDescs (closeSlots entries scope) = entryDescs entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simpa only [closeSlots, entryDescs, List.map_cons] using (congrArg (entry.desc :: ·) ih)

theorem struct_bind_success {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (value : β) (success : (bind first next).result = .ok value) :
    ∃ head, first.result = .ok head ∧ (next head first.used).result = .ok value := by
  cases result : first.result with
  | error reason =>
    simp only [bind, result] at success
    cases success
  | ok head => exact ⟨head, rfl, by simpa only [bind, result] using success⟩

theorem measureSlots_length_success {children : List Desc} (entries : List (Entry children))
    (allocation : Arena.Reservation) (index : Nat) (leading : NatOperand) (allFixed : Bool)
    (arena : Delimited.ArenaState) (measured : Measured children)
    (success : (measureSlots entries allocation index leading allFixed arena).result = .ok measured) :
    measured.entries.length = entries.length := by
  have spec := measureSlots_spec entries allocation index leading allFixed arena
  simp only [StructSpec, success] at spec
  have lengths := congrArg List.length spec.1
  simpa only [entryDescs, List.length_map] using lengths

end SszNative.CodecDecode
