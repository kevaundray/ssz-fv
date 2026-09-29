import SszArm.CodecMeasureContract
import SszArm.CodecStoragePlanOwned

set_option autoImplicit false

namespace SszArm.Codec.Measure.Provenance

open SszNative.CodecMeasure (Effect)
open Delimited (Span Protected MemoryFrame)

/-- Allocation provenance includes a physical span as well as separation.
WrittenAt alone intentionally does not imply nonwrapping memory geometry. -/
def WrittenOwned (writes : List Span) {α : Type}
    (call : SszNative.NatArithmetic.Outcome α) : Prop :=
  ∀ allocation, call.allocation = some allocation →
    allocation.pointer + 8 * call.written.length ≤ 2^64 ∧
      Protected writes allocation.pointer (8 * call.written.length)

def EffectOwned (writes : List Span) : Effect → Prop
  | .primitive _ _ _ measured => ∀ call ∈ measured.calls, WrittenOwned writes call
  | .arithmetic _ _ _ call => WrittenOwned writes call
  | .reservePlans _ _ _ => True
  | .writePlan address _ plan =>
      Protected writes address 40 ∧ Storage.PlanBackingsProtected writes plan

def EffectsOwned (writes : List Span) (effects : List Effect) : Prop :=
  ∀ effect ∈ effects, EffectOwned writes effect

theorem written_preserved {writes : List Span} {s t : ArmState} {α : Type}
    (call : SszNative.NatArithmetic.Outcome α) (owned : WrittenOwned writes call)
    (frame : MemoryFrame writes s t)
    (stored : NatDivision.WrittenAt (UintCodec.widthLoad s) call) :
    NatDivision.WrittenAt (UintCodec.widthLoad t) call := by
  intro allocation allocated index
  obtain ⟨physical, separated⟩ := owned allocation allocated
  have within := index.isLt
  have wordOwned := separated.subspan (8 * index.val) 8 (by omega)
  rw [frame.load (allocation.pointer + 8 * index.val) 8 (by omega) wordOwned]
  exact stored allocation allocated index

/-- Completed primitive limbs and initialized Plan prefixes survive later
writes only when the proven provenance separates their actual backing spans. -/
theorem effect_preserved {writes : List Span} {s t : ArmState} (effect : Effect)
    (owned : EffectOwned writes effect) (frame : MemoryFrame writes s t)
    (stored : EffectAt s effect) : EffectAt t effect := by
  cases effect with
  | primitive shape value arena measured =>
    intro call member
    exact written_preserved call (owned call member) frame (stored call member)
  | arithmetic left right arena call => exact written_preserved call owned frame stored
  | reservePlans count arena allocation => trivial
  | writePlan address index plan =>
    exact Storage.plan_at
      (Storage.plan_preserved (Storage.plan_owned plan stored owned.1 owned.2) frame)

theorem effects_preserved {writes : List Span} {s t : ArmState} (effects : List Effect)
    (owned : EffectsOwned writes effects) (frame : MemoryFrame writes s t)
    (stored : ∀ effect ∈ effects, EffectAt s effect) :
    ∀ effect ∈ effects, EffectAt t effect := by
  intro effect member
  exact effect_preserved effect (owned effect member) frame (stored effect member)

@[simp] theorem effectsOwned_nil (writes : List Span) : EffectsOwned writes [] := by
  intro effect member
  cases member

@[simp] theorem effectsOwned_cons (writes : List Span) (effect : Effect) (rest : List Effect) :
    EffectsOwned writes (effect :: rest) ↔ EffectOwned writes effect ∧ EffectsOwned writes rest := by
  constructor
  · intro owned
    exact ⟨owned effect (by simp), fun next member => owned next (List.mem_cons_of_mem _ member)⟩
  · rintro ⟨first, later⟩ next member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact later next member

@[simp] theorem effectsOwned_append (writes : List Span) (first later : List Effect) :
    EffectsOwned writes (first ++ later) ↔ EffectsOwned writes first ∧ EffectsOwned writes later := by
  constructor
  · intro owned
    exact ⟨fun effect member => owned effect (List.mem_append.mpr (Or.inl member)),
      fun effect member => owned effect (List.mem_append.mpr (Or.inr member))⟩
  · rintro ⟨before, after⟩ effect member
    rcases List.mem_append.mp member with earlier | later
    · exact before effect earlier
    · exact after effect later

end SszArm.Codec.Measure.Provenance
