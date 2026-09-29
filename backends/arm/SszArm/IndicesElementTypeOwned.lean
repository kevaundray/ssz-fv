import SszArm.IndicesElementTypeEntry
import SszArm.IndicesElementTypeRoutes
import SszArm.IndicesStorage
import SszArm.CodecStorageProjection

set_option autoImplicit false

namespace SszArm.Indices.ElementType

open SszNative.Codec (Desc)
open SszNative.Indices (PathStep)
open Codec.Storage (Image)

def stepTag : PathStep → BitVec 64
  | .position _ => 0
  | .length => 1
  | .activeFields => 2
  | .selector => 3

def stepPosition : PathStep → Bool
  | .position _ => true
  | _ => false

theorem descriptor_tag {protect : Nat → Nat → Prop} {s : ArmState}
    {address : Nat} (shape : Desc)
    (input : (Codec.Storage.desc address shape).Holds protect s) :
    read_mem_bytes 8 (BitVec.ofNat 64 address) s = (Dispatch.Kind.ofDesc shape).tag := by
  cases shape with
  | primitive shape =>
      cases shape <;> exact Codec.Storage.word_bits _ input.2.1
  | vector _ _ | list _ _ | progressiveList _ _ | container _
  | progressiveContainer _ _ | compatibleUnion _ =>
      exact Codec.Storage.word_bits _ input.2.1

theorem path_tag {protect : Nat → Nat → Prop} {s : ArmState}
    {address : Nat} (step : PathStep)
    (input : (Storage.pathStep address step).Holds protect s) :
    read_mem_bytes 8 (BitVec.ofNat 64 address) s = stepTag step := by
  cases step with
  | position _ => exact Codec.Storage.word_bits _ input.2.1
  | length | activeFields | selector => exact Codec.Storage.word_bits _ input.2

/-- Tags are taken from actual memory after the saved-register store. -/
theorem entered_descriptor_read (s : ArmState) :
    r (.GPR 8#5) (entered s) = read_mem_bytes 8 (r (.GPR 1#5) s) (entered s) := by
  simp [entered, saved, loadDescriptor, loadStep, state_simp_rules]

theorem entered_path_read (s : ArmState) :
    r (.GPR 9#5) (entered s) = read_mem_bytes 8 (r (.GPR 2#5) s) (entered s) := by
  simp [entered, saved, loadDescriptor, loadStep, state_simp_rules]

structure EntryOwned (s : ArmState) (shape : Desc) (step : PathStep) : Prop where
  stackLow : 16 ≤ (r (.GPR 31#5) s).toNat
  descriptor : Codec.Storage.DescOwned (entryWrites s) s (r (.GPR 1#5) s).toNat shape
  path : (Storage.pathStep (r (.GPR 2#5) s).toNat step).Owned (entryWrites s) s

theorem EntryOwned.entered_tag {s : ArmState} {shape : Desc} {step : PathStep}
    (owned : EntryOwned s shape step) :
    r (.GPR 8#5) (entered s) = (Dispatch.Kind.ofDesc shape).tag := by
  rw [entered_descriptor_read]
  have tag := descriptor_tag shape (descriptor_preserved owned.descriptor owned.stackLow)
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using tag

theorem EntryOwned.entered_step {s : ArmState} {shape : Desc} {step : PathStep}
    (owned : EntryOwned s shape step) :
    r (.GPR 9#5) (entered s) = stepTag step := by
  rw [entered_path_read]
  have preserved := Image.preserved _ (entered_frame s owned.stackLow) owned.path
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using path_tag step preserved

theorem dispatch_memory (ops : List Dispatch.Op) (s : ArmState) :
    (Dispatch.block ops s).mem = s.mem := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction => exact (induction _).trans (op.memory s)

/-- This is the concrete state at the selected body entry, including the original
save, tag loads, flag updates, and every taken or untaken branch. -/
def dispatched (s : ArmState) (shape : Desc) (step : PathStep) : ArmState :=
  Dispatch.block ((Dispatch.Kind.ofDesc shape).ops (stepPosition step)) (entered s)

theorem entry_dispatch_run (s : ArmState) (base : BitVec 64) (shape : Desc) (step : PathStep)
    (owned : EntryOwned s shape step)
    (code : Linked.ElementType.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    run (3 + ((Dispatch.Kind.ofDesc shape).ops (stepPosition step)).length) s =
      dispatched s shape step ∧
    read_pc (dispatched s shape step) =
      base + BitVec.ofNat 64 ((Dispatch.Kind.ofDesc shape).destination (stepPosition step)) := by
  have enteredPC : read_pc (entered s) = base + 12#64 := by rw [entered_pc, pc]
  have zero : r (.GPR 9#5) (entered s) = 0#64 ↔ stepPosition step = true := by
    rw [owned.entered_step]
    cases step <;> decide
  have route := Dispatch.route_run (Dispatch.Kind.ofDesc shape) (stepPosition step)
    (entered s) base (Codec.Linked.WordsAt.preserve code (entered_program s))
    ((entered_error s).trans error) enteredPC owned.entered_tag zero
  refine ⟨?_, route.2⟩
  rw [run_plus, entry_run s base code error aligned pc]
  exact route.1

theorem dispatched_frame {s : ArmState} {shape : Desc} {step : PathStep}
    (owned : EntryOwned s shape step) :
    Delimited.MemoryFrame (entryWrites s) s (dispatched s shape step) := by
  intro address outside
  exact (congrFun (dispatch_memory _ _) address).trans
    (entered_frame s owned.stackLow address outside)

end SszArm.Indices.ElementType
