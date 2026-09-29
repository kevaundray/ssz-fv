import SszArm.IndicesElementTypeContract
import SszArm.UintResultMemory

set_option autoImplicit false

namespace SszArm.Indices.ElementType

open SszNative.Codec (Desc)
open SszNative.Indices (PathStep)

namespace Dispatch

theorem Op.register (op : Op) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [8#5, 9#5, 10#5]) :
    r (.GPR reg) (op.effect s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at untouched
  cases op <;> simp [Op.effect, put, SszArm.Emit.Dispatch.next,
    SszArm.Emit.Dispatch.branch, SszArm.Emit.Dispatch.compare64,
    state_simp_rules, untouched.1, untouched.2.1, untouched.2.2]

theorem block_register (ops : List Op) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [8#5, 9#5, 10#5]) :
    r (.GPR reg) (block ops s) = r (.GPR reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction => exact (induction _).trans (op.register s reg untouched)

@[simp] theorem block_program (ops : List Op) (s : ArmState) :
    (block ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction => exact (induction _).trans (op.program s)

@[simp] theorem block_error (ops : List Op) (s : ArmState) :
    read_err (block ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction => exact (induction _).trans (op.error s)

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, put, SszArm.Emit.Dispatch.next,
    SszArm.Emit.Dispatch.branch, SszArm.Emit.Dispatch.compare64, state_simp_rules]

@[simp] theorem block_vector (ops : List Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (block ops s) = r (.SFP reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction => exact (induction _).trans (op.vector s reg)

end Dispatch

@[simp] theorem dispatched_program (s : ArmState) (shape : Desc) (step : PathStep) :
    (dispatched s shape step).program = s.program := by
  simp [dispatched]

@[simp] theorem dispatched_error (s : ArmState) (shape : Desc) (step : PathStep) :
    read_err (dispatched s shape step) = read_err s := by
  simp [dispatched]

@[simp] theorem dispatched_memory (s : ArmState) (shape : Desc) (step : PathStep) :
    (dispatched s shape step).mem = (entered s).mem := dispatch_memory _ _

@[simp] theorem dispatched_sp (s : ArmState) (shape : Desc) (step : PathStep) :
    r (.GPR 31#5) (dispatched s shape step) = r (.GPR 31#5) s - 16#64 := by
  rw [dispatched, Dispatch.block_register _ _ _ (by decide), entered_sp]

theorem dispatched_aligned (s : ArmState) (shape : Desc) (step : PathStep)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (dispatched s shape step) := by
  have lower := BooleanBody.Op.aligned .p60 s aligned
  simpa only [BooleanBody.Op.effect, BooleanBody.put, BooleanBody.next,
    CheckSPAlignment, read_gpr, BitVec.setWidth_eq, state_simp_rules, dispatched_sp] using lower

theorem dispatched_register (s : ArmState) (shape : Desc) (step : PathStep) (reg : BitVec 5)
    (untouched : reg ∉ [8#5, 9#5, 10#5, 31#5]) :
    r (.GPR reg) (dispatched s shape step) = r (.GPR reg) s := by
  have dispatchUntouched : reg ∉ [8#5, 9#5, 10#5] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at untouched ⊢
    exact ⟨untouched.1, untouched.2.1, untouched.2.2.1⟩
  rw [dispatched, Dispatch.block_register _ _ _ dispatchUntouched]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at untouched
  simp [entered, saved, loadDescriptor, loadStep, state_simp_rules,
    untouched.1, untouched.2.1, untouched.2.2.2]

@[simp] theorem dispatched_vector (s : ArmState) (shape : Desc) (step : PathStep)
    (reg : BitVec 5) : r (.SFP reg) (dispatched s shape step) = r (.SFP reg) s := by
  simp [dispatched, entered, saved, loadDescriptor, loadStep, state_simp_rules]

theorem Owned.bodyGeometry {s : ArmState} {shape : Desc} {step : PathStep}
    (owned : Owned s shape step) : BooleanBody.Geometry (dispatched s shape step) := by
  have out := dispatched_register s shape step 0#5 (by decide)
  have sp := dispatched_sp s shape step
  have low := owned.stackLow
  have bound := (r (.GPR 31#5) s).isLt
  have pointer : (r (.GPR 31#5) s - 16#64).toNat =
      (r (.GPR 31#5) s).toNat - 16 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [sp, pointer]
    omega
  · simpa only [out] using owned.output
  · rw [out, sp, pointer]
    have separate := owned.outputStack
    omega

/-- The real paired entry store initializes both saved words; no saved-memory
premise is required from the caller. -/
theorem entered_saved (s : ArmState) (low : 32 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (entered s) = r (.GPR 30#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64 + 8#64) (entered s) = r (.GPR 19#5) s := by
  have bound := (r (.GPR 31#5) s).isLt
  have pointer : (r (.GPR 31#5) s - 16#64).toNat =
      (r (.GPR 31#5) s).toNat - 16 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have nextPointer : (r (.GPR 31#5) s - 16#64 + 8#64).toNat =
      (r (.GPR 31#5) s).toNat - 8 := by
    simp only [BitVec.toNat_add, pointer, BitVec.toNat_ofNat]
    omega
  rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp (entered_memory s),
    Memory.mem_eq_iff_read_mem_bytes_eq.mp (entered_memory s)]
  simp (disch := (simp only [pointer, nextPointer]; omega)) only
    [UintCodec.Tail.write_pair_words, BoolCodec.read_mem_bytes_write_mem_bytes_same,
     BoolCodec.read_mem_bytes_write_mem_bytes_disjoint, and_self]

end SszArm.Indices.ElementType
