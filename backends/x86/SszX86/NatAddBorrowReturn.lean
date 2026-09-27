import SszX86.NatAddReturn
import SszX86.NatAddInitialMemory

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem unchanged_memory_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (frame : ControlFrame (pushedState s) t) (result : NatOperand)
    (model : SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat =
      NatArithmetic.unchanged used.toNat (.ok result)) :
    Eventually (step e) (Post s left right address capacity used ra)
      ({t with dmem := successMem t.dmem s.regs.rdi.toBitVec result.pointer result.payload}, base+612) := by
  refine success_memory_finish_cps e base hc s t left right address capacity used ra owned
    (frame.work _) ?_ ?_ frame.sp frame.original_simd result ?_
  · intro r allocated
    rw [model] at allocated
    cases allocated
  · rw [model]
    exact frame.cursor owned
  · rw [model]
    rfl

/-- Left zero is tested first, so the right representation is normalized and
borrowed even when both significant counts vanish. -/
theorem zero_left_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (frame : ControlFrame (pushedState s) t) (zero : left.wordCount = 0)
    (pointer : t.regs.rcx.toBitVec = right.normalized.pointer)
    (payload : t.regs.r8.toBitVec = right.normalized.payload) :
    Eventually (step e) (Post s left right address capacity used ra) (t,base+585) := by
  apply right_publish_cps e base hc t (frame.output_mapped owned)
  have out : t.regs.rdi.toBitVec = s.regs.rdi.toBitVec := by rw [frame.output]; rfl
  rw [out, pointer, payload]
  exact unchanged_memory_finish_cps e base hc s t left right address capacity used ra owned frame _
    (SszNative.NatAdd.run_zero_left left right address.toNat capacity.toNat used.toNat zero)

/-- Right zero borrows the normalized left without changing the arena cursor. -/
theorem zero_right_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (frame : ControlFrame (pushedState s) t) (nonzero : left.wordCount ≠ 0) (zero : right.wordCount = 0)
    (pointer : t.regs.rsi.toBitVec = left.normalized.pointer)
    (payload : t.regs.rdx.toBitVec = left.normalized.payload) :
    Eventually (step e) (Post s left right address capacity used ra) (t,base+598) := by
  apply left_publish_cps e base hc t (frame.output_mapped owned)
  have out : t.regs.rdi.toBitVec = s.regs.rdi.toBitVec := by rw [frame.output]; rfl
  rw [out, pointer, payload]
  exact unchanged_memory_finish_cps e base hc s t left right address capacity used ra owned frame _
    (SszNative.NatAdd.run_zero_right left right address.toNat capacity.toNat used.toNat nonzero zero)

end SszX86.NatAdd
