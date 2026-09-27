import SszX86.NatAddReturn
import SszX86.NatAddInitialMemory

namespace SszX86.NatAdd
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Failed reservation publishes the exact arithmetic error and returns with
an unchanged cursor, not a successful-reservation premise. -/
theorem reserve_failure_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (frame : ControlFrame (pushedState s) t)
    (empty : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = none)
    (failure : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).result = .error .scratchExhausted) :
    Eventually (step e) (Post s left right address capacity used ra) (t,base+766) := by
  apply error_publish_cps e base hc t (frame.output_mapped owned)
  have out : t.regs.rdi.toBitVec = s.regs.rdi.toBitVec := by rw [frame.output]; rfl
  rw [out]
  apply error_memory_finish_cps e base hc s t left right address capacity used ra owned
    (frame.work _) empty _ frame.sp frame.original_simd failure
  rw [(SszNative.NatAdd.no_allocation_resources left right address.toNat capacity.toNat used.toNat empty).1]
  exact frame.cursor owned

/-- The actual count-overflow site has a separate store order but the same
scratch-exhausted result and unchanged allocator resources. -/
theorem count_failure_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (frame : ControlFrame (pushedState s) t)
    (empty : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = none)
    (failure : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).result = .error .scratchExhausted) :
    Eventually (step e) (Post s left right address capacity used ra) (t,base+1399) := by
  apply count_error_publish_cps e base hc t (frame.output_mapped owned)
  have out : t.regs.rdi.toBitVec = s.regs.rdi.toBitVec := by rw [frame.output]; rfl
  rw [out]
  apply count_error_memory_finish_cps e base hc s t left right address capacity used ra owned
    (frame.work _) empty _ frame.sp frame.original_simd failure
  rw [(SszNative.NatAdd.no_allocation_resources left right address.toNat capacity.toNat used.toNat empty).1]
  exact frame.cursor owned

end SszX86.NatAdd
