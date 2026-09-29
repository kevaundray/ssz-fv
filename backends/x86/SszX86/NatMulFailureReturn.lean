import SszX86.NatMulZeroReturn

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem error_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (failed : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result =
      .error .scratchExhausted)
    (memory : t.dmem = pushedMem s) (output : t.regs.rdi = s.regs.rdi)
    (stack : t.regs.rsp = s.regs.rsp - 88) (simd : t.zmms = s.zmms) :
    Eventually (step e) (Post s left right address capacity used ra) (t, base + 318) := by
  have publish : PublishFrame s (pushedMem s) (errorMem (pushedMem s) s.regs.rdi.toBitVec)
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result := by
    rw [failed]
    exact error_publish_frame s _ _ owned.output_bound
  have work := (WorkFrame.initial s
    (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat)).publish publish
  apply error_publish_cps e base hc t
  · simpa only [OutputMapped, memory, output] using
      pushed_mapped s s.regs.rdi.toBitVec 72 owned.output_mapped
  apply return_cps e base hc s {t with dmem := errorMem t.dmem t.regs.rdi.toBitVec} ra stack
  · simpa only [memory, output] using work.saved owned
  · exact simd
  · simpa only [memory, output] using (work.to_frame owned.stack_low).return_slot owned
  intro u finalMemory returned
  apply error_post s left right address capacity used ra owned _ failed
  · simpa only [memory, output] using finalMemory
  · exact returned

theorem count_error_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (failed : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result =
      .error .scratchExhausted)
    (memory : t.dmem = pushedMem s) (output : t.regs.rdi = s.regs.rdi)
    (stack : t.regs.rsp = s.regs.rsp - 88) (simd : t.zmms = s.zmms) :
    Eventually (step e) (Post s left right address capacity used ra) (t, base + 746) := by
  have publish : PublishFrame s (pushedMem s) (countErrorMem (pushedMem s) s.regs.rdi.toBitVec)
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result := by
    rw [failed]
    exact count_error_publish_frame s _ _ owned.output_bound
  have work := (WorkFrame.initial s
    (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat)).publish publish
  apply count_error_publish_cps e base hc t
  · simpa only [OutputMapped, memory, output] using
      pushed_mapped s s.regs.rdi.toBitVec 72 owned.output_mapped
  apply return_cps e base hc s {t with dmem := countErrorMem t.dmem t.regs.rdi.toBitVec} ra stack
  · simpa only [memory, output] using work.saved owned
  · exact simd
  · simpa only [memory, output] using (work.to_frame owned.stack_low).return_slot owned
  intro u finalMemory returned
  apply count_error_post s left right address capacity used ra owned _ failed
  · simpa only [memory, output] using finalMemory
  · exact returned

end SszX86.NatMul
