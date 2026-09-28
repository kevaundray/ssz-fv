import SszX86.NatMulOutput
import SszX86.NatMulReturn
import SszX86.NatMulMemoryFinish

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem zero_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (zero : left.wordCount = 0 ∨ right.wordCount = 0)
    (memory : t.dmem = pushedMem s) (output : t.regs.rdi = s.regs.rdi)
    (stack : t.regs.rsp = s.regs.rsp - 88) (simd : t.zmms = s.zmms) :
    Eventually (step e) (Post s left right address capacity used ra) (t, base + 206) := by
  have model := SszNative.NatMul.run_zero left right address.toNat capacity.toNat used.toNat zero
  have publish : PublishFrame s (pushedMem s) (zeroMem (pushedMem s) s.regs.rdi.toBitVec)
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result := by
    rw [model]
    exact zero_publish_frame s _ owned.output_bound
  have work := (WorkFrame.initial s
    (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat)).publish publish
  apply zero_publish_cps e base hc t
  · simpa only [OutputMapped, memory, output] using
      pushed_mapped s s.regs.rdi.toBitVec 72 owned.output_mapped
  apply return_cps e base hc s _ ra
  · exact stack
  · simpa only [memory, output] using work.saved owned
  · exact simd
  · simpa only [memory, output] using (work.to_frame owned.stack_low).return_slot owned
  intro u finalMemory returned
  apply zero_post s left right address capacity used ra owned _ zero
  · simpa only [memory, output] using finalMemory
  · exact returned

end SszX86.NatMul
