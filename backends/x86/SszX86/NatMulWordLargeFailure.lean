import SszX86.NatMulWordLargeMemoryResources
import SszX86.NatMulWordReturn

namespace SszX86.NatMulWord
open SszNative UintCodec

theorem large_error_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (model : SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
      NatArithmetic.unchanged used.toNat (.error .scratchExhausted))
    (memory : t.dmem = pushedMem s) (output : t.regs.rdi = s.regs.rdi)
    (sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec-64) (vectors : t.zmms = s.zmms) :
    Eventually (step e) (Post s operand factor address capacity used ra) (t, base+617) := by
  have publish := NatMul.error_publish_frame s (pushedMem s) .scratchExhausted owned.output_bound
  have work : WorkFrame s (errorMem (pushedMem s) s.regs.rdi.toBitVec)
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat) := by
    apply (WorkFrame.initial s _).publish
    simpa only [model, NatArithmetic.unchanged] using publish
  have header := pushed_header s operand factor address capacity used ra owned
  have usedLoad : Mem.loadInt (pushedMem s) (s.regs.r8.toBitVec+16#64) 8 = some (used.toNat : Int) := by
    simpa only [show (16 : BitVec 64) = 16#64 by decide] using header.2.2
  have cursor : widthLoad (pushedMem s) (s.regs.r8.toNat+16) 8 = some used.toNat := by
    change (Mem.loadInt (pushedMem s) (BitVec.ofNat 64 (s.regs.r8.toBitVec.toNat+16)) 8).map Int.toNat = _
    rw [width_address, usedLoad]
    rfl
  have publishedCursor := (large_publish_cursor s operand factor address capacity used ra owned _ _ _ publish).trans cursor
  apply error_cps e base hc t
  · simpa only [OutputMapped, memory, output] using pushed_mapped s _ _ owned.output_mapped
  apply finish_cps e base hc s _ operand factor address capacity used ra owned
  refine ⟨?_, ?_, ?_, ?_, sp, ?_, vectors⟩
  · rw [model]
    change NatArithmetic.errorAt (widthLoad (errorMem t.dmem t.regs.rdi.toBitVec))
      s.regs.rdi.toBitVec.toNat .scratchExhausted
    rw [memory, output]
    exact NatMul.error_reads (pushedMem s) s.regs.rdi.toBitVec
  · intro r allocated
    simp only [model, NatArithmetic.unchanged] at allocated
    cases allocated
  · simpa only [memory, output] using work.to_frame owned.stack_low
  · simpa only [memory, output, model, NatArithmetic.unchanged] using publishedCursor
  · have savedAddress : s.regs.rsp.toBitVec-64+16 = s.regs.rsp.toBitVec-48 := by bv_omega
    simpa only [memory, output, sp, savedAddress] using work.saved owned

end SszX86.NatMulWord
