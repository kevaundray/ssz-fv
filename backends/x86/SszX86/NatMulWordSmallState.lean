import SszX86.NatMulWordSmallMemory
import SszX86.NatMulWordProduct
import SszX86.NatMulWordReserveSmall

namespace SszX86.NatMulWord
open SszNative UintCodec

/-- Pure arithmetic preparation retains all physical anchors. The saved scalar
values live in the pushed memory; temporary scalar registers need not survive. -/
structure PureFrame (s t : MachineData) : Prop where
  memory : t.dmem = pushedMem s
  sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 64
  output : t.regs.rdi = s.regs.rdi
  arena : t.regs.r8 = s.regs.r8
  simd : t.zmms = s.zmms

structure WideReady (s t : MachineData) (wide : BitVec 128) : Prop extends PureFrame s t where
  low : t.regs.rax.toBitVec = wide.setWidth 64
  high : t.regs.rdx.toBitVec = (wide >>> 64).setWidth 64

theorem PureFrame.output_mapped {s t : MachineData} {operand : NatOperand}
    {factor address capacity used ra : BitVec 64} (owned : Owned s operand factor address capacity used ra)
    (frame : PureFrame s t) : OutputMapped t := by
  unfold OutputMapped
  rw [frame.memory, frame.output]
  exact pushed_mapped s _ _ owned.output_mapped

theorem PureFrame.header {s t : MachineData} {operand : NatOperand}
    {factor address capacity used ra : BitVec 64} (owned : Owned s operand factor address capacity used ra)
    (frame : PureFrame s t) : SmallReservation.Header t address capacity used := by
  have header := pushed_header s operand factor address capacity used ra owned
  constructor
  · simpa only [frame.memory, frame.arena] using header.1
  · simpa only [frame.memory, frame.arena, show (8 : BitVec 64) = 8#64 by decide] using header.2.1
  · simpa only [frame.memory, frame.arena, show (16 : BitVec 64) = 16#64 by decide] using header.2.2

theorem product_ready (s t : MachineData) (operand : NatOperand) (factor : BitVec 64)
    (frame : PureFrame s t) (low : t.regs.r9.toBitVec = SszNative.NatMul.lowWord operand)
    (factorReg : t.regs.rcx.toBitVec = factor) (flags : StatusFlags) :
    WideReady s (productState t flags) (SszNative.NatMul.wordProduct operand factor) := by
  refine ⟨⟨frame.memory, frame.sp, frame.output, frame.arena, frame.simd⟩, ?_, ?_⟩
  · simpa only [productState, UInt64.toBitVec_ofBitVec, low, factorReg,
      SszNative.NatMul.wordProduct] using mul_low (SszNative.NatMul.lowWord operand) factor
  · simpa only [productState, UInt64.toBitVec_ofBitVec, low, factorReg,
      SszNative.NatMul.wordProduct] using mul_high (SszNative.NatMul.lowWord operand) factor

theorem small_memory_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (small : operand.wordCount ≤ 1)
    (memory : t.dmem = smallResultMem s operand factor address capacity used)
    (sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 64) (simd : t.zmms = s.zmms) :
    Eventually (step e) (Post s operand factor address capacity used ra) (t, base + 687) := by
  exact finish_cps e base hc s t operand factor address capacity used ra owned
    (small_result_finished s t operand factor address capacity used ra owned nonzero notone small memory sp simd)

end SszX86.NatMulWord
