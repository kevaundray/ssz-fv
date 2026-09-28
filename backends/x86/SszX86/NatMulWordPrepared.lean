import SszX86.NatMulWordSmallState
import SszX86.NatMulWordCountFinish

namespace SszX86.NatMulWord
open SszNative

/-- The exact register invariant at the allocating word branch, derived by the
physical trailing-zero scan; all memory is still just the activation pushes. -/
structure MultiplyReady (s t : MachineData) (operand : NatOperand) (factor : BitVec 64) : Prop
    extends PureFrame s t where
  input : t.regs.rsi.toBitVec = operand.pointer
  payload : t.regs.r9.toBitVec = BitVec.ofNat 64 operand.words.length
  factorReg : t.regs.rcx.toBitVec = factor
  count : t.regs.r15.toBitVec = BitVec.ofNat 64 operand.wordCount
  counter : t.regs.rbx.toBitVec = BitVec.ofNat 64 (operand.wordCount+2)
  skipped : t.regs.r11.toBitVec = BitVec.ofNat 64 (operand.words.length-operand.wordCount)

theorem PureFrame.counted {s t : MachineData} (frame : PureFrame s t)
    (b skipped saved : BitVec 64) (flags : StatusFlags) : PureFrame s (countState t b skipped saved flags) :=
  ⟨frame.memory, frame.sp, frame.output, frame.arena, frame.simd⟩

end SszX86.NatMulWord
