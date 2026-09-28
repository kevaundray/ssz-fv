import SszX86.NatMulWordLargeMath
import SszX86.NatMulWordPrepared

namespace SszX86.NatMulWord
open SszNative

/-- The concrete original loop-entry registers after the first product/store.
Memory facts are independently derived from the actual executed stores. -/
structure LargeLoopRegisters (s t : MachineData) (operand : NatOperand)
    (factor address : BitVec 64) (r : Arena.Reservation) : Prop where
  sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec-64
  output : t.regs.rdi = s.regs.rdi
  simd : t.zmms = s.zmms
  input : t.regs.rsi.toBitVec = operand.pointer
  payload : t.regs.r9.toBitVec = BitVec.ofNat 64 operand.words.length
  factorReg : t.regs.rcx.toBitVec = factor
  count : t.regs.r15.toBitVec = BitVec.ofNat 64 operand.wordCount
  counter : t.regs.rbx.toBitVec = BitVec.ofNat 64 (operand.wordCount+2)
  paired : t.regs.r12.toBitVec = BitVec.ofNat 64 (2*(operand.wordCount/2))
  destination : t.regs.rbp.toBitVec = BitVec.ofNat 64 r.pointer+8#64
  index : t.regs.rax.toBitVec = 1#64
  carry : t.regs.r10.toBitVec = BitVec.ofNat 64 (firstResult operand factor).2
  arenaBase : t.regs.r14.toBitVec = address

end SszX86.NatMulWord
