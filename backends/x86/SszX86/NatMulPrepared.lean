import SszX86.NatMulSmallLeft
import SszX86.NatMulSmallRight
import SszX86.NatMulSelect
import SszNatMul

namespace SszX86.NatMul
open SszNative

structure CountReady (s t : MachineData) (left right : NatOperand) : Prop where
  frame : ControlFrame s t
  left_pointer : t.regs.rsi.toBitVec = left.pointer
  left_payload : t.regs.rax.toBitVec = left.payload
  right_pointer : t.regs.rcx.toBitVec = right.pointer
  left_count : t.regs.r12.toBitVec = BitVec.ofNat 64 left.wordCount
  right_count : t.regs.r13.toBitVec = BitVec.ofNat 64 right.wordCount
  right_countdown : t.regs.r10.toBitVec = 1 - BitVec.ofNat 64 right.wordCount

inductive Prepared (s : MachineData) (left right : NatOperand) (base : Int64)
    (t : MachineState) : Prop where
  | zero (empty : left.wordCount = 0 ∨ right.wordCount = 0)
      (frame : ControlFrame s t.1) (pc : t.2 = base + 206)
  | word_left (leftNonzero : left.wordCount ≠ 0) (rightOne : right.wordCount = 1)
      (frame : ControlFrame s t.1)
      (pointer : t.1.regs.rsi.toBitVec = left.pointer)
      (payload : t.1.regs.rdx.toBitVec = left.payload)
      (factor : t.1.regs.rcx.toBitVec = SszNative.NatMul.lowWord right)
      (pc : t.2 = base + 184)
  | word_right (leftOne : left.wordCount = 1) (rightNonzero : right.wordCount ≠ 0)
      (rightNotOne : right.wordCount ≠ 1) (frame : ControlFrame s t.1)
      (pointer : t.1.regs.rsi.toBitVec = right.pointer)
      (payload : t.1.regs.rdx.toBitVec = right.payload)
      (factor : t.1.regs.rcx.toBitVec = SszNative.NatMul.lowWord left)
      (pc : t.2 = base + 184)
  | counted (leftMany : 1 < left.wordCount) (rightMany : 1 < right.wordCount)
      (ready : CountReady s t.1 left right) (pc : t.2 = base + 275)

theorem Prepared.rebase {s u : MachineData} {left right : NatOperand} {base : Int64}
    {t : MachineState} (frame : ControlFrame s u) (prepared : Prepared u left right base t) :
    Prepared s left right base t := by
  cases prepared with
  | zero empty rest pc => exact .zero empty (frame.trans rest) pc
  | word_left nonzero one rest pointer payload factor pc =>
    exact .word_left nonzero one (frame.trans rest) pointer payload factor pc
  | word_right one nonzero notone rest pointer payload factor pc =>
    exact .word_right one nonzero notone (frame.trans rest) pointer payload factor pc
  | counted leftMany rightMany ready pc =>
    exact .counted leftMany rightMany
      ⟨frame.trans ready.frame, ready.left_pointer, ready.left_payload, ready.right_pointer,
        ready.left_count, ready.right_count, ready.right_countdown⟩ pc

end SszX86.NatMul
