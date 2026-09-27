import SszX86.NatAddSelectPhase

namespace SszX86.NatAdd
open SszNative

/-- All allocation-free control exits of the actual preparation prefix. Zero
branches have normalized the borrowed result; nonzero branches retain the
original operands alongside either their counts or their full one-word sum. -/
inductive Prepared (s : MachineData) (left right : NatOperand) (base : Int64)
    (t : MachineState) : Prop where
  | zero_left (zero : left.wordCount = 0) (frame : ControlFrame s t.1)
      (pointer : t.1.regs.rcx.toBitVec = right.normalized.pointer)
      (payload : t.1.regs.r8.toBitVec = right.normalized.payload)
      (pc : t.2 = base + 585)
  | zero_right (nonzero : left.wordCount ≠ 0) (zero : right.wordCount = 0)
      (frame : ControlFrame s t.1)
      (pointer : t.1.regs.rsi.toBitVec = left.normalized.pointer)
      (payload : t.1.regs.rdx.toBitVec = left.normalized.payload)
      (pc : t.2 = base + 598)
  | counted (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
      (ready : CountReady s t.1 left right) (pc : t.2 = base + 193)
  | summed (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
      (small : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1)
      (ready : SumReady s t.1 left right) (pc : t.2 = sumTarget left right base)

theorem Prepared.rebase {s u : MachineData} {left right : NatOperand} {base : Int64}
    {t : MachineState} (frame : ControlFrame s u) (prepared : Prepared u left right base t) :
    Prepared s left right base t := by
  cases prepared with
  | zero_left zero rest pointer payload pc =>
    exact .zero_left zero (frame.trans rest) pointer payload pc
  | zero_right nonzero zero rest pointer payload pc =>
    exact .zero_right nonzero zero (frame.trans rest) pointer payload pc
  | counted leftNonzero rightNonzero ready pc =>
    exact .counted leftNonzero rightNonzero
      ⟨frame.trans ready.frame, ready.left_pointer, ready.left_payload,
        ready.right_pointer, ready.right_payload, ready.left_count, ready.right_count, ready.marker⟩ pc
  | summed leftNonzero rightNonzero small ready pc =>
    exact .summed leftNonzero rightNonzero small ⟨frame.trans ready.frame, ready.low, ready.high⟩ pc

end SszX86.NatAdd
