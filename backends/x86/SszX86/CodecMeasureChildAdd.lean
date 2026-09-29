import SszX86.CodecMeasureChildHelpers
import SszX86.NatAddProofs

namespace SszX86.CodecMeasureChild
open SszNative

/-- The variable-head addition runs the checked native Nat helper all the way to
PC324, including any retained limb allocation and exact error publication. -/
theorem leading_add_correct (e : Executable) (base : Int64) (code : CodeAt e base)
    (addCode : NatAdd.CodeAt e (base + Int64.ofInt natAddOffset))
    (s : MachineData) (left : NatOperand) (address capacity used : BitVec 64)
    (slot : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (owned : NatAdd.Owned (callState s (base + 324).toBitVec)
      left (.small 4) address capacity used (base + 324).toBitVec) :
    Eventually (step e) (NatAdd.Post (callState s (base + 324).toBitVec)
      left (.small 4) address capacity used (base + 324).toBitVec) (s, base + 319) := by
  apply leading_add_call e base code s _ slot
  exact NatAdd.add_correct e (base + Int64.ofInt natAddOffset) addCode
    (callState s (base + 324).toBitVec) left (.small 4) address capacity used
    (base + 324).toBitVec owned

/-- The body/common inline addition is a separate actual call with its own exact
committed cursor, result and outside-write frame, on both success and failure. -/
theorem size_add_correct (e : Executable) (base : Int64) (code : CodeAt e base)
    (addCode : NatAdd.CodeAt e (base + Int64.ofInt natAddOffset))
    (s : MachineData) (left right : NatOperand) (address capacity used : BitVec 64)
    (slot : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (owned : NatAdd.Owned (callState s (base + 391).toBitVec)
      left right address capacity used (base + 391).toBitVec) :
    Eventually (step e) (NatAdd.Post (callState s (base + 391).toBitVec)
      left right address capacity used (base + 391).toBitVec) (s, base + 386) := by
  apply size_add_call e base code s _ slot
  exact NatAdd.add_correct e (base + Int64.ofInt natAddOffset) addCode
    (callState s (base + 391).toBitVec) left right address capacity used
    (base + 391).toBitVec owned

end SszX86.CodecMeasureChild
