import SszX86.BitVectorErrorsMemory

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- Registers and private loads at the actual division-failure branch. -/
structure DivisionErrorReads (u : MachineData) (reason : NatArithmetic.Failure)
    (padding : BitVec 32) : Prop where
  text : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 120#64) 8 = some 1
  textLength : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 128#64) 8 = some 0
  firstPointer : u.regs.r13.toBitVec = 0#64
  firstPayload : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 40#64) 8 = some 0
  secondPointer : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 48#64) 8 = some 0
  secondPayload : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 56#64) 8 = some 0
  thirdPointer : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 64#64) 8 = some 0
  thirdPayload : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 72#64) 8 = some 0
  status : u.regs.rax.toBitVec.setWidth 32 = (arithmeticErrorImage reason padding).reason
  paddingWord : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 84#64) 4 = some (padding.toNat : Int)

/-- Complete arithmetic rejection, including copied padding and the real RET. -/
theorem division_error_terminal (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s u : MachineData) (saved : Saved) (data : Ssz.Bytes)
    (reason : NatArithmetic.Failure) (padding : BitVec 32)
    (h : ErrorSuffixAt s u saved) (inputReads : DivisionErrorReads u reason padding) :
    Eventually (step e) (Terminal s saved u.dmem data (.error (.arithmetic reason)))
      (u, base + 197) := by
  have high := h.stack_bound
  have low := h.stack_low
  have apart := h.output_work
  have frame := errors_division_frame s u (arithmeticErrorImage reason padding) h.output_bound
  have savedAfter := finish_saved s saved u.dmem _ low high h.output_saved h.current frame
  apply division_error_cps e base hc u s.regs.rdi.toBitVec
    (arithmeticErrorImage reason padding) h.output_mapped h.output_bound
  · simp only [h.stack, UInt64.toNat_toBitVec]
    omega
  · simp only [h.stack, UInt64.toNat_toBitVec]
    simp only [Body.Apart, workStart, workSize] at apart ⊢
    omega
  · exact h.output_cache
  · exact inputReads.text
  · exact inputReads.textLength
  · exact inputReads.firstPointer
  · exact inputReads.firstPayload
  · exact inputReads.secondPointer
  · exact inputReads.secondPayload
  · exact inputReads.thirdPointer
  · exact inputReads.thirdPayload
  · exact inputReads.status
  · exact inputReads.paddingWord
  apply epilogue_cps e base hc _ saved
  · simpa only [divisionErrorState, h.stack] using savedAfter
  refine ⟨?_, ?_, ?_⟩
  · exact division_arithmetic_observed u.dmem s.regs.rdi.toBitVec reason padding h.output_bound
  · apply finish_returned s (divisionErrorState u s.regs.rdi.toBitVec
      (arithmeticErrorImage reason padding)) saved h.original
    · exact h.stack
    · exact savedAfter
  · simpa only [finishRegions, returned] using frame

/-- The private add error is consumed as physical words, not as a future helper contract. -/
structure AddErrorReads (u : MachineData) (reason : NatArithmetic.Failure)
    (padding : BitVec 32) : Prop where
  text : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 16#64) 8 = some 1
  textLength : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 24#64) 8 = some 0
  firstPointer : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 32#64) 8 = some 0
  firstPayload : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 40#64) 8 = some 0
  secondPointer : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 48#64) 8 = some 0
  secondPayload : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 56#64) 8 = some 0
  thirdPointer : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 64#64) 8 = some 0
  thirdPayload : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 72#64) 8 = some 0
  status : u.regs.rax.toBitVec.setWidth 32 = (arithmeticErrorImage reason padding).reason
  paddingWord : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 84#64) 4 = some (padding.toNat : Int)

theorem add_error_terminal (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s u : MachineData) (saved : Saved) (data : Ssz.Bytes)
    (reason : NatArithmetic.Failure) (padding : BitVec 32)
    (h : ErrorSuffixAt s u saved) (inputReads : AddErrorReads u reason padding)
    (work : Large.Mapped u.dmem u.regs.rsp.toBitVec 224) :
    Eventually (step e) (Terminal s saved u.dmem data (.error (.arithmetic reason)))
      (u, base + 1776) := by
  have high := h.stack_bound
  have frame := errors_add_frame s u saved h (arithmeticAddImage reason padding)
  have savedAfter := finish_saved s saved u.dmem _ h.stack_low high h.output_saved h.current frame
  apply add_error_cps e base hc u s.regs.rdi.toBitVec
    (arithmeticAddImage reason padding) work h.output_mapped
  · simp only [h.stack, UInt64.toNat_toBitVec]
    omega
  · exact h.output_cache
  · exact inputReads.text
  · exact inputReads.textLength
  · exact inputReads.firstPointer
  · exact inputReads.firstPayload
  · exact inputReads.secondPointer
  · exact inputReads.secondPayload
  · exact inputReads.thirdPointer
  · exact inputReads.thirdPayload
  · exact inputReads.status
  · exact inputReads.paddingWord
  apply epilogue_cps e base hc _ saved
  · simpa only [addErrorState, addErrorStage, h.stack] using savedAfter
  refine ⟨?_, ?_, ?_⟩
  · exact add_arithmetic_observed _ s.regs.rdi.toBitVec reason padding h.output_bound
  · apply finish_returned s (addErrorState u s.regs.rdi.toBitVec
      (arithmeticAddImage reason padding)) saved h.original
    · exact h.stack
    · exact savedAfter
  · simpa only [finishRegions, returned] using frame

/-- Exact scope metadata keeps the original Nat pair and all nine native copy words. -/
structure ExactErrorReads (u : MachineData) (expected : NatOperand)
    (actual statusPadding : BitVec 64) : Prop where
  text : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 16#64) 8 = some 1
  textLength : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 24#64) 8 = some 0
  firstPointer : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 32#64) 8 = some (expected.pointer.toNat : Int)
  firstPayload : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 40#64) 8 = some (expected.payload.toNat : Int)
  secondPointer : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 48#64) 8 = some 0
  secondPayload : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 56#64) 8 = some (actual.toNat : Int)
  thirdPointer : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 64#64) 8 = some 0
  thirdPayload : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 72#64) 8 = some 0
  finalWord : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 80#64) 8 = some (statusPadding.toNat : Int)
  status : statusPadding.setWidth 32 = 3#32
  operand : expected.At (widthLoad u.dmem)

theorem exact_error_terminal (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s u : MachineData) (saved : Saved) (data : Ssz.Bytes)
    (expected : NatOperand) (actual statusPadding : BitVec 64)
    (h : ErrorSuffixAt s u saved) (inputReads : ExactErrorReads u expected actual statusPadding)
    (dataLength : actual.toNat = data.size) (slot : CallSlot u)
    (operandApart : ∀ pointer limbs, expected = .large pointer limbs →
      Body.Apart pointer.toNat (8 * limbs.length) s.regs.rdi.toNat 80 ∧
      Body.Apart pointer.toNat (8 * limbs.length) (workStart s) workSize) :
    Eventually (step e) (Terminal s saved u.dmem data (.error (.scope expected data.size)))
      (u, base + 4650) := by
  have high := h.stack_bound
  have frame := errors_exact_frame s u saved h (scopeErrorImage expected actual statusPadding)
  have savedAfter := finish_saved s saved u.dmem _ h.stack_low high h.output_saved h.current frame
  have operandAfter := frame.operand expected inputReads.operand (by
    intro pointer limbs he span member
    have separated := operandApart pointer limbs he
    simp only [finishRegions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact separated.1
    · exact separated.2)
  apply exact_error_cps e base hc u s.regs.rdi.toBitVec
    (scopeErrorImage expected actual statusPadding) h.output_mapped slot
  · simpa only [h.stack, UInt64.toNat_toBitVec] using h.stack_low
  · simp only [h.stack, UInt64.toNat_toBitVec]
    omega
  · exact h.output_bound
  · simpa only [h.stack, UInt64.toNat_toBitVec, workStart, workSize] using h.output_work
  · exact h.output_cache
  · exact inputReads.text
  · exact inputReads.textLength
  · exact inputReads.firstPointer
  · exact inputReads.firstPayload
  · exact inputReads.secondPointer
  · exact inputReads.secondPayload
  · exact inputReads.thirdPointer
  · exact inputReads.thirdPayload
  · exact inputReads.finalWord
  apply epilogue_cps e base hc _ saved
  · simpa only [exactErrorState, h.stack] using savedAfter
  refine ⟨?_, ?_, ?_⟩
  · simpa only [SszNative.BitVector.ResultAt, dataLength, returned, exactErrorState,
      UInt64.toNat_toBitVec] using
      scope_error_observed _ s.regs.rdi.toBitVec expected actual statusPadding
        h.output_bound inputReads.status operandAfter
  · apply finish_returned s (exactErrorState u s.regs.rdi.toBitVec
      (scopeErrorImage expected actual statusPadding)) saved h.original
    · exact h.stack
    · exact savedAfter
  · simpa only [finishRegions, returned] using frame

end SszX86.BitVector
