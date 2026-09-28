import SszX86.BitVectorFinishMemory
import SszX86.BitVectorErrorFields
import SszX86.BitVectorAddErrorFrame
import SszX86.BitVectorExactErrorFields

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- Physical facts at a reached rejection branch, tied to the original activation. -/
structure ErrorSuffixAt (s u : MachineData) (saved : Saved) : Prop where
  original : SavedAt s.dmem s.regs.rsp.toBitVec saved
  stack : u.regs.rsp = s.regs.rsp
  current : SavedAt u.dmem s.regs.rsp.toBitVec saved
  output_bound : s.regs.rdi.toNat + 80 ≤ 2^64
  output_mapped : Large.Mapped u.dmem s.regs.rdi.toBitVec 80
  stack_low : 72 ≤ s.regs.rsp.toNat
  stack_bound : s.regs.rsp.toNat + 368 ≤ 2^64
  output_work : Body.Apart s.regs.rdi.toNat 80 (workStart s) workSize
  output_saved : Body.Apart s.regs.rdi.toNat 80 (s.regs.rsp.toNat + 312) 56
  output_cache : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 8#64) 8 =
    some (s.regs.rdi.toNat : Int)

def arithmeticAddImage (reason : NatArithmetic.Failure) (padding : BitVec 32) : AddErrorImage :=
  { w0 := 1#64, w1 := 0#64, w2 := 0#64, w3 := 0#64,
    w4 := 0#64, w5 := 0#64, w6 := 0#64, w7 := 0#64,
    reason := (arithmeticErrorImage reason padding).reason, padding := padding }

def scopeErrorImage (expected : NatOperand) (actual statusPadding : BitVec 64) : ExactErrorImage :=
  { w0 := 1#64, w1 := 0#64, w2 := expected.pointer, w3 := expected.payload,
    w4 := 0#64, w5 := actual, w6 := 0#64, w7 := 0#64, w8 := statusPadding }

theorem errors_observe (m : DataMem) (out : BitVec 64) (off count : Nat) :
    widthLoad m (out.toNat + off) count = observe m out off count := by
  simp only [widthLoad, observe, width_address]

theorem errors_observe_zero (m : DataMem) (out : BitVec 64) (count : Nat) :
    widthLoad m out.toNat count = observe m out 0 count := by
  simp only [widthLoad, observe, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero]

theorem add_arithmetic_observed (m : DataMem) (out : BitVec 64)
    (reason : NatArithmetic.Failure) (padding : BitVec 32)
    (bound : out.toNat + 80 ≤ 2^64) :
    SszNative.BitVector.failureAt
      (widthLoad (addErrorOutputMem m out (arithmeticAddImage reason padding))) out.toNat reason := by
  have fields := add_error_observed m out (arithmeticAddImage reason padding) bound
  rcases fields with ⟨tag, text, textSize, p0, n0, p1, n1, p2, n2, status, _⟩
  refine ⟨?_, ?_, ?_, Or.inl ⟨⟨?_, ?_⟩, by decide⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  · simpa only [errors_observe_zero] using tag
  · simpa only [errors_observe, arithmeticAddImage, show (1#64).toNat = 1 by decide] using text
  · simpa only [errors_observe, arithmeticAddImage, show (0#64).toNat = 0 by decide] using textSize
  · simpa only [errors_observe, arithmeticAddImage, show (0#64).toNat = 0 by decide] using p0
  · simpa only [Nat.add_assoc, Nat.reduceAdd, errors_observe, arithmeticAddImage,
      show (0#64).toNat = 0 by decide] using n0
  · simpa only [errors_observe, arithmeticAddImage, show (0#64).toNat = 0 by decide] using p1
  · simpa only [Nat.add_assoc, Nat.reduceAdd, errors_observe, arithmeticAddImage,
      show (0#64).toNat = 0 by decide] using n1
  · simpa only [errors_observe, arithmeticAddImage, show (0#64).toNat = 0 by decide] using p2
  · simpa only [Nat.add_assoc, Nat.reduceAdd, errors_observe, arithmeticAddImage,
      show (0#64).toNat = 0 by decide] using n2
  · cases reason <;>
      simpa only [errors_observe, arithmeticAddImage, arithmeticErrorImage,
        show (32768#32).toNat = 32768 by decide,
        show (32770#32).toNat = 32770 by decide] using status

theorem scope_error_observed (m : DataMem) (out : BitVec 64)
    (expected : NatOperand) (actual statusPadding : BitVec 64)
    (bound : out.toNat + 80 ≤ 2^64) (statusLow : statusPadding.setWidth 32 = 3#32)
    (operand : expected.At (widthLoad (exactErrorMem m out
      (scopeErrorImage expected actual statusPadding)))) :
    SszNative.BitVector.ResultAt
      (widthLoad (exactErrorMem m out (scopeErrorImage expected actual statusPadding)))
      out.toNat 0 #[] (.error (.scope expected actual.toNat)) := by
  have fields := exact_error_observed m out (scopeErrorImage expected actual statusPadding) bound
  rcases fields with ⟨tag, text, textSize, pointer, payload, p1, n1, p2, n2, _⟩
  have status := (exact_error_reason_padding m out
    (scopeErrorImage expected actual statusPadding) bound).1
  have pair : NatArithmetic.operandAt
      (widthLoad (exactErrorMem m out (scopeErrorImage expected actual statusPadding)))
      (out.toNat + 24) expected := by
    refine ⟨?_, ?_, operand⟩
    · simpa only [errors_observe, scopeErrorImage] using pointer
    · simpa only [Nat.add_assoc, Nat.reduceAdd, errors_observe, scopeErrorImage] using payload
  refine ⟨⟨?_, ?_, ?_, ?_, Or.inl ⟨⟨?_, ?_⟩, actual.isLt⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩, pair⟩
  · simpa only [errors_observe_zero] using tag
  · simpa only [errors_observe, scopeErrorImage, show (1#64).toNat = 1 by decide] using text
  · simpa only [errors_observe, scopeErrorImage, show (0#64).toNat = 0 by decide] using textSize
  · exact NatMemory.Pair.at _ expected.pointer expected.payload expected.value _
      (NatArithmetic.operandAt.pair _ _ expected pair) pair.1 pair.2.1
  · simpa only [errors_observe, scopeErrorImage, show (0#64).toNat = 0 by decide] using p1
  · simpa only [Nat.add_assoc, Nat.reduceAdd, errors_observe, scopeErrorImage] using n1
  · simpa only [errors_observe, scopeErrorImage, show (0#64).toNat = 0 by decide] using p2
  · simpa only [Nat.add_assoc, Nat.reduceAdd, errors_observe, scopeErrorImage,
      show (0#64).toNat = 0 by decide] using n2
  · simpa only [errors_observe, scopeErrorImage, statusLow,
      show (3#32).toNat = 3 by decide] using status

theorem errors_division_frame (s u : MachineData) (image : ErrorImage)
    (bound : s.regs.rdi.toNat + 80 ≤ 2^64) :
    RegionsFrame u.dmem (divisionErrorState u s.regs.rdi.toBitVec image).dmem (finishRegions s) := by
  intro a outside
  apply division_error_frame
  intro i hi
  exact Body.outside_byte s.regs.rdi.toBitVec a 80 i bound
    (outside (s.regs.rdi.toNat, 80) (by simp [finishRegions])) hi

theorem errors_add_frame (s u : MachineData) (saved : Saved) (h : ErrorSuffixAt s u saved)
    (image : AddErrorImage) :
    RegionsFrame u.dmem (addErrorState u s.regs.rdi.toBitVec image).dmem (finishRegions s) := by
  have bound := h.stack_bound
  have low := h.stack_low
  have stackNat := UInt64.toNat_toBitVec s.regs.rsp
  have frame := add_error_regions_frame u s.regs.rdi.toBitVec image h.output_bound (by
    rw [h.stack]
    bv_omega)
  apply frame.cover
  intro span member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨(s.regs.rdi.toNat, 80), by simp [finishRegions], Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨(workStart s, workSize), by simp [finishRegions], ?_, ?_⟩ <;>
      simp only [h.stack, workStart, workSize] <;> bv_omega

theorem errors_exact_frame (s u : MachineData) (saved : Saved) (h : ErrorSuffixAt s u saved)
    (image : ExactErrorImage) :
    RegionsFrame u.dmem (exactErrorState u s.regs.rdi.toBitVec image).dmem (finishRegions s) := by
  have bound := h.stack_bound
  have low := h.stack_low
  have stackNat := UInt64.toNat_toBitVec s.regs.rsp
  have frame := exact_error_regions_frame u s.regs.rdi.toBitVec image h.output_bound (by
    rw [h.stack]
    bv_omega)
  apply frame.cover
  intro span member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨(s.regs.rdi.toNat, 80), by simp [finishRegions], Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨(workStart s, workSize), by simp [finishRegions], ?_, ?_⟩ <;>
      simp only [h.stack, workStart, workSize] <;> bv_omega

end SszX86.BitVector
