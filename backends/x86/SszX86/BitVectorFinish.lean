import SszX86.BitVectorFinishBorrow
import SszX86.BitVectorFinishTailMath
import SszX86.BitVectorTailShift

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- Complete actual successful-scope suffix, from the padding gate through RET.
The only branch information is the already executed exact helper's success.
The tail read, linked conversion, native guard, stores and epilogue are derived. -/
theorem finish_suffix_correct (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s u : MachineData) (saved : Saved) (length expected : NatOperand)
    (remainder address capacity used : BitVec 64) (data : Ssz.Bytes)
    (owned : Owned {s with dmem := u.dmem} saved length data address capacity used)
    (original : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (stack : u.regs.rsp = s.regs.rsp) (sizeReg : u.regs.r14 = s.regs.r14)
    (remainderReg : u.regs.r13.toBitVec = remainder)
    (pointer : u.regs.r15.toBitVec = length.pointer)
    (payload : u.regs.r12.toBitVec = length.payload)
    (outputCache : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 8#64) 8 =
      some (s.regs.rdi.toNat : Int))
    (sourceCache : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 104#64) 8 =
      some (s.regs.rdx.toNat : Int))
    (arithmetic : SszNative.BitVector.Expected length expected remainder)
    (checked : NatNarrow.runExact expected (BitVec.ofNat 64 data.size) = true) :
    Eventually (step e)
      (Terminal s saved u.dmem data (SszNative.BitVector.finish length expected remainder data))
      (u, base + 4832) := by
  have physical : data.size < 2^64 := by
    rw [owned.data_length]
    exact s.regs.r14.toBitVec.isLt
  have result := finish_result length expected remainder data physical arithmetic checked
  have remainderBound := SszNative.BitVector.expected_remainder_bound arithmetic
  have sizeZero : u.regs.r14.toBitVec = 0#64 ↔ data.size = 0 := by
    rw [sizeReg]
    constructor
    · intro zero
      have value := congrArg BitVec.toNat zero
      simpa only [owned.data_length, UInt64.toNat_toBitVec, BitVec.toNat_ofNat] using value
    · intro zero
      apply BitVec.eq_of_toNat_eq
      simpa only [owned.data_length, BitVec.toNat_ofNat, UInt64.toNat_toBitVec] using zero
  have gate : (u.regs.r13.toBitVec = 0#64 ∨ u.regs.r14.toBitVec = 0#64) ↔
      remainder = 0#64 ∨ data.size = 0 := by rw [remainderReg, sizeZero]
  rw [result]
  apply padding_gate_cps e base hc.body u
  intro gateFlags
  let g := paddingGateState u gateFlags
  by_cases bypass : remainder = 0#64 ∨ data.size = 0
  · have native := gate.mpr bypass
    simp only [native, bypass, ↓reduceIte]
    exact finish_borrow_cps e base hc s g saved length expected remainder address capacity used
      data owned original stack sizeReg pointer payload outputCache sourceCache arithmetic checked
  have native : ¬(u.regs.r13.toBitVec = 0#64 ∨ u.regs.r14.toBitVec = 0#64) := mt gate.mp bypass
  simp only [native, bypass, ↓reduceIte]
  have positive : 0 < data.size := by omega
  have remainderNonzero : remainder ≠ 0#64 := by
    intro equal
    exact bypass (Or.inl equal)
  let byte := data[data.size - 1]!.toBitVec
  apply tail_load_cps e base hc.body g s.regs.rdx.toBitVec byte
  · simpa only [g, paddingGateState, stack, UInt64.toNat_toBitVec] using sourceCache
  · exact finish_tail_read s g saved length data address capacity used owned sizeReg positive
  apply tail_mask_cps e base hc.body
    (tailLoadState g byte) (by simpa only [tailLoadState, g, paddingGateState, remainderReg]
      using remainderBound)
  intro maskFlags
  let m := tailMaskState (tailLoadState g byte) maskFlags
  apply tail_shift_cps e base hc.body m byte remainder
  · exact remainderReg
  · simp [m, tailMaskState, tailLoadState]
  · exact remainderNonzero
  · exact remainderBound
  intro shiftFlags
  let v := tailShiftState m byte remainder shiftFlags
  by_cases zero : data[data.size - 1]!.toBitVec >>> remainder.toNat = 0#8
  · simp only [byte, zero, ↓reduceIte]
    exact finish_borrow_cps e base hc s v saved length expected remainder address capacity used
      data owned original stack sizeReg pointer payload outputCache sourceCache arithmetic checked
  · simp only [byte, zero, ↓reduceIte]
    apply padding_pointer_cps e base hc.body v s.regs.rdi.toBitVec
    · simpa only [v, tailShiftState, m, tailMaskState, tailLoadState, g, paddingGateState,
        stack, UInt64.toNat_toBitVec] using outputCache
    exact finish_padding_cps e base hc.body s
      {v with regs := {v.regs with rax := UInt64.ofBitVec s.regs.rdi.toBitVec}}
      saved data original stack rfl owned.output_mapped owned.output_bound owned.stack_low
      owned.stack_bound owned.output_saved owned.saved_at

end SszX86.BitVector
