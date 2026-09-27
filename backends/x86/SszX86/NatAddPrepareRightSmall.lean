import SszX86.NatAddPrepared
import SszX86.NatAddSmallRight
import SszX86.NatAddNormalizeLeftPhase

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The right-Small path after the left scan distinguishes zero-left borrowing,
zero-right normalization, and two nonzero counted operands. -/
theorem prepare_right_small_scanned (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left : NatOperand) (limb : BitVec 64)
    (leftPointer : s.regs.rsi.toBitVec = left.pointer)
    (leftPayload : s.regs.rdx.toBitVec = left.payload)
    (rightPayload : s.regs.r8.toBitVec = limb)
    (leftCount : s.regs.rax.toBitVec = BitVec.ofNat 64 left.wordCount)
    (counter : s.regs.r10.toBitVec = BitVec.ofNat 64 (left.wordCount+1))
    (leftAt : left.At (widthLoad s.dmem)) :
    Eventually (step e) (Prepared s left (.small limb) base) (s, base + 96) := by
  have bound := operand_count_bound s.dmem left leftAt
  have normalized := normalized_small limb
  apply small_right_dispatch e base hc s
  intro flags
  by_cases rightZero : limb = 0#64
  · have rightRegZero : s.regs.r8.toBitVec = 0#64 := rightPayload.trans rightZero
    rw [ite_eq_left rightRegZero]
    apply small_right_zero e base hc
    intro flags
    by_cases leftZero : left.wordCount = 0
    · have one : s.regs.r10.toBitVec = 1#64 := by rw [counter, leftZero]
      rw [ite_eq_left one]
      apply Eventually.done
      apply Prepared.zero_left (s := s) leftZero ⟨rfl, rfl, rfl, rfl, rfl⟩
      · simp only [normalized, NatOperand.pointer, UInt64.toBitVec_ofNat]
      · rw [normalized]
        simp only [NatOperand.payload, UInt64.toBitVec_ofNat, rightZero]
      · rfl
    · have notOne : s.regs.r10.toBitVec ≠ 1#64 := by rw [counter]; bv_omega
      rw [ite_eq_right notOne]
      let input : MachineData := {s with
        regs := {s.regs with rcx := 0, r8 := 0}
        status := flags}
      apply normalize_left_cps e base hc input left leftPointer leftPayload leftAt
      intro t frame ptr pay
      apply Eventually.done
      apply Prepared.zero_right leftZero
      · simp only [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, rightZero, ↓reduceIte]
      · exact ⟨frame.memory, frame.stack, frame.output, frame.arena, frame.simd⟩
      · exact ptr
      · exact pay
      · rfl
  · have rightRegNonzero : s.regs.r8.toBitVec ≠ 0#64 := by simpa only [rightPayload] using rightZero
    rw [ite_eq_right rightRegNonzero]
    apply small_right_nonzero e base hc
    intro flags
    by_cases leftZero : left.wordCount = 0
    · have one : s.regs.r10.toBitVec = 1#64 := by rw [counter, leftZero]
      rw [ite_eq_left one]
      apply Eventually.done
      apply Prepared.zero_left (s := s) leftZero ⟨rfl, rfl, rfl, rfl, rfl⟩
      · simp only [normalized, NatOperand.pointer, UInt64.toBitVec_ofNat]
      · simpa only [normalized, NatOperand.payload] using rightPayload
      · rfl
    · have notOne : s.regs.r10.toBitVec ≠ 1#64 := by rw [counter]; bv_omega
      rw [ite_eq_right notOne]
      apply small_right_count e base hc
      intro flags
      apply Eventually.done
      apply Prepared.counted leftZero
      · simp only [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, rightZero, ↓reduceIte]
        decide
      · refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, leftPointer, leftPayload, ?_, rightPayload,
          leftCount, ?_, ?_⟩
        · rfl
        · simp only [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, rightZero, ↓reduceIte]
          decide
        · change ((0#64).setWidth 8 = 0#8) ↔ (0#64 = 0#64)
          decide
      · rfl

end SszX86.NatAdd
