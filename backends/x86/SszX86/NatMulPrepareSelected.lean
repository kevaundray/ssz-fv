import SszX86.NatMulPrepared
import SszX86.NatMulLowWordPhase

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem prepare_selected (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand)
    (leftPointer : s.regs.rsi.toBitVec = left.pointer)
    (leftPayload : s.regs.rax.toBitVec = left.payload)
    (rightPointer : s.regs.rcx.toBitVec = right.pointer)
    (rightPayload : s.regs.r8.toBitVec = right.payload)
    (leftCount : s.regs.r12.toBitVec = BitVec.ofNat 64 left.wordCount)
    (rightCount : s.regs.r13.toBitVec = BitVec.ofNat 64 right.wordCount)
    (rightCountdown : s.regs.r10.toBitVec = 1 - BitVec.ofNat 64 right.wordCount)
    (leftAt : left.At (widthLoad s.dmem))
    (leftNonzero : left.wordCount ≠ 0) (rightMany : 1 < right.wordCount) :
    Eventually (step e) (Prepared s left right base) (s, base + 243) := by
  have leftBound := NatAdd.operand_count_bound s.dmem left leftAt
  apply count_select_cps e base hc s
  · intro one flags
    have leftOne : left.wordCount = 1 := by
      rw [leftCount] at one
      bv_omega
    apply left_low_phase_cps e base hc {s with status := flags} left
      leftPointer leftPayload leftAt leftNonzero
    intro t loaded
    apply swapped_cps e base hc
    apply Eventually.done
    apply Prepared.word_right leftOne (by omega) (by omega)
    · exact ⟨loaded.frame.memory, loaded.frame.stack, loaded.frame.output,
        loaded.frame.arena, loaded.frame.simd⟩
    · simpa only [swappedState, loaded.pointer] using rightPointer
    · simpa only [swappedState, loaded.payload] using rightPayload
    · exact loaded.low
    · rfl
  · intro notone flags
    have leftMany : 1 < left.wordCount := by
      have ne : left.wordCount ≠ 1 := by
        intro eqOne
        apply notone
        simpa only [eqOne] using leftCount
      omega
    apply Eventually.done
    exact .counted leftMany rightMany
      ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, leftPointer, leftPayload, rightPointer,
        leftCount, rightCount, rightCountdown⟩ rfl

end SszX86.NatMul
