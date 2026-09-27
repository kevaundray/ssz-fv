import SszX86.NatAddPrepared
import SszX86.NatAddSmallRight
import SszX86.NatAddNormalizeEntry

namespace SszX86.NatAdd
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The specialized nonzero-Small-left/Small-right path either borrows the
left Small on zero-right or executes the complete ADD/ADC including overflow. -/
theorem prepare_small_pair (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : BitVec 64)
    (leftPayload : s.regs.rdx.toBitVec = left)
    (rightPayload : s.regs.r8.toBitVec = right) (leftNonzero : left ≠ 0#64) :
    Eventually (step e) (Prepared s (.small left) (.small right) base) (s, base + 75) := by
  have leftCount : (NatOperand.small left).wordCount = 1 := by
    simp only [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, leftNonzero, ↓reduceIte]
  apply small_right_inline e base hc s
  intro flags
  by_cases rightZero : right = 0#64
  · have zero : s.regs.r8.toBitVec = 0#64 := rightPayload.trans rightZero
    rw [ite_eq_left zero]
    apply left_small_normalize e base hc
    intro flags
    apply Eventually.done
    apply Prepared.zero_right
    · rw [leftCount]
      decide
    · simp only [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, rightZero, ↓reduceIte]
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp only [normalized_small, NatOperand.pointer, UInt64.toBitVec_ofNat]
    · simpa only [normalized_small, NatOperand.payload] using leftPayload
    · rfl
  · have nonzero : s.regs.r8.toBitVec ≠ 0#64 := by simpa only [rightPayload] using rightZero
    have rightCount : (NatOperand.small right).wordCount = 1 := by
      simp only [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, rightZero, ↓reduceIte]
    rw [ite_eq_right nonzero]
    apply inline_sum_entry e base hc
    intro flags
    refine (sum_sites_cps e base hc _ (.small left) (.small right) rfl ?_ ?_ _ ?_).2.2.1
    · simpa only [sumStart, SszNative.NatAdd.lowWord, NatOperand.words,
        List.getElem?_cons_zero, Option.getD_some] using leftPayload
    · simpa only [sumStart, SszNative.NatAdd.lowWord, NatOperand.words,
        List.getElem?_cons_zero, Option.getD_some] using rightPayload
    · intro t ready
      apply Eventually.done
      apply Prepared.summed
      · rw [leftCount]
        decide
      · rw [rightCount]
        decide
      · rw [leftCount, rightCount]
        exact ⟨by decide, by decide⟩
      · exact ⟨⟨ready.frame.memory, ready.frame.stack, ready.frame.output,
          ready.frame.arena, ready.frame.simd⟩, ready.low, ready.high⟩
      · rfl

end SszX86.NatAdd
