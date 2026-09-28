import SszX86.NatMulPrepared
import SszX86.NatAddSmallMath

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem prepare_right_small_scanned (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left : NatOperand) (limb : BitVec 64)
    (leftPointer : s.regs.rsi.toBitVec = left.pointer)
    (leftPayload : s.regs.rdx.toBitVec = left.payload)
    (rightPayload : s.regs.r8.toBitVec = limb)
    (leftMarker : s.regs.r10.toBitVec = BitVec.ofNat 64 (left.wordCount+1))
    (leftAt : left.At (widthLoad s.dmem)) :
    Eventually (step e) (Prepared s left (.small limb) base) (s, base + 100) := by
  have bound := NatAdd.operand_count_bound s.dmem left leftAt
  apply eventually_trans (step e) (SmallRightPost s base)
    (Prepared s left (.small limb) base) _ (scanned_small_runs e base hc s)
  rintro ⟨t, pc⟩ post
  have pcEq := post.pc
  dsimp only at pcEq
  rw [pcEq]
  by_cases zero : s.regs.r10.toBitVec = 1#64 ∨ s.regs.r8.toBitVec = 0#64
  · rw [ite_eq_left zero]
    apply Eventually.done
    apply Prepared.zero
    · rcases zero with hl | hr
      · apply Or.inl
        rw [leftMarker] at hl
        bv_omega
      · apply Or.inr
        have hz : limb = 0#64 := rightPayload.symm.trans hr
        simp [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, hz]
    · exact post.frame
    · rfl
  · rw [ite_eq_right zero]
    have leftNonzero : left.wordCount ≠ 0 := by
      intro hz
      apply zero
      apply Or.inl
      simpa only [hz] using leftMarker
    have rightNonzero : limb ≠ 0#64 := by
      intro hz
      exact zero (Or.inr (rightPayload.trans hz))
    have rightOne : (NatOperand.small limb).wordCount = 1 := by
      simp [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, rightNonzero]
    apply right_factor_cps e base hc
    apply Eventually.done
    apply Prepared.word_left leftNonzero rightOne
    · exact ⟨post.frame.memory, post.frame.stack, post.frame.output, post.frame.arena, post.frame.simd⟩
    · exact (congrArg UInt64.toBitVec post.pointer).trans leftPointer
    · exact (congrArg UInt64.toBitVec post.payload).trans leftPayload
    · change t.regs.r8.toBitVec = limb
      exact (congrArg UInt64.toBitVec post.factor).trans rightPayload
    · rfl

end SszX86.NatMul
