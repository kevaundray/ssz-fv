import SszX86.NatDivisionNormalizeResult
import SszX86.NatDivisionOutputPreserve

namespace SszX86.NatDivision
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Publication retains every written quotient word, and the normalized Nat
observation follows from the original buffer ownership, not a final-state premise. -/
theorem normalized_result_memory (s : MachineData) (words : List (BitVec 64))
    (flags : StatusFlags)
    (outputBound : s.regs.rbx.toNat + 68 ≤ 2^64)
    (apart : Body.Apart s.regs.r14.toNat (8*words.length) s.regs.rbx.toNat 68)
    (stored : (NatOperand.large s.regs.r14.toBitVec words).At (widthLoad s.dmem)) :
    NatMemory.wordsAt (widthLoad (normalizedResultState s words flags).dmem)
        s.regs.r14.toNat words ∧
      NatArithmetic.DivisionResultAt (widthLoad (normalizedResultState s words flags).dmem)
        s.regs.rbx.toNat
        (.ok (NatOperand.fromWords s.regs.r14.toBitVec words, s.regs.r15.toBitVec)) := by
  obtain ⟨positive, aligned, bound, limbs⟩ := stored
  have retained := result_success_preserves_words s.dmem s.regs.rbx.toBitVec
    (NatOperand.fromWords s.regs.r14.toBitVec words).pointer
    (NatOperand.fromWords s.regs.r14.toBitVec words).payload
    s.regs.r15.toBitVec s.regs.r14.toNat words outputBound bound apart limbs
  refine ⟨retained, normalized_result_observed s words flags ?_⟩
  exact ⟨positive, aligned, bound, retained⟩

/-- Original borrowed inputs survive normalization even when their high zeros
or physical length differ from the allocated quotient's significant prefix. -/
theorem normalized_result_operand (s : MachineData) (words : List (BitVec 64))
    (flags : StatusFlags) (operand : NatOperand)
    (outputBound : s.regs.rbx.toNat + 68 ≤ 2^64)
    (apart : ∀ pointer limbs, operand = .large pointer limbs →
      Body.Apart pointer.toNat (8*limbs.length) s.regs.rbx.toNat 68)
    (stored : operand.At (widthLoad s.dmem)) :
    operand.At (widthLoad (normalizedResultState s words flags).dmem) := by
  exact result_frame_operand s.dmem _ s.regs.rbx.toBitVec
    (result_success_mem_frame s.dmem s.regs.rbx.toBitVec
      (NatOperand.fromWords s.regs.r14.toBitVec words).pointer
      (NatOperand.fromWords s.regs.r14.toBitVec words).payload s.regs.r15.toBitVec)
    outputBound operand apart stored

end SszX86.NatDivision
