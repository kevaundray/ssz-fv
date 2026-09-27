import SszX86.NatDivisionNormalizePreserve

namespace SszX86.NatDivision
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The large path's observed ABI is the exact native phase result; the full
written quotient list remains an independent resource even after normalization. -/
theorem normalized_result_phase (s : MachineData) (operand : NatOperand)
    (divisor : BitVec 64) (address capacity used : Nat)
    (nonzero : divisor ≠ 0) (notone : divisor ≠ 1) (large : 2 < operand.wordCount)
    (reservation : Arena.Reservation)
    (reserved : Arena.reserve address capacity used operand.wordCount = some reservation)
    (pointer : s.regs.r14.toBitVec = BitVec.ofNat 64 reservation.pointer)
    (remainder : s.regs.r15.toBitVec = BitVec.ofNat 64
      (LimbDivision.divideWords divisor (Limbs.trim operand.words)).2)
    (outputBound : s.regs.rbx.toNat + 68 ≤ 2^64)
    (apart : Body.Apart s.regs.r14.toNat
      (8*(LimbDivision.divideWords divisor (Limbs.trim operand.words)).1.length) s.regs.rbx.toNat 68)
    (stored : (NatOperand.large s.regs.r14.toBitVec
      (LimbDivision.divideWords divisor (Limbs.trim operand.words)).1).At (widthLoad s.dmem))
    (flags : StatusFlags) :
    NatArithmetic.DivisionResultAt
      (widthLoad (normalizedResultState s
        (LimbDivision.divideWords divisor (Limbs.trim operand.words)).1 flags).dmem)
      s.regs.rbx.toNat (SszNative.NatDivision.run operand divisor address capacity used).result := by
  have observed := (normalized_result_memory s
    (LimbDivision.divideWords divisor (Limbs.trim operand.words)).1 flags outputBound apart stored).2
  rw [SszNative.NatDivision.phase_reserved operand divisor address capacity used
    nonzero notone large reservation reserved]
  simpa only [pointer, remainder] using observed

/-- The failed large reservation observes scratch exhaustion, never BadRep. -/
theorem result_error_phase (m : DataMem) (out : BitVec 64) (operand : NatOperand)
    (divisor : BitVec 64) (address capacity used : Nat)
    (nonzero : divisor ≠ 0) (notone : divisor ≠ 1) (large : 2 < operand.wordCount)
    (failed : Arena.reserve address capacity used operand.wordCount = none) :
    NatArithmetic.DivisionResultAt (widthLoad (resultErrorMem m out)) out.toNat
      (SszNative.NatDivision.run operand divisor address capacity used).result := by
  rw [SszNative.NatDivision.phase_reserve_failure operand divisor address capacity used
    nonzero notone large failed]
  exact result_error_observed m out

end SszX86.NatDivision
