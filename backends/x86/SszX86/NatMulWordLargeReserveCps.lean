import SszX86.NatMulWordLargeFailure
import SszX86.NatMulWordPrepared
import SszX86.NatMulWordReserveLarge
import SszX86.NatAddSmallMath

namespace SszX86.NatMulWord
open SszNative

theorem large_reserve_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s current : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (large : 1 < operand.wordCount)
    (ready : MultiplyReady s current operand factor)
    (success : ∀ r guardFlags,
      Arena.reserve address.toNat capacity.toNat used.toNat (operand.wordCount+1) = some r →
      SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
        NatArithmetic.committed r (SszNative.NatMul.wordWritten operand factor) →
      Eventually (step e) (Post s operand factor address capacity used ra)
        (LargeReservation.reservedState current address used guardFlags, base+310)) :
    Eventually (step e) (Post s operand factor address capacity used ra) (current, base+195) := by
  have countBound := NatAdd.operand_count_bound s.dmem operand owned.operand_at
  have countNat : current.regs.r15.toNat = operand.wordCount := by
    change current.regs.r15.toBitVec.toNat = operand.wordCount
    rw [ready.count]
    exact Nat.mod_eq_of_lt (by omega)
  have sizeBound : operand.wordCount+1 < 2^64 := by omega
  have header := pushed_header s operand factor address capacity used ra owned
  have currentHeader : LargeReservation.Header current address capacity used := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [ready.memory, ready.arena] using header.1
    · simpa only [ready.memory, ready.arena] using header.2.1
    · simpa only [ready.memory, ready.arena] using header.2.2
  apply eventually_trans (step e) (LargeReservation.Post current base address capacity used)
    (Post s operand factor address capacity used ra) _ (LargeReservation.runs e base hc current address capacity used currentHeader)
  rintro ⟨t, pc⟩ ⟨frame, failed | ⟨r, reserved, pcEq, guardFlags, stateEq⟩⟩
  · obtain ⟨exhausted, pcEq, memory⟩ := failed
    rw [countNat] at exhausted
    have outcome : SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
        NatArithmetic.unchanged used.toNat (.error .scratchExhausted) := by
      rw [SszNative.NatMul.runWord_large operand factor _ _ _ nonzero notone large,
        if_pos sizeBound, exhausted]
    have output : t.regs.rdi = current.regs.rdi := by
      simpa only [Reg64s.get64] using frame.2 .rdi (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have stack : t.regs.rsp = current.regs.rsp := by
      simpa only [Reg64s.get64] using frame.2 .rsp (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    rw [pcEq]
    exact large_error_finish_cps e base hc s t operand factor address capacity used ra owned outcome
      (memory.trans ready.memory) (output.trans ready.output)
      ((congrArg UInt64.toBitVec stack).trans ready.sp) (frame.1.trans ready.simd)
  · rw [countNat] at reserved
    have outcome : SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
        NatArithmetic.committed r (SszNative.NatMul.wordWritten operand factor) := by
      rw [SszNative.NatMul.runWord_large operand factor _ _ _ nonzero notone large,
        if_pos sizeBound, reserved]
    rw [pcEq, stateEq]
    exact success r guardFlags reserved outcome

end SszX86.NatMulWord
