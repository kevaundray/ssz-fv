import SszX86.NatMulWordLargeRunState
import SszX86.NatMulWordLargeMemoryInitializedState

namespace SszX86.NatMulWord
open SszNative

theorem large_loop_many (s current : MachineData) (operand : NatOperand)
    (factor address used : BitVec 64) (ready : MultiplyReady s current operand factor)
    (large : 1 < operand.wordCount) (physical : operand.words.length+1 < 2^64)
    (guardFlags mulFlags : StatusFlags) :
    (LargeMemory.state current operand address used guardFlags mulFlags).regs.r11.toBitVec+1#64 ≠
      (LargeMemory.state current operand address used guardFlags mulFlags).regs.r9.toBitVec := by
  change current.regs.r11.toBitVec+1#64 ≠ current.regs.r9.toBitVec
  rw [ready.skipped, ready.payload]
  have bound := Limbs.sigWords_le_length operand.words
  change operand.wordCount ≤ operand.words.length at bound
  bv_omega

theorem large_loop_registers (s current : MachineData) (operand : NatOperand)
    (factor address capacity used : BitVec 64) (ready : MultiplyReady s current operand factor)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat (operand.wordCount+1) = some r)
    (guardFlags mulFlags loopFlags : StatusFlags) :
    LargeLoopRegisters s
      (loopStartState (LargeMemory.state current operand address used guardFlags mulFlags) loopFlags)
      operand factor address r := by
  obtain ⟨checks, geometry⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega) r).mp reserved
  have countBound : operand.wordCount < 2^61 := by have := checks.1; omega
  have count64 : operand.wordCount < 2^64 := by omega
  have countNat : (BitVec.ofNat 64 operand.wordCount).toNat = operand.wordCount := Nat.mod_eq_of_lt count64
  have paired := paired_count (BitVec.ofNat 64 operand.wordCount) (by rw [countNat]; exact countBound)
  refine ⟨ready.sp, ready.output, ready.simd, ready.input, ready.payload,
    ready.factorReg, ready.count, ready.counter, ?_, ?_, rfl, ?_, rfl⟩
  · change 2305843009213693950#64 &&& current.regs.r15.toBitVec = _
    rw [ready.count, BitVec.and_comm, paired, countNat, Nat.mul_comm]
  · change BitVec.ofNat 64 (address.toNat+Arena.start address.toNat used.toNat)+8#64 = _
    rw [geometry]
  · change productHigh current.regs.rcx.toBitVec (SszNative.NatMul.lowWord operand) = _
    rw [ready.factorReg]
    exact (initial_step factor (SszNative.NatMul.lowWord operand)).2

end SszX86.NatMulWord
