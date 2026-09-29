import SszX86.NatMulWordLargeReserveCps
import SszX86.NatMulWordLargeStartCps
import SszX86.NatMulWordLargeRun

namespace SszX86.NatMulWord
open SszNative UintCodec

/-- Original allocating mul_word branch: checked reservation, cursor commit,
first MUL and spills, arbitrary paired iterations, optional carry tail,
normalization, publication, and the original epilogue/RET. -/
theorem large_multiply_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (large : 1 < operand.wordCount)
    (ready : MultiplyReady s t operand factor) :
    Eventually (step e) (Post s operand factor address capacity used ra) (t, base+195) := by
  apply large_reserve_cps e base hc s t operand factor address capacity used ra owned nonzero notone large ready
  intro r guardFlags reserved model
  apply large_start_cps e base hc s t operand factor address capacity used ra owned ready large r reserved model guardFlags
  intro mulFlags loopFlags loopState initialized registers
  refine large_run_cps e base hc s loopState operand factor address capacity used ra owned r model large
    initialized.work ?_ ?_ initialized.destination_mapped
    (LargeMemory.prefixMem s operand factor address used r) initialized.memory registers ?_ ?_ ?_
  · simpa only [model, NatArithmetic.committed] using initialized.cursor
  · simpa only [OutputMapped, registers.output] using initialized.output_mapped
  · word_simpa [registers.sp, LargeMemory.low, firstResult] using initialized.low_load
  · have checks := ((Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega) r).mp reserved).1
    have startNat : (BitVec.ofNat 64 (Arena.start address.toNat used.toNat)).toNat = Arena.start address.toNat used.toNat :=
      Nat.mod_eq_of_lt checks.2.2.2.1
    simpa only [registers.sp, startNat] using initialized.start_load
  · have geometry := ((Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega) r).mp reserved).2
    rw [geometry]
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end SszX86.NatMulWord
