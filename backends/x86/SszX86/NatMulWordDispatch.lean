import SszX86.NatMulWordCountPhase
import SszX86.NatMulWordSmallProofs

namespace SszX86.NatMulWord
open SszNative

/-- Original entry through all fast/scalar returns or the physical allocating
cut. The continuation is used only for genuinely multiword multiplication. -/
theorem mul_word_dispatch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (multiply : factor ≠ 0 → factor ≠ 1 → ∀ t, 1 < operand.wordCount →
      MultiplyReady s t operand factor →
      Eventually (step e) (Post s operand factor address capacity used ra) (t, base+195)) :
    Eventually (step e) (Post s operand factor address capacity used ra) (s, base) := by
  cases operand with
  | small limb =>
    exact mul_word_inline_correct e base hc s limb factor address capacity used ra owned
  | large p words =>
    by_cases zero : factor = 0
    · subst factor
      exact mul_word_zero_correct e base hc s (.large p words) address capacity used ra owned
    by_cases one : factor = 1
    · subst factor
      exact mul_word_one_correct e base hc s (.large p words) address capacity used ra owned
    apply entry_multiply_cps e base hc s
      (by simpa only [owned.factor, show (0 : BitVec 64) = 0#64 by decide] using zero)
      (by simpa only [owned.factor, show (1 : BitVec 64) = 1#64 by decide] using one)
    intro entryFlags
    apply pushes_cps e base hc (entryState s entryFlags) owned.stack_mapped
    intro stackFlags
    apply select_operand_cps e base hc
    · intro inline selectorFlags
      have positive := owned.operand_at.1
      change s.regs.rsi.toBitVec = 0#64 at inline
      rw [owned.operand_pointer] at inline
      simp only [NatOperand.pointer] at inline
      rw [inline] at positive
      simp only [BitVec.toNat_zero] at positive
      omega
    · intro large selectorFlags
      apply large_count_cps e base hc s _ p words factor address capacity used ra owned zero one
      · exact ⟨rfl, UInt64.toBitVec_ofBitVec _, rfl, rfl, rfl⟩
      · exact owned.operand_pointer
      · exact owned.operand_payload
      · exact owned.factor
      · exact multiply zero one

end SszX86.NatMulWord
