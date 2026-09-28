import SszArm.NatMulWordZero
import SszArm.NatMulWordIdentityReturn
import SszArm.NatMulWordSmallRun
import SszArm.NatMulWordLarge

namespace SszArm.NatMulWord

/-- Original entry through the original RET for arbitrary physically owned
operands. All four branches preserve the exact checked allocation outcome. -/
theorem program_correct (s : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) (factor : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : Owned s operand factor)
    (pc : read_pc s = base + BitVec.ofNat 64 entry) :
    ∃ fuel t, run fuel s = t ∧ Post s t operand factor := by
  by_cases zero : factor = 0#64
  · subst factor
    obtain ⟨t, execution, post⟩ := zero_correct s base operand owned code error aligned pc
    exact ⟨25, t, execution, post⟩
  by_cases one : factor = 1#64
  · subst factor
    exact identity_run s base operand code error aligned
      (by simpa only [entry, BitVec.ofNat_zero, BitVec.add_zero] using pc) owned
  by_cases small : operand.wordCount ≤ 1
  · exact small_run s base operand factor code error aligned owned pc zero one small
  · exact large_run s base operand factor code error aligned owned pc zero one (by omega)

end SszArm.NatMulWord
