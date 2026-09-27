import SszArm.NatDivisionSmall
import SszArm.NatDivisionLargeFast
import SszArm.NatDivisionLargeFailure
import SszArm.NatDivisionLargeSuccess

namespace SszArm.NatDivision

/-- The complete frozen native Nat.div_rem_small helper executes from entry
through the actual RET and implements the shared unbounded Nat source model.

Only structural linked code, the physical ownership/ABI entry conditions, and
the caller-derived divisor lower bound in Owned are assumed. Original physical
Large lists may be empty or padded. Capacity is unsigned and unrestricted;
old used need not fit capacity. Every allocation and failure path is included. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (operand : SszNative.NatOperand)
    (owned : Owned s operand) (code : JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel, Post s (run fuel s) operand := by
  cases operand with
  | small word => exact small_correct s base word owned code error aligned pc
  | large pointer words =>
    by_cases fast : (SszNative.NatOperand.large pointer words).wordCount ≤ 2
    · exact large_fast_correct s base pointer words owned code error aligned pc fast
    · have count : 2 < SszNative.Limbs.sigWords words := by
        change ¬ SszNative.Limbs.sigWords words ≤ 2 at fast
        omega
      cases reserved : SszNative.Arena.reserve (arenaOf s).base (arenaOf s).capacity
          (arenaOf s).used (SszNative.Limbs.sigWords words) with
      | none => exact large_failure_correct s base pointer words owned code error aligned pc count reserved
      | some reservation =>
        exact large_success_correct s base pointer words reservation owned code error aligned pc count reserved

/-- A successful returned native result is mathematical quotient and remainder,
with the exact source-model memory/resources/ABI postcondition retained. -/
theorem program_correct_success (s : ArmState) (base : BitVec 64)
    (operand quotient : SszNative.NatOperand) (remainder : BitVec 64)
    (owned : Owned s operand) (code : JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base)
    (success : (outcome s operand).result = .ok (quotient, remainder)) :
    ∃ fuel, Post s (run fuel s) operand ∧
      quotient.value = operand.value / (r (.GPR 3#5) s).toNat ∧
      remainder.toNat = operand.value % (r (.GPR 3#5) s).toNat ∧
      remainder.toNat < (r (.GPR 3#5) s).toNat := by
  obtain ⟨fuel, post⟩ := program_correct s base operand owned code error aligned pc
  exact ⟨fuel, post, (post.arithmetic success).2.2.2⟩

end SszArm.NatDivision
