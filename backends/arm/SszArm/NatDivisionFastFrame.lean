import SszArm.NatDivisionFast
import SszArm.NatDivisionActivation

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem fast_finish_register (site : FastSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) :
    r (.GPR reg) (block base (site.finish s) s) = r (.GPR reg) s := by
  cases site <;> by_cases hz : r (.GPR 1#5) s = 0#64 <;>
    simp [FastSite.finish, block, Op.effect, state_simp_rules, hz]

theorem fast_finish_sfp (site : FastSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) :
    r (.SFP reg) (block base (site.finish s) s) = r (.SFP reg) s := by
  cases site <;> by_cases hz : r (.GPR 1#5) s = 0#64 <;>
    simp [FastSite.finish, block, Op.effect, state_simp_rules, hz]

/-- All saved-register observations survive the runtime call. The setup's X22
copy is intentional; its original value remains in the saved activation. -/
theorem fast_gpr (site : FastSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (lower : 9 ≤ reg.toNat) (notLow : reg ≠ 22#5) (notLR : reg ≠ 30#5) :
    r (.GPR reg) (fastResult site s base) = r (.GPR reg) s := by
  have keep : Udivti3.Preserved (.GPR reg) := by
    simp only [Udivti3.Preserved]
    bv_omega
  rw [fastResult, fast_finish_register]
  have call := call_frame site.call (fastPrepared site s base) base (.GPR reg) keep
  have calledKeep : r (.GPR reg) (fastDivided site s base) = r (.GPR reg) (fastPrepared site s base) := by
    simpa [fastDivided, called, state_simp_rules, notLR] using call
  rw [calledKeep]
  have others : reg ≠ 0#5 ∧ reg ≠ 1#5 ∧ reg ≠ 2#5 ∧ reg ≠ 3#5 := by bv_omega
  cases site <;> simp [fastPrepared, FastSite.setup, block, Op.effect, put, next,
    state_simp_rules, others.1, others.2.1, others.2.2.1, others.2.2.2, notLow]

@[simp] theorem fast_sp (site : FastSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (fastResult site s base) = r (.GPR 31#5) s :=
  fast_gpr site s base 31#5 (by decide) (by decide) (by decide)

@[simp] theorem fast_sfp (site : FastSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) : r (.SFP reg) (fastResult site s base) = r (.SFP reg) s := by
  rw [fastResult, fast_finish_sfp]
  change r (.SFP reg) (callResult site.call (fastPrepared site s base) base) = _
  rw [call_sfp]
  cases site <;> simp [fastPrepared, FastSite.setup, block, Op.effect, put, next, state_simp_rules]

theorem fast_saved (site : FastSite) (original s : ArmState) (base : BitVec 64)
    (saved : Saved original s) : Saved original (fastResult site s base) := by
  refine ⟨(fast_sp _ _ _).trans saved.sp, ?_, ?_, ?_⟩
  · intro reg offset member
    rw [fast_sp]
    have memory := Memory.mem_eq_iff_read_mem_bytes_eq.mp (fast_memory site s base)
    rw [memory]
    exact saved.words reg offset member
  · intro reg low high
    have notLow : reg ≠ 22#5 := by bv_omega
    have notLR : reg ≠ 30#5 := by bv_omega
    exact (fast_gpr site s base reg (by omega) notLow notLR).trans (saved.high reg low high)
  · intro reg low high
    rw [fast_sfp]
    exact saved.vectors reg low high

end SszArm.NatDivision
