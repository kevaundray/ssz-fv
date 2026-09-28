import SszArm.NatMulWordHighRun

namespace SszArm.NatMulWord

open Delimited (MemoryFrame)

theorem high_completed_memory (site : HighSite) (s : ArmState) (base : BitVec 64) :
    (highCompleted site s base).mem = (site.spilled s).mem := by
  have restore : ∀ t, (block base site.restoreOps t).mem = t.mem := by
    intro t
    cases site <;> simp [HighSite.restoreOps, block, Op.effect, put, next, state_simp_rules]
  rw [highCompleted, restore, high_core_mem, high_save_effect]
  simp only [ArmState.mem_w_eq_mem]

theorem high_completed_stack (site : HighSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (highCompleted site s base) = r (.GPR 31#5) s := by
  have restore : ∀ t, r (.GPR 31#5) (block base site.restoreOps t) = r (.GPR 31#5) t + 48#64 := by
    intro t
    cases site <;> simp [HighSite.restoreOps, block, Op.effect, put, next, state_simp_rules]
  rw [highCompleted, restore, high_core_sp, high_save_effect]
  simp [state_simp_rules, BitVec.sub_add_cancel]

theorem high_core_registers (site : HighSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (notSaved : reg ∉ site.saved) (notDestination : reg ≠ site.destination) :
    r (.GPR reg) (block base site.coreOps s) = r (.GPR reg) s := by
  cases site <;>
    simp_all (config := {decide := true}) [HighSite.saved, HighSite.destination,
      HighSite.coreOps, block, Op.effect, put, next, state_simp_rules]

theorem high_completed_saved (site : HighSite) (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) (reg : BitVec 5) (member : reg ∈ site.saved) :
    r (.GPR reg) (highCompleted site s base) = r (.GPR reg) s := by
  let a := block base site.saveOps s
  let b := block base site.coreOps a
  have sp : r (.GPR 31#5) b = r (.GPR 31#5) s - 48#64 := by
    rw [show b = block base site.coreOps a from rfl, high_core_sp,
      show a = block base site.saveOps s from rfl, high_save_effect]
    simp [state_simp_rules]
  have memory : b.mem = (site.spilled s).mem := by
    rw [show b = block base site.coreOps a from rfl, high_core_mem,
      show a = block base site.saveOps s from rfl, high_save_effect]
    simp only [ArmState.mem_w_eq_mem]
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp memory
  have observed := NatMulSpill.six_reads s (r (.GPR 31#5) s)
    (r (.GPR site.saved[0]!) s) (r (.GPR site.saved[1]!) s)
    (r (.GPR site.saved[2]!) s) (r (.GPR site.saved[3]!) s)
    (r (.GPR site.saved[4]!) s) (r (.GPR site.saved[5]!) s) stack
  change r (.GPR reg) (block base site.restoreOps b) = _
  cases site <;>
    simp only [HighSite.saved, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [HighSite.saved, BitVec.sub_eq_add_neg] at observed
    simp (config := {decide := true}) [HighSite.restoreOps, HighSite.spilled, HighSite.saved,
      block, Op.effect, put, next, state_simp_rules, reads, sp, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, observed.1, observed.2.1, observed.2.2.1,
      observed.2.2.2.1, observed.2.2.2.2.1, observed.2.2.2.2.2]

theorem high_completed_registers (site : HighSite) (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) (reg : BitVec 5)
    (different : reg ≠ site.destination) :
    r (.GPR reg) (highCompleted site s base) = r (.GPR reg) s := by
  by_cases saved : reg ∈ site.saved
  · exact high_completed_saved site s base stack reg saved
  by_cases sp : reg = 31#5
  · subst reg
    exact high_completed_stack site s base
  have restore : ∀ t, r (.GPR reg) (block base site.restoreOps t) = r (.GPR reg) t := by
    intro t
    cases site <;> simp_all (config := {decide := true}) [HighSite.restoreOps, HighSite.saved,
      block, Op.effect, put, next, state_simp_rules]
  rw [highCompleted, restore, high_core_registers site _ base reg saved different, high_save_effect]
  simp (disch := simp_all) [state_simp_rules, NatMulSpill.six, HighSite.spilled]

theorem high_completed_frame (site : HighSite) (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 48, 48)] s (highCompleted site s base) := by
  intro address outside
  rw [high_completed_memory]
  exact NatMulSpill.six_frame s _ _ _ _ _ _ _ stack address outside

end SszArm.NatMulWord
