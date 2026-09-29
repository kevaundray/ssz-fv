import SszArm.NatMulWordHighRestore
import SszArm.NatMulWordHighRegisters
import SszArm.NatMulWordHighSpilled

namespace SszArm.NatMulWord

open Delimited (MemoryFrame)

theorem high_completed_memory (site : HighSite) (s : ArmState) (base : BitVec 64) :
    (highCompleted site s base).mem = (site.spilled s).mem := by
  rw [highCompleted, high_restore_memory, high_core_mem, high_save_effect] <;>
    simp only [ArmState.mem_w_eq_mem]

theorem high_completed_stack (site : HighSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (highCompleted site s base) = r (.GPR 31#5) s := by
  rw [highCompleted, high_restore_stack, high_core_sp, high_save_effect] <;>
    simp only [r_of_w_same, BitVec.sub_add_cancel]


theorem high_completed_saved (site : HighSite) (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) (reg : BitVec 5) (member : reg ∈ site.saved) :
    r (.GPR reg) (highCompleted site s base) = r (.GPR reg) s := by
  let b := block base site.coreOps (block base site.saveOps s)
  have sp : r (.GPR 31#5) b = r (.GPR 31#5) s - 48#64 := by
    rw [show b = block base site.coreOps (block base site.saveOps s) from rfl,
      high_core_sp, high_save_effect, r_of_w_same]
  have memory : b.mem = (site.spilled s).mem := by
    rw [show b = block base site.coreOps (block base site.saveOps s) from rfl,
      high_core_mem, high_save_effect] <;>
      simp only [ArmState.mem_w_eq_mem]
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp memory
  rcases List.getElem_of_mem member with ⟨index, bound, selected⟩
  have length : site.saved.length = 6 := by cases site <;> rfl
  let slot : Fin 6 := ⟨index, by omega⟩
  have slotReg : site.saved[slot.val]! = reg := by
    change site.saved[index]! = reg
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem bound]
    exact selected
  have restored := high_restore_read site b base slot
  rw [sp, reads] at restored
  change r (.GPR reg) (block base site.restoreOps b) = r (.GPR reg) s
  exact (congrArg (fun query : BitVec 5 =>
    r (.GPR query) (block base site.restoreOps b) = r (.GPR query) s) slotReg).mp
      (restored.trans (high_spilled_read site s slot stack))

theorem high_completed_registers (site : HighSite) (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) (reg : BitVec 5)
    (different : reg ≠ site.destination) :
    r (.GPR reg) (highCompleted site s base) = r (.GPR reg) s := by
  by_cases saved : reg ∈ site.saved
  · exact high_completed_saved site s base stack reg saved
  by_cases sp : reg = 31#5
  · subst reg
    exact high_completed_stack site s base
  rw [highCompleted, high_restore_registers site _ base reg saved sp,
    high_core_registers site _ base reg saved different,
    high_save_registers site s base reg sp]

theorem high_completed_frame (site : HighSite) (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 48, 48)] s (highCompleted site s base) := by
  intro address outside
  rw [high_completed_memory]
  exact NatMulSpill.six_frame s _ _ _ _ _ _ _ stack address outside

end SszArm.NatMulWord
