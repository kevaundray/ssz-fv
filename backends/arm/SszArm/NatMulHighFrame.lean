import SszArm.NatMulHighRun

namespace SszArm.NatMul

open Delimited (MemoryFrame)

theorem high_completed_memory (s : ArmState) (base : BitVec 64) :
    (highCompleted s base).mem = (highSpilled s).mem := by
  have restore : ∀ t, (block base highRestoreOps t).mem = t.mem := by
    intro t
    simp [highRestoreOps, block, Op.effect, put, next, state_simp_rules]
  rw [highCompleted, restore, high_core_mem, high_save_effect]
  simp only [ArmState.mem_w_eq_mem]

theorem high_completed_stack (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (highCompleted s base) = r (.GPR 31#5) s := by
  have restore : ∀ t, r (.GPR 31#5) (block base highRestoreOps t) = r (.GPR 31#5) t + 48#64 := by
    intro t
    simp [highRestoreOps, block, Op.effect, put, next, state_simp_rules]
  rw [highCompleted, restore, high_core_sp, high_save_effect]
  simp [state_simp_rules, BitVec.sub_add_cancel, highSpilled]

theorem high_completed_saved (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) (reg : BitVec 5) (member : reg ∈ highSaved) :
    r (.GPR reg) (highCompleted s base) = r (.GPR reg) s := by
  let a := block base highSaveOps s
  let b := block base highCoreOps a
  have sp : r (.GPR 31#5) b = r (.GPR 31#5) s - 48#64 := by
    rw [show b = block base highCoreOps a from rfl, high_core_sp,
      show a = block base highSaveOps s from rfl, high_save_effect]
    simp [state_simp_rules, highSpilled]
  have memory : b.mem = (highSpilled s).mem := by
    rw [show b = block base highCoreOps a from rfl, high_core_mem,
      show a = block base highSaveOps s from rfl, high_save_effect]
    simp only [ArmState.mem_w_eq_mem]
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp memory
  have saved : reg ∈ NatMulWord.HighSite.first.saved := member
  rcases List.getElem_of_mem saved with ⟨index, bound, selected⟩
  have length : NatMulWord.HighSite.first.saved.length = 6 := rfl
  let slot : Fin 6 := ⟨index, by omega⟩
  have slotReg : NatMulWord.HighSite.first.saved[slot.val]! = reg := by
    change NatMulWord.HighSite.first.saved[index]! = reg
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem bound]
    exact selected
  have restored := NatMulWord.high_restore_read .first b base slot
  rw [sp, reads] at restored
  change r (.GPR reg) (block base highRestoreOps b) = r (.GPR reg) s
  rw [high_restore_word]
  exact (congrArg (fun query : BitVec 5 =>
    r (.GPR query) (NatMulWord.block base NatMulWord.HighSite.first.restoreOps b) =
      r (.GPR query) s) slotReg).mp
    (restored.trans (NatMulWord.high_spilled_read .first s slot stack))

theorem high_completed_registers (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) (reg : BitVec 5) (different : reg ≠ 18#5) :
    r (.GPR reg) (highCompleted s base) = r (.GPR reg) s := by
  by_cases saved : reg ∈ highSaved
  · exact high_completed_saved s base stack reg saved
  by_cases sp : reg = 31#5
  · subst reg
    exact high_completed_stack s base
  have restore : ∀ t, r (.GPR reg) (block base highRestoreOps t) = r (.GPR reg) t := by
    intro t
    simp_all (config := {decide := true}) [highRestoreOps, highSaved,
      block, Op.effect, put, next, state_simp_rules]
  rw [highCompleted, restore, high_core_registers _ base reg saved different, high_save_effect]
  simp (disch := simp_all) [state_simp_rules, highSpilled]

theorem high_completed_flags (s : ArmState) (base : BitVec 64) (flag : PFlag) :
    r (.FLAG flag) (highCompleted s base) = r (.FLAG flag) s := by
  have restore : ∀ t, r (.FLAG flag) (block base highRestoreOps t) = r (.FLAG flag) t := by
    intro t
    simp [highRestoreOps, block, Op.effect, put, next, state_simp_rules]
  rw [highCompleted, restore, high_core_flags, high_save_effect]
  simp [highSpilled, NatMulSpill.six, state_simp_rules]

theorem high_completed_vectors (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (highCompleted s base) = r (.SFP reg) s := by
  have preserved : ∀ ops t, r (.SFP reg) (block base ops t) = r (.SFP reg) t := by
    intro ops t
    exact NatMulStateFold.preserves (fun t op => op.effect base t) (r (.SFP reg))
      ops t (fun op _ u => op.sfp base u reg)
  simp only [highCompleted, preserved]

theorem high_completed_program (s : ArmState) (base : BitVec 64) :
    (highCompleted s base).program = s.program := by
  simp only [highCompleted, block_program]

theorem high_completed_error (s : ArmState) (base : BitVec 64) :
    read_err (highCompleted s base) = read_err s := by
  simp only [highCompleted, block_error]

theorem high_completed_frame (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 48, 48)] s (highCompleted s base) := by
  intro address outside
  rw [high_completed_memory]
  exact NatMulSpill.six_frame s _ _ _ _ _ _ _ stack address outside

theorem high_completed_spill_reads (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 48#64) (highCompleted s base) = r (.GPR 9#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 40#64) (highCompleted s base) = r (.GPR 10#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 32#64) (highCompleted s base) = r (.GPR 11#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 24#64) (highCompleted s base) = r (.GPR 12#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (highCompleted s base) = r (.GPR 13#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s - 8#64) (highCompleted s base) = r (.GPR 15#5) s := by
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp (high_completed_memory s base)
  simp only [reads]
  exact NatMulSpill.six_reads s _ _ _ _ _ _ _ stack

end SszArm.NatMul
