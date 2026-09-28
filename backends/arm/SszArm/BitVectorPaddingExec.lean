import SszArm.BitVectorPaddingOps
import SszArm.NatExactFinish

namespace SszArm.BitVector.Padding

open Block BoolCodec

/-- Persistent spill bytes remain after the architectural stack is restored. -/
def saveResult (s : ArmState) : ArmState :=
  w .PC (read_pc s + 12#64)
    (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64)
      (NatExact.spillTwo s (r (.GPR 9#5) s) (r (.GPR 10#5) s)))

def Store.zeroImage (store : Store) (s : ArmState) : ArmState :=
  let address := r (.GPR 23#5) s + store.displacement
  let first := write_mem_bytes 8 address 0#64 s
  if store = .text then first else write_mem_bytes 8 (address + 8#64) 0#64 first

def Store.bodyResult (store : Store) (s : ArmState) : ArmState :=
  w .PC (read_pc s + BitVec.ofNat 64 (4 * store.bodyOps.length))
    (w (.GPR 10#5) 0#64
      (w (.GPR 9#5) (r (.GPR 23#5) s + store.displacement) (store.zeroImage s)))

def restoreResult (s : ArmState) : ArmState :=
  w .PC (read_pc s + 12#64)
    (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s)
        (w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s)))

private theorem save_follows (store : Store) (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 store.start) :
    Follows base store.saveOps s := by
  have stack := stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := aligned_sub16 _ stack
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  cases store <;>
    simp (config := {decide := true, instances := true})
      [Follows, Store.saveOps, Store.start, p6052, p6056, p6060,
       p6104, p6108, p6112, p6152, p6156, p6160, p6200, p6204, p6208,
       Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       aligned, stack, lower, error, pc, BitVec.add_assoc]

private theorem save_summary (store : Store) (s : ArmState)
    (aligned : CheckSPAlignment s) : effect store.saveOps s = saveResult s := by
  have same : effect store.saveOps s = effect Store.third.saveOps s := by
    cases store <;> rfl
  rw [same]
  have stack := stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := aligned_sub16 _ stack
  simp (config := {decide := true, instances := true})
    [effect, Store.saveOps, p6052, p6056, p6060, Op.effect, exec_inst,
     saveResult, NatExact.spillTwo, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, stack, lower, BitVec.add_assoc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc,
      write_base_gpr, store_write_over_write_shadow]

private theorem body_follows (store : Store) (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 store.bodyStart) :
    Follows base store.bodyOps s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  cases store <;>
    simp (config := {decide := true, instances := true})
      [Follows, Store.bodyOps, Store.bodyStart, Store.start,
       p6064, p6068, p6072, p6076, p6080, p6084,
       p6116, p6120, p6124, p6128, p6132, p6136,
       p6164, p6168, p6172, p6176, p6180, p6184,
       p6212, p6216, p6220, p6224, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, error, pc, BitVec.add_assoc]

private theorem zero_move : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide

private theorem third_body_summary (s : ArmState) :
    effect Store.third.bodyOps s = Store.third.bodyResult s := by
  simp (config := {decide := true, instances := true})
    [effect, Store.bodyOps, Store.bodyResult, Store.zeroImage, Store.displacement,
     p6064, p6068, p6072, p6076, p6080, p6084, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.add_assoc, zero_move] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc,
      write_base_gpr, store_write_over_write_shadow]

private theorem second_body_summary (s : ArmState) :
    effect Store.second.bodyOps s = Store.second.bodyResult s := by
  simp (config := {decide := true, instances := true})
    [effect, Store.bodyOps, Store.bodyResult, Store.zeroImage, Store.displacement,
     p6116, p6120, p6124, p6128, p6132, p6136, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.add_assoc, zero_move] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc,
      write_base_gpr, store_write_over_write_shadow]

private theorem first_body_summary (s : ArmState) :
    effect Store.first.bodyOps s = Store.first.bodyResult s := by
  simp (config := {decide := true, instances := true})
    [effect, Store.bodyOps, Store.bodyResult, Store.zeroImage, Store.displacement,
     p6164, p6168, p6172, p6176, p6180, p6184, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.add_assoc, zero_move] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc,
      write_base_gpr, store_write_over_write_shadow]

private theorem text_body_summary (s : ArmState) :
    effect Store.text.bodyOps s = Store.text.bodyResult s := by
  simp (config := {decide := true, instances := true})
    [effect, Store.bodyOps, Store.bodyResult, Store.zeroImage, Store.displacement,
     p6212, p6216, p6220, p6224, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.add_assoc, zero_move] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc,
      write_base_gpr, store_write_over_write_shadow]

private theorem body_summary (store : Store) (s : ArmState) :
    effect store.bodyOps s = store.bodyResult s := by
  cases store
  · exact third_body_summary s
  · exact second_body_summary s
  · exact first_body_summary s
  · exact text_body_summary s

private theorem restore_follows (store : Store) (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 store.restoreStart) :
    Follows base store.restoreOps s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  cases store <;>
    simp (config := {decide := true, instances := true})
      [Follows, Store.restoreOps, Store.restoreStart,
       p6088, p6092, p6096, p6140, p6144, p6148,
       p6188, p6192, p6196, p6228, p6232, p6236, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, aligned, error, pc, BitVec.add_assoc]

private theorem restore_summary (store : Store) (s : ArmState)
    (aligned : CheckSPAlignment s) : effect store.restoreOps s = restoreResult s := by
  have same : effect store.restoreOps s = effect Store.third.restoreOps s := by
    cases store <;> rfl
  rw [same]
  simp (config := {decide := true, instances := true})
    [effect, Store.restoreOps, p6088, p6092, p6096, Op.effect, exec_inst,
     restoreResult, state_simp_rules, bitvec_rules, minimal_theory, aligned, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr, store_write_over_write_shadow]

theorem save_run (store : Store) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 store.start) :
    run 3 s = saveResult s := by
  have count : store.saveOps.length = 3 := by cases store <;> rfl
  rw [← count, runs _ _ _ code (save_follows store s base error aligned pc)]
  exact save_summary store s aligned

theorem body_run (store : Store) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 store.bodyStart) :
    run store.bodyOps.length s = store.bodyResult s := by
  rw [runs _ _ _ code (body_follows store s base error pc)]
  exact body_summary store s

theorem restore_run (store : Store) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 store.restoreStart) :
    run 3 s = restoreResult s := by
  have count : store.restoreOps.length = 3 := by cases store <;> rfl
  rw [← count, runs _ _ _ code (restore_follows store s base error aligned pc)]
  exact restore_summary store s aligned

theorem reason_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 6100#64) :
    run 1 s = w .PC (base + 6104#64) (w (.GPR 8#5) 15#64 s) := by
  change stepi s = _
  rw [p6100.step s base code error pc]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [p6100, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc]

theorem branch_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 6240#64) : run 1 s = w .PC (base + 8224#64) s := by
  change stepi s = _
  rw [p6240.step s base code error pc]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [p6240, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc]

end SszArm.BitVector.Padding
