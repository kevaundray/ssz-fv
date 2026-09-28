import SszArm.MeasureResultStages

namespace SszArm.Measure.Result

private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4192#64) :
    effect [p4192, p4196, p4200] s = spillStage .successLeading s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair, p4192, p4196, p4200,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4204#64) :
    effect [p4204, p4208, p4212, p4216] s = payloadStage .successLeading s base := by
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Payload.store, zeroMove, p4204, p4208, p4212, p4216,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4220#64) :
    effect [p4220, p4224, p4228] s = reloadStage .successLeading s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp, p4220, p4224, p4228,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]


theorem successLeading_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 4192#64) :
    run 10 s = Lower.successLeading.result s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have follows : Follows base Lower.successLeading.ops s := by
    simp (config := {decide := true, instances := true}) [Follows, Lower.ops,
       p4192, p4196, p4200, p4204, p4208, p4212, p4216, p4220, p4224, p4228, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, lower, error, pc, BitVec.add_assoc,
       address, NatExact.store_w, NatExact.gpr_w_pc]
  rw [show 10 = Lower.successLeading.ops.length by rfl, runs _ s base code follows]
  change effect [p4220, p4224, p4228] (effect [p4204, p4208, p4212, p4216] (effect [p4192, p4196, p4200] s)) = _
  rw [spill_summary s base aligned pc]
  rw [payload_summary (spillStage .successLeading s base) base
    (spillStage_aligned .successLeading s base aligned) (spillStage_pc .successLeading s base)]
  rw [reload_summary (payloadStage .successLeading (spillStage .successLeading s base) base) base
    (payloadStage_aligned .successLeading _ base (spillStage_aligned .successLeading s base aligned))
    (payloadStage_pc .successLeading _ base)]
  exact stages_assemble .successLeading s base

end SszArm.Measure.Result
