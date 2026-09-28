import SszArm.MeasureResultStages

namespace SszArm.Measure.Result

private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4232#64) :
    effect [p4232, p4236, p4240] s = spillStage .successStatus s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair, p4232, p4236, p4240,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc, stack, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4244#64) :
    effect [p4244, p4248, p4252, p4256] s = payloadStage .successStatus s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Lower.high, Payload.store, p4244, p4248, p4252, p4256,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4260#64) :
    effect [p4260, p4264, p4268] s = reloadStage .successStatus s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp, p4260, p4264, p4268,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]


theorem successStatus_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 4232#64) :
    run 10 s = Lower.successStatus.result s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have follows : Follows base Lower.successStatus.ops s := by
    simp (config := {decide := true, instances := true}) [effect, Follows, Lower.ops, Lower.start, Lower.finish, Lower.tmp, Lower.offset,
       Lower.kind, Lower.low, Lower.high, Lower.memory, Lower.result, Payload.store,
       savedPair, p4232, p4236, p4240, p4244, p4248, p4252, p4256, p4260, p4264, p4268, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, aligned, stack, lower, error, pc, BitVec.add_assoc,
       BitVec.sub_add_cancel, address, NatExact.store_w, NatExact.gpr_w_pc]
  rw [show 10 = Lower.successStatus.ops.length by rfl, runs _ s base code follows]
  change effect [p4260, p4264, p4268] (effect [p4244, p4248, p4252, p4256] (effect [p4232, p4236, p4240] s)) = _
  rw [spill_summary s base aligned pc]
  rw [payload_summary (spillStage .successStatus s base) base
    (spillStage_aligned .successStatus s base aligned) (spillStage_pc .successStatus s base)]
  rw [reload_summary (payloadStage .successStatus (spillStage .successStatus s base) base) base
    (payloadStage_aligned .successStatus _ base (spillStage_aligned .successStatus s base aligned))
    (payloadStage_pc .successStatus _ base)]
  exact stages_assemble .successStatus s base

end SszArm.Measure.Result
