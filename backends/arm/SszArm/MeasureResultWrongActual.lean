import SszArm.MeasureResultStages

namespace SszArm.Measure.Result

private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4016#64) :
    effect [p4016, p4020, p4024] s = spillStage .wrongActual s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair, p4016, p4020, p4024,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4028#64) :
    effect [p4028, p4032, p4036, p4040, p4044, p4048] s = payloadStage .wrongActual s base := by
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Lower.high, Payload.store, zeroMove, p4028, p4032, p4036, p4040, p4044, p4048,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4052#64) :
    effect [p4052, p4056, p4060] s = reloadStage .wrongActual s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp, p4052, p4056, p4060,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]


theorem wrongActual_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 4016#64) :
    run 12 s = Lower.wrongActual.result s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have follows : Follows base Lower.wrongActual.ops s := by
    simp (config := {decide := true, instances := true}) [Follows, Lower.ops,
       p4016, p4020, p4024, p4028, p4032, p4036, p4040, p4044, p4048, p4052, p4056, p4060, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, lower, error, pc, BitVec.add_assoc,
       address, NatExact.store_w, NatExact.gpr_w_pc]
  rw [show 12 = Lower.wrongActual.ops.length by rfl, runs _ s base code follows]
  change effect [p4052, p4056, p4060] (effect [p4028, p4032, p4036, p4040, p4044, p4048] (effect [p4016, p4020, p4024] s)) = _
  rw [spill_summary s base aligned pc]
  rw [payload_summary (spillStage .wrongActual s base) base
    (spillStage_aligned .wrongActual s base aligned) (spillStage_pc .wrongActual s base)]
  rw [reload_summary (payloadStage .wrongActual (spillStage .wrongActual s base) base) base
    (payloadStage_aligned .wrongActual _ base (spillStage_aligned .wrongActual s base aligned))
    (payloadStage_pc .wrongActual _ base)]
  exact stages_assemble .wrongActual s base

end SszArm.Measure.Result
