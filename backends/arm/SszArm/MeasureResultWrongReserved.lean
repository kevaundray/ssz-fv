import SszArm.MeasureResultStages

namespace SszArm.Measure.Result

private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4064#64) :
    effect [p4064, p4068, p4072] s = spillStage .wrongReserved s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair, p4064, p4068, p4072,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4076#64) :
    effect [p4076, p4080, p4084, p4088, p4092, p4096] s = payloadStage .wrongReserved s base := by
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Lower.high, Payload.store, zeroMove, p4076, p4080, p4084, p4088, p4092, p4096,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4100#64) :
    effect [p4100, p4104, p4108] s = reloadStage .wrongReserved s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp, p4100, p4104, p4108,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]


theorem wrongReserved_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 4064#64) :
    run 12 s = Lower.wrongReserved.result s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have follows : Follows base Lower.wrongReserved.ops s := by
    simp (config := {decide := true, instances := true}) [Follows, Lower.ops,
       p4064, p4068, p4072, p4076, p4080, p4084, p4088, p4092, p4096, p4100, p4104, p4108, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, lower, error, pc, BitVec.add_assoc,
       address, NatExact.store_w, NatExact.gpr_w_pc]
  rw [show 12 = Lower.wrongReserved.ops.length by rfl, runs _ s base code follows]
  change effect [p4100, p4104, p4108] (effect [p4076, p4080, p4084, p4088, p4092, p4096] (effect [p4064, p4068, p4072] s)) = _
  rw [spill_summary s base aligned pc]
  rw [payload_summary (spillStage .wrongReserved s base) base
    (spillStage_aligned .wrongReserved s base aligned) (spillStage_pc .wrongReserved s base)]
  rw [reload_summary (payloadStage .wrongReserved (spillStage .wrongReserved s base) base) base
    (payloadStage_aligned .wrongReserved _ base (spillStage_aligned .wrongReserved s base aligned))
    (payloadStage_pc .wrongReserved _ base)]
  exact stages_assemble .wrongReserved s base

end SszArm.Measure.Result
