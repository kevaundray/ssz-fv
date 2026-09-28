import SszArm.MeasureResultStages

namespace SszArm.Measure.Result

private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3756#64) :
    effect [p3756, p3760, p3764] s = spillStage .scopeReserved s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair, p3756, p3760, p3764,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3768#64) :
    effect [p3768, p3772, p3776, p3780, p3784, p3788] s = payloadStage .scopeReserved s base := by
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Lower.high, Payload.store, zeroMove, p3768, p3772, p3776, p3780, p3784, p3788,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3792#64) :
    effect [p3792, p3796, p3800] s = reloadStage .scopeReserved s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp, p3792, p3796, p3800,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]


theorem scopeReserved_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3756#64) :
    run 12 s = Lower.scopeReserved.result s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have follows : Follows base Lower.scopeReserved.ops s := by
    simp (config := {decide := true, instances := true}) [Follows, Lower.ops,
       p3756, p3760, p3764, p3768, p3772, p3776, p3780, p3784, p3788, p3792, p3796, p3800, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, lower, error, pc, BitVec.add_assoc,
       address, NatExact.store_w, NatExact.gpr_w_pc]
  rw [show 12 = Lower.scopeReserved.ops.length by rfl, runs _ s base code follows]
  change effect [p3792, p3796, p3800] (effect [p3768, p3772, p3776, p3780, p3784, p3788] (effect [p3756, p3760, p3764] s)) = _
  rw [spill_summary s base aligned pc]
  rw [payload_summary (spillStage .scopeReserved s base) base
    (spillStage_aligned .scopeReserved s base aligned) (spillStage_pc .scopeReserved s base)]
  rw [reload_summary (payloadStage .scopeReserved (spillStage .scopeReserved s base) base) base
    (payloadStage_aligned .scopeReserved _ base (spillStage_aligned .scopeReserved s base aligned))
    (payloadStage_pc .scopeReserved _ base)]
  exact stages_assemble .scopeReserved s base

end SszArm.Measure.Result
