import SszArm.MeasureResultStages

namespace SszArm.Measure.Result

private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3804#64) :
    effect [p3804, p3808, p3812] s = spillStage .scopeHeader s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair, p3804, p3808, p3812,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3816#64) :
    effect [p3816, p3820, p3824, p3828] s = payloadStage .scopeHeader s base := by
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Lower.high, Payload.store, zeroMove, p3816, p3820, p3824, p3828,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3832#64) :
    effect [p3832, p3836, p3840] s = reloadStage .scopeHeader s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp, p3832, p3836, p3840,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]


theorem scopeHeader_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3804#64) :
    run 10 s = Lower.scopeHeader.result s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have follows : Follows base Lower.scopeHeader.ops s := by
    simp (config := {decide := true, instances := true}) [Follows, Lower.ops,
       p3804, p3808, p3812, p3816, p3820, p3824, p3828, p3832, p3836, p3840, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, lower, error, pc, BitVec.add_assoc,
       address, NatExact.store_w, NatExact.gpr_w_pc]
  rw [show 10 = Lower.scopeHeader.ops.length by rfl, runs _ s base code follows]
  change effect [p3832, p3836, p3840] (effect [p3816, p3820, p3824, p3828] (effect [p3804, p3808, p3812] s)) = _
  rw [spill_summary s base aligned pc]
  rw [payload_summary (spillStage .scopeHeader s base) base
    (spillStage_aligned .scopeHeader s base aligned) (spillStage_pc .scopeHeader s base)]
  rw [reload_summary (payloadStage .scopeHeader (spillStage .scopeHeader s base) base) base
    (payloadStage_aligned .scopeHeader _ base (spillStage_aligned .scopeHeader s base aligned))
    (payloadStage_pc .scopeHeader _ base)]
  exact stages_assemble .scopeHeader s base

end SszArm.Measure.Result
