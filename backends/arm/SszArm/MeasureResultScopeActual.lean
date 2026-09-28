import SszArm.MeasureResultStages

namespace SszArm.Measure.Result

private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3852#64) :
    effect [p3852, p3856, p3860] s = spillStage .scopeActual s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair, p3852, p3856, p3860,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3864#64) :
    effect [p3864, p3868, p3872, p3876, p3880] s = payloadStage .scopeActual s base := by
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Lower.high, Payload.store, zeroMove, p3864, p3868, p3872, p3876, p3880,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3884#64) :
    effect [p3884, p3888, p3892] s = reloadStage .scopeActual s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp, p3884, p3888, p3892,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]


theorem scopeActual_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3852#64) :
    run 11 s = Lower.scopeActual.result s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have follows : Follows base Lower.scopeActual.ops s := by
    simp (config := {decide := true, instances := true}) [Follows, Lower.ops,
       p3852, p3856, p3860, p3864, p3868, p3872, p3876, p3880, p3884, p3888, p3892, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, lower, error, pc, BitVec.add_assoc,
       address, NatExact.store_w, NatExact.gpr_w_pc]
  rw [show 11 = Lower.scopeActual.ops.length by rfl, runs _ s base code follows]
  change effect [p3884, p3888, p3892] (effect [p3864, p3868, p3872, p3876, p3880] (effect [p3852, p3856, p3860] s)) = _
  rw [spill_summary s base aligned pc]
  rw [payload_summary (spillStage .scopeActual s base) base
    (spillStage_aligned .scopeActual s base aligned) (spillStage_pc .scopeActual s base)]
  rw [reload_summary (payloadStage .scopeActual (spillStage .scopeActual s base) base) base
    (payloadStage_aligned .scopeActual _ base (spillStage_aligned .scopeActual s base aligned))
    (payloadStage_pc .scopeActual _ base)]
  exact stages_assemble .scopeActual s base

end SszArm.Measure.Result
