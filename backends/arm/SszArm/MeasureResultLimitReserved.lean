import SszArm.MeasureResultStages

namespace SszArm.Measure.Result

private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 2396#64) :
    effect [p2396, p2400, p2404] s = spillStage .limitReserved s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair, p2396, p2400, p2404,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 2408#64) :
    effect [p2408, p2412, p2416, p2420, p2424, p2428] s = payloadStage .limitReserved s base := by
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Lower.high, Payload.store, zeroMove, p2408, p2412, p2416, p2420, p2424, p2428,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 2432#64) :
    effect [p2432, p2436, p2440] s = reloadStage .limitReserved s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp, p2432, p2436, p2440,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]


theorem limitReserved_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2396#64) :
    run 12 s = Lower.limitReserved.result s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have follows : Follows base Lower.limitReserved.ops s := by
    simp (config := {decide := true, instances := true}) [Follows, Lower.ops,
       p2396, p2400, p2404, p2408, p2412, p2416, p2420, p2424, p2428, p2432, p2436, p2440, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, lower, error, pc, BitVec.add_assoc,
       address, NatExact.store_w, NatExact.gpr_w_pc]
  rw [show 12 = Lower.limitReserved.ops.length by rfl, runs _ s base code follows]
  change effect [p2432, p2436, p2440] (effect [p2408, p2412, p2416, p2420, p2424, p2428] (effect [p2396, p2400, p2404] s)) = _
  rw [spill_summary s base aligned pc]
  rw [payload_summary (spillStage .limitReserved s base) base
    (spillStage_aligned .limitReserved s base aligned) (spillStage_pc .limitReserved s base)]
  rw [reload_summary (payloadStage .limitReserved (spillStage .limitReserved s base) base) base
    (payloadStage_aligned .limitReserved _ base (spillStage_aligned .limitReserved s base aligned))
    (payloadStage_pc .limitReserved _ base)]
  exact stages_assemble .limitReserved s base

end SszArm.Measure.Result
