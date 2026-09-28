import SszArm.MeasureBitsScratchOps
import SszArm.MeasureResultStages

namespace SszArm.Measure.Bits.Scratch

open Result

@[irreducible] def reservedResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3580#64) (Lower.wrongReserved.result s base)

private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4064#64) :
    effect [p3532, p3536, p3540] s = spillStage .wrongReserved s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair, p3532, Result.p4064, p3536, Result.p4068, p3540, Result.p4072,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4076#64) :
    effect [p3544, p3548, p3552, p3556, p3560, p3564] s = payloadStage .wrongReserved s base := by
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Lower.high, Payload.store, zeroMove, p3544, Result.p4076, p3548, Result.p4080, p3552, Result.p4084, p3556, Result.p4088, p3560, Result.p4092, p3564, Result.p4096,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4100#64) :
    effect [p3568, p3572, p3576] s = reloadStage .wrongReserved s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp, p3568, Result.p4100, p3572, Result.p4104, p3576, Result.p4108,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

theorem reserved_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3532#64) :
    run 12 s = reservedResult s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have follows : Follows base reservedOps s := by
    simp (config := {decide := true, instances := true}) [Follows, reservedOps,
      p3532, Result.p4064, p3536, Result.p4068, p3540, Result.p4072, p3544, Result.p4076, p3548, Result.p4080, p3552, Result.p4084, p3556, Result.p4088, p3560, Result.p4092, p3564, Result.p4096, p3568, Result.p4100, p3572, Result.p4104, p3576, Result.p4108, Op.effect, exec_inst, state_simp_rules,
      bitvec_rules, minimal_theory, lower, error, pc, BitVec.add_assoc,
      address, NatExact.store_w, NatExact.gpr_w_pc]
  rw [show 12 = reservedOps.length by rfl, runs _ s base code follows]
  change effect [p3568, p3572, p3576] (effect [p3544, p3548, p3552, p3556, p3560, p3564] (effect [p3532, p3536, p3540] s)) = _
  let shifted : BitVec 64 := base - 532#64
  have shiftedPC : read_pc s = shifted + 4064#64 := by unfold read_pc; rw [pc]; dsimp [shifted]; bv_omega
  rw [spill_summary s shifted aligned shiftedPC]
  rw [payload_summary (spillStage .wrongReserved s shifted) shifted
    (spillStage_aligned .wrongReserved s shifted aligned) (spillStage_pc .wrongReserved s shifted)]
  rw [reload_summary (payloadStage .wrongReserved (spillStage .wrongReserved s shifted) shifted) shifted
    (payloadStage_aligned .wrongReserved _ shifted (spillStage_aligned .wrongReserved s shifted aligned))
    (payloadStage_pc .wrongReserved _ shifted), stages_assemble]
  have finishPC : shifted + 4112#64 = base + 3580#64 := by dsimp [shifted]; bv_omega
  simp only [reservedResult, Lower.result, Lower.finish, finishPC, w, write_base_pc]

end SszArm.Measure.Bits.Scratch
