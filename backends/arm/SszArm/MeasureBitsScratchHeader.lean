import SszArm.MeasureBitsScratchOps
import SszArm.MeasureResultStages

namespace SszArm.Measure.Bits.Scratch

open Result

@[irreducible] def headerResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3620#64) (Lower.wrongHeader.result s base)

private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3976#64) :
    effect [p3580, p3584, p3588] s = spillStage .wrongHeader s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair, p3580, Result.p3976, p3584, Result.p3980, p3588, Result.p3984,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3988#64) :
    effect [p3592, p3596, p3600, p3604] s = payloadStage .wrongHeader s base := by
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Lower.high, Payload.store, zeroMove, p3592, Result.p3988, p3596, Result.p3992, p3600, Result.p3996, p3604, Result.p4000,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4004#64) :
    effect [p3608, p3612, p3616] s = reloadStage .wrongHeader s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp, p3608, Result.p4004, p3612, Result.p4008, p3616, Result.p4012,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

theorem header_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3580#64) :
    run 10 s = headerResult s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have follows : Follows base headerOps s := by
    simp (config := {decide := true, instances := true}) [Follows, headerOps,
      p3580, Result.p3976, p3584, Result.p3980, p3588, Result.p3984, p3592, Result.p3988, p3596, Result.p3992, p3600, Result.p3996, p3604, Result.p4000, p3608, Result.p4004, p3612, Result.p4008, p3616, Result.p4012, Op.effect, exec_inst, state_simp_rules,
      bitvec_rules, minimal_theory, lower, error, pc, BitVec.add_assoc,
      address, NatExact.store_w, NatExact.gpr_w_pc]
  rw [show 10 = headerOps.length by rfl, runs _ s base code follows]
  change effect [p3608, p3612, p3616] (effect [p3592, p3596, p3600, p3604] (effect [p3580, p3584, p3588] s)) = _
  let shifted : BitVec 64 := base - 396#64
  have shiftedPC : read_pc s = shifted + 3976#64 := by unfold read_pc; rw [pc]; dsimp [shifted]; bv_omega
  rw [spill_summary s shifted aligned shiftedPC]
  rw [payload_summary (spillStage .wrongHeader s shifted) shifted
    (spillStage_aligned .wrongHeader s shifted aligned) (spillStage_pc .wrongHeader s shifted)]
  rw [reload_summary (payloadStage .wrongHeader (spillStage .wrongHeader s shifted) shifted) shifted
    (payloadStage_aligned .wrongHeader _ shifted (spillStage_aligned .wrongHeader s shifted aligned))
    (payloadStage_pc .wrongHeader _ shifted), stages_assemble]
  have finishPC : shifted + 4016#64 = base + 3620#64 := by dsimp [shifted]; bv_omega
  simp only [headerResult, Lower.result, Lower.finish, finishPC, w, write_base_pc]

end SszArm.Measure.Bits.Scratch
