import SszArm.MeasureBitsScratchOps
import SszArm.MeasureResultStages

namespace SszArm.Measure.Bits.Scratch

open Result

@[irreducible] def actualResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3672#64) (Lower.wrongActual.result s base)

private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4016#64) :
    effect [p3624, p3628, p3632] s = spillStage .wrongActual s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair, p3624, Result.p4016, p3628, Result.p4020, p3632, Result.p4024,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4028#64) :
    effect [p3636, p3640, p3644, p3648, p3652, p3656] s = payloadStage .wrongActual s base := by
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Lower.high, Payload.store, zeroMove, p3636, Result.p4028, p3640, Result.p4032, p3644, Result.p4036, p3648, Result.p4040, p3652, Result.p4044, p3656, Result.p4048,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4052#64) :
    effect [p3660, p3664, p3668] s = reloadStage .wrongActual s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp, p3660, Result.p4052, p3664, Result.p4056, p3668, Result.p4060,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

theorem actual_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3624#64) :
    run 12 s = actualResult s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have follows : Follows base actualOps s := by
    simp (config := {decide := true, instances := true}) [Follows, actualOps,
      p3624, Result.p4016, p3628, Result.p4020, p3632, Result.p4024, p3636, Result.p4028, p3640, Result.p4032, p3644, Result.p4036, p3648, Result.p4040, p3652, Result.p4044, p3656, Result.p4048, p3660, Result.p4052, p3664, Result.p4056, p3668, Result.p4060, Op.effect, exec_inst, state_simp_rules,
      bitvec_rules, minimal_theory, lower, error, pc, BitVec.add_assoc,
      address, NatExact.store_w, NatExact.gpr_w_pc]
  rw [show 12 = actualOps.length by rfl, runs _ s base code follows]
  change effect [p3660, p3664, p3668] (effect [p3636, p3640, p3644, p3648, p3652, p3656] (effect [p3624, p3628, p3632] s)) = _
  let shifted : BitVec 64 := base - 392#64
  have shiftedPC : read_pc s = shifted + 4016#64 := by unfold read_pc; rw [pc]; dsimp [shifted]; bv_omega
  rw [spill_summary s shifted aligned shiftedPC]
  rw [payload_summary (spillStage .wrongActual s shifted) shifted
    (spillStage_aligned .wrongActual s shifted aligned) (spillStage_pc .wrongActual s shifted)]
  rw [reload_summary (payloadStage .wrongActual (spillStage .wrongActual s shifted) shifted) shifted
    (payloadStage_aligned .wrongActual _ shifted (spillStage_aligned .wrongActual s shifted aligned))
    (payloadStage_pc .wrongActual _ shifted), stages_assemble]
  have finishPC : shifted + 4064#64 = base + 3672#64 := by dsimp [shifted]; bv_omega
  simp only [actualResult, Lower.result, Lower.finish, finishPC, w, write_base_pc]

end SszArm.Measure.Bits.Scratch
