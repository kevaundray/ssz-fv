import SszArm.MeasureBitsScratchOps
import SszArm.MeasureResultStages

namespace SszArm.Measure.Bits.Scratch

open Result

@[irreducible] def expectedResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3720#64) (Lower.wrongExpected.result s base)

private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3928#64) :
    effect [p3672, p3676, p3680] s = spillStage .wrongExpected s base := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair, p3672, Result.p3928, p3676, Result.p3932, p3680, Result.p3936,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3940#64) :
    effect [p3684, p3688, p3692, p3696, p3700, p3704] s = payloadStage .wrongExpected s base := by
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Lower.high, Payload.store, zeroMove, p3684, Result.p3940, p3688, Result.p3944, p3692, Result.p3948, p3696, Result.p3952, p3700, Result.p3956, p3704, Result.p3960,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3964#64) :
    effect [p3708, p3712, p3716] s = reloadStage .wrongExpected s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp, p3708, Result.p3964, p3712, Result.p3968, p3716, Result.p3972,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

theorem expected_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3672#64) :
    run 12 s = expectedResult s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have follows : Follows base expectedOps s := by
    simp (config := {decide := true, instances := true}) [Follows, expectedOps,
      p3672, Result.p3928, p3676, Result.p3932, p3680, Result.p3936, p3684, Result.p3940, p3688, Result.p3944, p3692, Result.p3948, p3696, Result.p3952, p3700, Result.p3956, p3704, Result.p3960, p3708, Result.p3964, p3712, Result.p3968, p3716, Result.p3972, Op.effect, exec_inst, state_simp_rules,
      bitvec_rules, minimal_theory, lower, error, pc, BitVec.add_assoc,
      address, NatExact.store_w, NatExact.gpr_w_pc]
  rw [show 12 = expectedOps.length by rfl, runs _ s base code follows]
  change effect [p3708, p3712, p3716] (effect [p3684, p3688, p3692, p3696, p3700, p3704] (effect [p3672, p3676, p3680] s)) = _
  let shifted : BitVec 64 := base - 256#64
  have shiftedPC : read_pc s = shifted + 3928#64 := by unfold read_pc; rw [pc]; dsimp [shifted]; bv_omega
  rw [spill_summary s shifted aligned shiftedPC]
  rw [payload_summary (spillStage .wrongExpected s shifted) shifted
    (spillStage_aligned .wrongExpected s shifted aligned) (spillStage_pc .wrongExpected s shifted)]
  rw [reload_summary (payloadStage .wrongExpected (spillStage .wrongExpected s shifted) shifted) shifted
    (payloadStage_aligned .wrongExpected _ shifted (spillStage_aligned .wrongExpected s shifted aligned))
    (payloadStage_pc .wrongExpected _ shifted), stages_assemble]
  have finishPC : shifted + 3976#64 = base + 3720#64 := by dsimp [shifted]; bv_omega
  simp only [expectedResult, Lower.result, Lower.finish, finishPC, w, write_base_pc]

end SszArm.Measure.Bits.Scratch
