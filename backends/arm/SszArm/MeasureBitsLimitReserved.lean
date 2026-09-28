import SszArm.MeasureBitsLimitOps
import SszArm.MeasureResultStages

namespace SszArm.Measure.Bits.Limit

open Result

@[irreducible] def reservedResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 1796#64) (Lower.wrongReserved.result s base)

-- Relocate only the pure stage summaries. Every execution witness below
-- still fetches the original 1748..1792 rows from the actual CodeAt base.
private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4064#64) :
    effect [p1748, p1752, p1756] s = spillStage .wrongReserved s base := by
  change effect [Result.p4064, Result.p4068, Result.p4072] s = _
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair,
     Result.p4064, Result.p4068, Result.p4072, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, pc, BitVec.add_assoc,
     NatExact.store_w, NatExact.gpr_w_pc, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4076#64) :
    effect [p1760, p1764, p1768, p1772, p1776, p1780] s =
      payloadStage .wrongReserved s base := by
  change effect
    [Result.p4076, Result.p4080, Result.p4084, Result.p4088, Result.p4092, Result.p4096] s = _
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Lower.high, Payload.store, zeroMove,
     Result.p4076, Result.p4080, Result.p4084, Result.p4088, Result.p4092, Result.p4096,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4100#64) :
    effect [p1784, p1788, p1792] s = reloadStage .wrongReserved s base := by
  change effect [Result.p4100, Result.p4104, Result.p4108] s = _
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp,
     Result.p4100, Result.p4104, Result.p4108, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem spill_follows (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1748#64) : Follows base [p1748, p1752, p1756] s := by
  let a := Result.p4064.effect s
  let b := Result.p4068.effect a
  change read_err s = .None ∧ read_pc s = base + 1748#64 ∧
    read_err a = .None ∧ read_pc a = base + 1752#64 ∧
    read_err b = .None ∧ read_pc b = base + 1756#64 ∧ True
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  simp (config := {decide := true, instances := true})
    [a, b, Result.p4064, Result.p4068, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, lower, error, pc,
     BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc]

private theorem payload_follows (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (pc : read_pc s = base + 1760#64) :
    Follows base [p1760, p1764, p1768, p1772, p1776, p1780] s := by
  let a := Result.p4076.effect s
  let b := Result.p4080.effect a
  let c := Result.p4084.effect b
  let d := Result.p4088.effect c
  let e := Result.p4092.effect d
  change read_err s = .None ∧ read_pc s = base + 1760#64 ∧
    read_err a = .None ∧ read_pc a = base + 1764#64 ∧
    read_err b = .None ∧ read_pc b = base + 1768#64 ∧
    read_err c = .None ∧ read_pc c = base + 1772#64 ∧
    read_err d = .None ∧ read_pc d = base + 1776#64 ∧
    read_err e = .None ∧ read_pc e = base + 1780#64 ∧ True
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  simp (config := {decide := true, instances := true})
    [a, b, c, d, e, Result.p4076, Result.p4080, Result.p4084,
     Result.p4088, Result.p4092, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, error, pc,
     BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc]

private theorem reload_follows (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1784#64) : Follows base [p1784, p1788, p1792] s := by
  let a := Result.p4100.effect s
  let b := Result.p4104.effect a
  change read_err s = .None ∧ read_pc s = base + 1784#64 ∧
    read_err a = .None ∧ read_pc a = base + 1788#64 ∧
    read_err b = .None ∧ read_pc b = base + 1792#64 ∧ True
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  simp (config := {decide := true, instances := true})
    [a, b, Result.p4100, Result.p4104, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, error, pc,
     BitVec.add_assoc, NatExact.gpr_w_pc]

private theorem spill_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1748#64) :
    run 3 s = spillStage .wrongReserved s (base - 2316#64) := by
  rw [show 3 = [p1748, p1752, p1756].length by rfl,
    runs _ s base code (spill_follows s base error aligned pc)]
  exact spill_summary s (base - 2316#64) aligned (by rw [pc]; bv_omega)

private theorem payload_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1760#64) :
    run 6 s = payloadStage .wrongReserved s (base - 2316#64) := by
  rw [show 6 = [p1760, p1764, p1768, p1772, p1776, p1780].length by rfl,
    runs _ s base code (payload_follows s base error pc)]
  exact payload_summary s (base - 2316#64) aligned (by rw [pc]; bv_omega)

private theorem reload_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1784#64) :
    run 3 s = reloadStage .wrongReserved s (base - 2316#64) := by
  rw [show 3 = [p1784, p1788, p1792].length by rfl,
    runs _ s base code (reload_follows s base error aligned pc)]
  exact reload_summary s (base - 2316#64) aligned (by rw [pc]; bv_omega)

private theorem relocated_result (s : ArmState) (base : BitVec 64) :
    Lower.wrongReserved.result s (base - 2316#64) = reservedResult s base := by
  have finishPc : base - 2316#64 + 4112#64 = base + 1796#64 := by bv_omega
  simp only [reservedResult, Lower.result, Lower.finish, finishPc, w_of_w_shadow]

theorem reserved_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1748#64) :
    run 12 s = reservedResult s base := by
  let a := spillStage .wrongReserved s (base - 2316#64)
  let b := payloadStage .wrongReserved a (base - 2316#64)
  have ap : a.program = s.program := by
    simp [a, spillStage, savedPair, state_simp_rules]
  have ae : read_err a = .None := by
    simpa [a, spillStage, savedPair, state_simp_rules] using error
  have aa : CheckSPAlignment a :=
    spillStage_aligned .wrongReserved s (base - 2316#64) aligned
  have ac : read_pc a = base + 1760#64 := by
    rw [show read_pc a = base - 2316#64 + 4076#64 from
      spillStage_pc .wrongReserved s (base - 2316#64)]
    bv_omega
  have ha : run 3 s = a := spill_run s base code error aligned pc
  have hb : run 6 a = b := payload_run a base (code.congr ap) ae aa ac
  have bp : b.program = a.program := by
    simp [b, payloadStage, Lower.kind, Payload.store, state_simp_rules]
  have be : read_err b = .None := by
    simpa [b, payloadStage, Lower.kind, Payload.store, state_simp_rules] using ae
  have ba : CheckSPAlignment b :=
    payloadStage_aligned .wrongReserved a (base - 2316#64) aa
  have bc : read_pc b = base + 1784#64 := by
    rw [show read_pc b = base - 2316#64 + 4100#64 from
      payloadStage_pc .wrongReserved a (base - 2316#64)]
    bv_omega
  have hc : run 3 b = reloadStage .wrongReserved b (base - 2316#64) :=
    reload_run b base (code.congr (bp.trans ap)) be ba bc
  rw [show 12 = 3 + 6 + 3 by decide, run_plus, run_plus, ha, hb, hc]
  exact (stages_assemble .wrongReserved s (base - 2316#64)).trans
    (relocated_result s base)

end SszArm.Measure.Bits.Limit
