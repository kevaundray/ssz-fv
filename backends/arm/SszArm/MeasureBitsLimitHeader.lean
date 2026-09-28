import SszArm.MeasureBitsLimitOps
import SszArm.MeasureResultStages

namespace SszArm.Measure.Bits.Limit

open Result

@[irreducible] def headerResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 1836#64) (Lower.wrongHeader.result s base)

-- Use the accepted wrong-header stage model at its relocated PC, without
-- relocating CodeAt or replacing the actual 1796..1832 instruction witnesses.
private theorem spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3976#64) :
    effect [p1796, p1800, p1804] s = spillStage .wrongHeader s base := by
  change effect [Result.p3976, Result.p3980, Result.p3984] s = _
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [effect, spillStage, Lower.start, Lower.tmp, savedPair,
     Result.p3976, Result.p3980, Result.p3984, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, pc, BitVec.add_assoc,
     NatExact.store_w, NatExact.gpr_w_pc, lower, address] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem payload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3988#64) :
    effect [p1808, p1812, p1816, p1820] s = payloadStage .wrongHeader s base := by
  change effect [Result.p3988, Result.p3992, Result.p3996, Result.p4000] s = _
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [effect, payloadStage, Lower.finish, Lower.tmp, Lower.kind, Lower.offset,
     Lower.low, Lower.high, Payload.store, zeroMove,
     Result.p3988, Result.p3992, Result.p3996, Result.p4000,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 4004#64) :
    effect [p1824, p1828, p1832] s = reloadStage .wrongHeader s base := by
  change effect [Result.p4004, Result.p4008, Result.p4012] s = _
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, reloadStage, Lower.finish, Lower.tmp,
     Result.p4004, Result.p4008, Result.p4012, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem spill_follows (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1796#64) : Follows base [p1796, p1800, p1804] s := by
  let a := Result.p3976.effect s
  let b := Result.p3980.effect a
  change read_err s = .None ∧ read_pc s = base + 1796#64 ∧
    read_err a = .None ∧ read_pc a = base + 1800#64 ∧
    read_err b = .None ∧ read_pc b = base + 1804#64 ∧ True
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  simp (config := {decide := true, instances := true})
    [a, b, Result.p3976, Result.p3980, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, lower, error, pc,
     BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc]

private theorem payload_follows (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (pc : read_pc s = base + 1808#64) :
    Follows base [p1808, p1812, p1816, p1820] s := by
  let a := Result.p3988.effect s
  let b := Result.p3992.effect a
  let c := Result.p3996.effect b
  change read_err s = .None ∧ read_pc s = base + 1808#64 ∧
    read_err a = .None ∧ read_pc a = base + 1812#64 ∧
    read_err b = .None ∧ read_pc b = base + 1816#64 ∧
    read_err c = .None ∧ read_pc c = base + 1820#64 ∧ True
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  simp (config := {decide := true, instances := true})
    [a, b, c, Result.p3988, Result.p3992, Result.p3996, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, error, pc,
     BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc]

private theorem reload_follows (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1824#64) : Follows base [p1824, p1828, p1832] s := by
  let a := Result.p4004.effect s
  let b := Result.p4008.effect a
  change read_err s = .None ∧ read_pc s = base + 1824#64 ∧
    read_err a = .None ∧ read_pc a = base + 1828#64 ∧
    read_err b = .None ∧ read_pc b = base + 1832#64 ∧ True
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  simp (config := {decide := true, instances := true})
    [a, b, Result.p4004, Result.p4008, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, error, pc,
     BitVec.add_assoc, NatExact.gpr_w_pc]

private theorem spill_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1796#64) :
    run 3 s = spillStage .wrongHeader s (base - 2180#64) := by
  rw [show 3 = [p1796, p1800, p1804].length by rfl,
    runs _ s base code (spill_follows s base error aligned pc)]
  exact spill_summary s (base - 2180#64) aligned (by rw [pc]; bv_omega)

private theorem payload_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1808#64) :
    run 4 s = payloadStage .wrongHeader s (base - 2180#64) := by
  rw [show 4 = [p1808, p1812, p1816, p1820].length by rfl,
    runs _ s base code (payload_follows s base error pc)]
  exact payload_summary s (base - 2180#64) aligned (by rw [pc]; bv_omega)

private theorem reload_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1824#64) :
    run 3 s = reloadStage .wrongHeader s (base - 2180#64) := by
  rw [show 3 = [p1824, p1828, p1832].length by rfl,
    runs _ s base code (reload_follows s base error aligned pc)]
  exact reload_summary s (base - 2180#64) aligned (by rw [pc]; bv_omega)

private theorem relocated_result (s : ArmState) (base : BitVec 64) :
    Lower.wrongHeader.result s (base - 2180#64) = headerResult s base := by
  have finishPc : base - 2180#64 + 4016#64 = base + 1836#64 := by bv_omega
  simp only [headerResult, Lower.result, Lower.finish, finishPc, w_of_w_shadow]

theorem header_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1796#64) :
    run 10 s = headerResult s base := by
  let a := spillStage .wrongHeader s (base - 2180#64)
  let b := payloadStage .wrongHeader a (base - 2180#64)
  have ap : a.program = s.program := by
    simp [a, spillStage, savedPair, state_simp_rules]
  have ae : read_err a = .None := by
    simpa [a, spillStage, savedPair, state_simp_rules] using error
  have aa : CheckSPAlignment a :=
    spillStage_aligned .wrongHeader s (base - 2180#64) aligned
  have ac : read_pc a = base + 1808#64 := by
    rw [show read_pc a = base - 2180#64 + 3988#64 from
      spillStage_pc .wrongHeader s (base - 2180#64)]
    bv_omega
  have ha : run 3 s = a := spill_run s base code error aligned pc
  have hb : run 4 a = b := payload_run a base (code.congr ap) ae aa ac
  have bp : b.program = a.program := by
    simp [b, payloadStage, Lower.kind, Payload.store, state_simp_rules]
  have be : read_err b = .None := by
    simpa [b, payloadStage, Lower.kind, Payload.store, state_simp_rules] using ae
  have ba : CheckSPAlignment b :=
    payloadStage_aligned .wrongHeader a (base - 2180#64) aa
  have bc : read_pc b = base + 1824#64 := by
    rw [show read_pc b = base - 2180#64 + 4004#64 from
      payloadStage_pc .wrongHeader a (base - 2180#64)]
    bv_omega
  have hc : run 3 b = reloadStage .wrongHeader b (base - 2180#64) :=
    reload_run b base (code.congr (bp.trans ap)) be ba bc
  rw [show 10 = 3 + 4 + 3 by decide, run_plus, run_plus, ha, hb, hc]
  exact (stages_assemble .wrongHeader s (base - 2180#64)).trans
    (relocated_result s base)

end SszArm.Measure.Bits.Limit
