import SszArm.MeasureResultLimitReserved
import SszArm.MeasureResultLimitHeader
import SszArm.MeasureResultScopeActual
import SszArm.MeasureResultMemory

namespace SszArm.Measure.Result

@[irreducible] def limitPrefix (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 2396#64) (w (.GPR 10#5) 1#64 s)

theorem limit_prefix_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2392#64) : run 1 s = limitPrefix s base := by
  have follows : Follows base [p2392] s := ⟨error, pc, trivial⟩
  rw [show 1 = [p2392].length by rfl, runs _ s base code follows]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, p2392, Op.effect, exec_inst, limitPrefix, state_simp_rules,
     bitvec_rules, minimal_theory, pc, BitVec.add_assoc, NatExact.gpr_w_pc]

@[irreducible] def limitPrepared (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3852#64) (w (.GPR 8#5) 2#64
    (write_mem_bytes 16 (r (.GPR 19#5) s + 16#64)
      (r (.GPR 9#5) s ++ r (.GPR 8#5) s) s))

theorem limit_prepared_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2484#64) : run 3 s = limitPrepared s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p2484, p2488, p2492] s := by
    simp (config := {decide := true, instances := true})
      [Follows, p2484, p2488, p2492, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, pc, error, BitVec.add_assoc]
  rw [show 3 = [p2484, p2488, p2492].length by rfl, runs _ s base code follows]
  simp (config := {decide := true, instances := true})
    [effect, p2484, p2488, p2492, Op.effect, exec_inst, limitPrepared, state_simp_rules,
     bitvec_rules, minimal_theory, pc, BitVec.add_assoc]
  simp only [NatExact.gpr_w_pc, w_of_w_shadow]

@[irreducible] def limitResult (s : ArmState) (base : BitVec 64) : ArmState :=
  statusResult (Lower.scopeActual.result
    (limitPrepared (Lower.limitHeader.result
      (Lower.limitReserved.result (limitPrefix s base) base) base) base) base) base

theorem limit_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2392#64) : run 39 s = limitResult s base := by
  let a := limitPrefix s base
  let b := Lower.limitReserved.result a base
  let c := Lower.limitHeader.result b base
  let d := limitPrepared c base
  let e := Lower.scopeActual.result d base
  have ap : a.program = s.program := by simp [a, limitPrefix, state_simp_rules]
  have ae : read_err a = .None := by simpa [a, limitPrefix, state_simp_rules] using error
  have aa : CheckSPAlignment a := by
    simpa (config := {decide := true}) [a, limitPrefix, CheckSPAlignment, state_simp_rules] using aligned
  have ha : run 1 s = a := limit_prefix_run s base code error pc
  have hb : run 12 a = b := limitReserved_run a base (code.congr ap) ae aa
    (by simp [a, limitPrefix, state_simp_rules])
  have bp : b.program = s.program := (Lower.program _ _ _).trans ap
  have be : read_err b = .None := (Lower.error _ _ _).trans ae
  have ba : CheckSPAlignment b := by
    simpa only [b, CheckSPAlignment, read_gpr, BitVec.setWidth_eq, Lower.sp] using aa
  have hc : run 10 b = c := limitHeader_run b base (code.congr bp) be ba
    (by simp [b, Lower.finish])
  have cp : c.program = s.program := (Lower.program _ _ _).trans bp
  have ce : read_err c = .None := (Lower.error _ _ _).trans be
  have ca : CheckSPAlignment c := by
    simpa only [c, CheckSPAlignment, read_gpr, BitVec.setWidth_eq, Lower.sp] using ba
  have hd : run 3 c = d := limit_prepared_run c base (code.congr cp) ce
    (by simp [c, Lower.finish])
  have dp : d.program = s.program := by simpa [d, limitPrepared, state_simp_rules] using cp
  have de : read_err d = .None := by simpa [d, limitPrepared, state_simp_rules] using ce
  have da : CheckSPAlignment d := by
    simpa (config := {decide := true}) [d, limitPrepared, CheckSPAlignment, state_simp_rules] using ca
  have he : run 11 d = e := scopeActual_run d base (code.congr dp) de da
    (by simp [d, limitPrepared, state_simp_rules])
  have ep : e.program = s.program := (Lower.program _ _ _).trans dp
  have ee : read_err e = .None := (Lower.error _ _ _).trans de
  have hf : run 2 e = statusResult e base := status_run e base (code.congr ep) ee
    (by simp [e, Lower.finish])
  rw [show 39 = 1 + 12 + 10 + 3 + 11 + 2 by decide,
    run_plus, run_plus, run_plus, run_plus, run_plus, ha, hb, hc, hd, he, hf]
  simp only [limitResult, a, b, c, d, e]

@[simp] theorem limit_program (s : ArmState) (base : BitVec 64) :
    (limitResult s base).program = s.program := by
  simp [limitResult, limitPrepared, limitPrefix, state_simp_rules]

@[simp] theorem limit_error (s : ArmState) (base : BitVec 64) :
    read_err (limitResult s base) = read_err s := by
  simp [limitResult, statusResult, Lower.result, Lower.memory, Lower.kind,
    Payload.store, savedPair, limitPrepared, limitPrefix, state_simp_rules]

@[simp] theorem limit_pc (s : ArmState) (base : BitVec 64) :
    read_pc (limitResult s base) = base + 4116#64 := by
  simp [limitResult, statusResult, state_simp_rules]

@[simp] theorem limit_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (limitResult s base) = r (.GPR 31#5) s := by
  simp (config := {decide := true}) [limitResult, limitPrepared, limitPrefix, state_simp_rules]

theorem limit_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (eight : reg ≠ 8#5) (nine : reg ≠ 9#5) (ten : reg ≠ 10#5) (eleven : reg ≠ 11#5) :
    r (.GPR reg) (limitResult s base) = r (.GPR reg) s := by
  simp [limitResult, limitPrepared, limitPrefix, Lower.register, Lower.tmp,
    eight, nine, ten, eleven, NatExact.r_gpr_w, state_simp_rules]

@[simp] theorem limit_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (limitResult s base) = r (.SFP reg) s := by
  simp [limitResult, limitPrepared, limitPrefix, state_simp_rules]

end SszArm.Measure.Result
