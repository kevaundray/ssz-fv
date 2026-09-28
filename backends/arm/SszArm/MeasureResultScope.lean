import SszArm.MeasureResultScopeReserved
import SszArm.MeasureResultScopeHeader
import SszArm.MeasureResultScopeActual
import SszArm.MeasureResultMemory

namespace SszArm.Measure.Result

@[irreducible] def scopePrefix (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3756#64) (w (.GPR 10#5) 1#64 s)

theorem scope_prefix_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3752#64) : run 1 s = scopePrefix s base := by
  have follows : Follows base [p3752] s := ⟨error, pc, trivial⟩
  rw [show 1 = [p3752].length by rfl, runs _ s base code follows]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, p3752, Op.effect, exec_inst, scopePrefix, state_simp_rules,
     bitvec_rules, minimal_theory, pc, BitVec.add_assoc, NatExact.gpr_w_pc]

@[irreducible] def scopePrepared (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3852#64) (w (.GPR 8#5) 3#64
    (write_mem_bytes 16 (r (.GPR 19#5) s + 16#64)
      (r (.GPR 9#5) s ++ r (.GPR 8#5) s) s))

theorem scope_prepared_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3844#64) : run 2 s = scopePrepared s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p3844, p3848] s := by
    simp (config := {decide := true, instances := true})
      [Follows, p3844, p3848, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, pc, error, BitVec.add_assoc]
  rw [show 2 = [p3844, p3848].length by rfl, runs _ s base code follows]
  simp (config := {decide := true, instances := true})
    [effect, p3844, p3848, Op.effect, exec_inst, scopePrepared, state_simp_rules,
     bitvec_rules, minimal_theory, pc, BitVec.add_assoc]
  simp only [NatExact.gpr_w_pc, w_of_w_shadow]

@[irreducible] def scopeResult (s : ArmState) (base : BitVec 64) : ArmState :=
  statusResult (Lower.scopeActual.result
    (scopePrepared (Lower.scopeHeader.result
      (Lower.scopeReserved.result (scopePrefix s base) base) base) base) base) base

theorem scope_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3752#64) : run 38 s = scopeResult s base := by
  let a := scopePrefix s base
  let b := Lower.scopeReserved.result a base
  let c := Lower.scopeHeader.result b base
  let d := scopePrepared c base
  let e := Lower.scopeActual.result d base
  have ap : a.program = s.program := by simp [a, scopePrefix, state_simp_rules]
  have ae : read_err a = .None := by simpa [a, scopePrefix, state_simp_rules] using error
  have aa : CheckSPAlignment a := by
    simpa (config := {decide := true}) [a, scopePrefix, CheckSPAlignment, state_simp_rules] using aligned
  have ha : run 1 s = a := scope_prefix_run s base code error pc
  have hb : run 12 a = b := scopeReserved_run a base (code.congr ap) ae aa
    (by simp [a, scopePrefix, state_simp_rules])
  have bp : b.program = s.program := (Lower.program _ _ _).trans ap
  have be : read_err b = .None := (Lower.error _ _ _).trans ae
  have ba : CheckSPAlignment b := by
    simpa only [b, CheckSPAlignment, read_gpr, BitVec.setWidth_eq, Lower.sp] using aa
  have hc : run 10 b = c := scopeHeader_run b base (code.congr bp) be ba
    (by simp [b, Lower.finish])
  have cp : c.program = s.program := (Lower.program _ _ _).trans bp
  have ce : read_err c = .None := (Lower.error _ _ _).trans be
  have ca : CheckSPAlignment c := by
    simpa only [c, CheckSPAlignment, read_gpr, BitVec.setWidth_eq, Lower.sp] using ba
  have hd : run 2 c = d := scope_prepared_run c base (code.congr cp) ce
    (by simp [c, Lower.finish])
  have dp : d.program = s.program := by simpa [d, scopePrepared, state_simp_rules] using cp
  have de : read_err d = .None := by simpa [d, scopePrepared, state_simp_rules] using ce
  have da : CheckSPAlignment d := by
    simpa (config := {decide := true}) [d, scopePrepared, CheckSPAlignment, state_simp_rules] using ca
  have he : run 11 d = e := scopeActual_run d base (code.congr dp) de da
    (by simp [d, scopePrepared, state_simp_rules])
  have ep : e.program = s.program := (Lower.program _ _ _).trans dp
  have ee : read_err e = .None := (Lower.error _ _ _).trans de
  have hf : run 2 e = statusResult e base := status_run e base (code.congr ep) ee
    (by simp [e, Lower.finish])
  rw [show 38 = 1 + 12 + 10 + 2 + 11 + 2 by decide,
    run_plus, run_plus, run_plus, run_plus, run_plus, ha, hb, hc, hd, he, hf]
  simp only [scopeResult, a, b, c, d, e]

@[simp] theorem scope_program (s : ArmState) (base : BitVec 64) :
    (scopeResult s base).program = s.program := by
  simp [scopeResult, scopePrepared, scopePrefix, state_simp_rules]

@[simp] theorem scope_error (s : ArmState) (base : BitVec 64) :
    read_err (scopeResult s base) = read_err s := by
  simp [scopeResult, statusResult, Lower.result, Lower.memory, Lower.kind,
    Payload.store, savedPair, scopePrepared, scopePrefix, state_simp_rules]

@[simp] theorem scope_pc (s : ArmState) (base : BitVec 64) :
    read_pc (scopeResult s base) = base + 4116#64 := by
  simp [scopeResult, statusResult, state_simp_rules]

@[simp] theorem scope_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (scopeResult s base) = r (.GPR 31#5) s := by
  simp (config := {decide := true}) [scopeResult, scopePrepared, scopePrefix, state_simp_rules]

theorem scope_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (eight : reg ≠ 8#5) (nine : reg ≠ 9#5) (ten : reg ≠ 10#5) (eleven : reg ≠ 11#5) :
    r (.GPR reg) (scopeResult s base) = r (.GPR reg) s := by
  simp [scopeResult, scopePrepared, scopePrefix, Lower.register, Lower.tmp,
    eight, nine, ten, eleven, NatExact.r_gpr_w, state_simp_rules]

@[simp] theorem scope_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (scopeResult s base) = r (.SFP reg) s := by
  simp [scopeResult, scopePrepared, scopePrefix, state_simp_rules]

end SszArm.Measure.Result
