import SszArm.MeasureResultWrongExpected
import SszArm.MeasureResultWrongHeader
import SszArm.MeasureResultWrongActual
import SszArm.MeasureResultWrongReserved
import SszArm.MeasureResultMemory

namespace SszArm.Measure.Result

@[irreducible] def wrongPrefix (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3928#64) (w (.GPR 8#5) 1#64 s)

theorem wrong_prefix_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3924#64) : run 1 s = wrongPrefix s base := by
  have follows : Follows base [p3924] s := ⟨error, pc, trivial⟩
  rw [show 1 = [p3924].length by rfl, runs _ s base code follows]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, p3924, Op.effect, exec_inst, wrongPrefix, state_simp_rules,
     bitvec_rules, minimal_theory, pc, BitVec.add_assoc, NatExact.gpr_w_pc]

@[irreducible] def wrongResult (s : ArmState) (base : BitVec 64) : ArmState :=
  statusResult
    (Lower.wrongReserved.result
      (Lower.wrongActual.result
        (Lower.wrongHeader.result
          (Lower.wrongExpected.result (wrongPrefix s base) base) base) base) base) base

theorem wrong_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3924#64) : run 48 s = wrongResult s base := by
  let a := wrongPrefix s base
  let b := Lower.wrongExpected.result a base
  let c := Lower.wrongHeader.result b base
  let d := Lower.wrongActual.result c base
  let e := Lower.wrongReserved.result d base
  have ap : a.program = s.program := by simp [a, wrongPrefix, state_simp_rules]
  have ae : read_err a = .None := by simpa [a, wrongPrefix, state_simp_rules] using error
  have aa : CheckSPAlignment a := by
    simpa (config := {decide := true}) [a, wrongPrefix, CheckSPAlignment, state_simp_rules] using aligned
  have ha : run 1 s = a := wrong_prefix_run s base code error pc
  have hb : run 12 a = b := wrongExpected_run a base (code.congr ap) ae aa
    (by simp [a, wrongPrefix, state_simp_rules])
  have bp : b.program = s.program := (Lower.program _ _ _).trans ap
  have be : read_err b = .None := (Lower.error _ _ _).trans ae
  have ba : CheckSPAlignment b := by
    simpa only [b, CheckSPAlignment, read_gpr, BitVec.setWidth_eq, Lower.sp] using aa
  have hc : run 10 b = c := wrongHeader_run b base (code.congr bp) be ba
    (by simp [b, Lower.finish])
  have cp : c.program = s.program := (Lower.program _ _ _).trans bp
  have ce : read_err c = .None := (Lower.error _ _ _).trans be
  have ca : CheckSPAlignment c := by
    simpa only [c, CheckSPAlignment, read_gpr, BitVec.setWidth_eq, Lower.sp] using ba
  have hd : run 12 c = d := wrongActual_run c base (code.congr cp) ce ca
    (by simp [c, Lower.finish])
  have dp : d.program = s.program := (Lower.program _ _ _).trans cp
  have de : read_err d = .None := (Lower.error _ _ _).trans ce
  have da : CheckSPAlignment d := by
    simpa only [d, CheckSPAlignment, read_gpr, BitVec.setWidth_eq, Lower.sp] using ca
  have he : run 12 d = e := wrongReserved_run d base (code.congr dp) de da
    (by simp [d, Lower.finish])
  have ep : e.program = s.program := (Lower.program _ _ _).trans dp
  have ee : read_err e = .None := (Lower.error _ _ _).trans de
  have epc : read_pc e = base + 4112#64 := by simp [e, Lower.finish]
  have hf : run 1 e = statusResult e base := by
    have follows : Follows base [p4112] e := ⟨ee, epc, trivial⟩
    rw [show 1 = [p4112].length by rfl, runs _ e base (code.congr ep) follows]
    change r .PC e = _ at epc
    simp (config := {decide := true, instances := true})
      [effect, p4112, Op.effect, exec_inst, statusResult, state_simp_rules,
       bitvec_rules, minimal_theory, epc, BitVec.add_assoc]
  rw [show 48 = 1 + 12 + 10 + 12 + 12 + 1 by decide,
    run_plus, run_plus, run_plus, run_plus, run_plus, ha, hb, hc, hd, he, hf]
  simp only [wrongResult, a, b, c, d, e]

@[simp] theorem wrong_program (s : ArmState) (base : BitVec 64) :
    (wrongResult s base).program = s.program := by
  simp [wrongResult, wrongPrefix, state_simp_rules]

@[simp] theorem wrong_error (s : ArmState) (base : BitVec 64) :
    read_err (wrongResult s base) = read_err s := by
  simp [wrongResult, statusResult, Lower.result, Lower.memory, Lower.kind,
    Payload.store, savedPair, wrongPrefix, state_simp_rules]

@[simp] theorem wrong_pc (s : ArmState) (base : BitVec 64) :
    read_pc (wrongResult s base) = base + 4116#64 := by
  simp [wrongResult, statusResult, state_simp_rules]

@[simp] theorem wrong_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (wrongResult s base) = r (.GPR 31#5) s := by
  simp (config := {decide := true}) [wrongResult, wrongPrefix, state_simp_rules]

theorem wrong_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (eight : reg ≠ 8#5) (nine : reg ≠ 9#5) (ten : reg ≠ 10#5) :
    r (.GPR reg) (wrongResult s base) = r (.GPR reg) s := by
  simp [wrongResult, wrongPrefix, Lower.register, Lower.tmp,
    eight, nine, ten, NatExact.r_gpr_w, state_simp_rules]

@[simp] theorem wrong_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (wrongResult s base) = r (.SFP reg) s := by
  simp [wrongResult, wrongPrefix, state_simp_rules]

end SszArm.Measure.Result
