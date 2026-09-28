import SszArm.MeasureResultSuccessHeader
import SszArm.MeasureResultSuccessLeading
import SszArm.MeasureResultSuccessStatus
import SszArm.MeasureResultMemory

namespace SszArm.Measure.Result

@[irreducible] def successPrefix (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 4152#64) (w (.GPR 8#5) 8#64
    (write_mem_bytes 16 (r (.GPR 19#5) s + 16#64)
      (r (.GPR 20#5) s ++ r (.GPR 21#5) s) s))

theorem success_prefix_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 4144#64) : run 2 s = successPrefix s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p4144, p4148] s := by
    simp (config := {decide := true, instances := true})
      [Follows, p4144, p4148, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, pc, error, BitVec.add_assoc]
  rw [show 2 = [p4144, p4148].length by rfl, runs _ s base code follows]
  simp (config := {decide := true, instances := true})
    [effect, p4144, p4148, Op.effect, exec_inst, successPrefix, state_simp_rules,
     bitvec_rules, minimal_theory, pc, BitVec.add_assoc]
  simp only [NatExact.store_w, w_of_w_shadow]

@[irreducible] def successResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 4116#64)
    (Lower.successStatus.result
      (Lower.successLeading.result
        (Lower.successHeader.result (successPrefix s base) base) base) base)

theorem success_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 4144#64) : run 33 s = successResult s base := by
  let a := successPrefix s base
  let b := Lower.successHeader.result a base
  let c := Lower.successLeading.result b base
  let d := Lower.successStatus.result c base
  have ap : a.program = s.program := by simp [a, successPrefix, state_simp_rules]
  have ae : read_err a = .None := by simpa [a, successPrefix, state_simp_rules] using error
  have aa : CheckSPAlignment a := by
    simpa (config := {decide := true}) [a, successPrefix, CheckSPAlignment, state_simp_rules] using aligned
  have ha : run 2 s = a := success_prefix_run s base code error pc
  have hb : run 10 a = b := successHeader_run a base (code.congr ap) ae aa
    (by simp [a, successPrefix, state_simp_rules])
  have bp : b.program = s.program := (Lower.program _ _ _).trans ap
  have be : read_err b = .None := (Lower.error _ _ _).trans ae
  have ba : CheckSPAlignment b := by
    simpa only [b, CheckSPAlignment, read_gpr, BitVec.setWidth_eq, Lower.sp] using aa
  have hc : run 10 b = c := successLeading_run b base (code.congr bp) be ba
    (by simp [b, Lower.finish])
  have cp : c.program = s.program := (Lower.program _ _ _).trans bp
  have ce : read_err c = .None := (Lower.error _ _ _).trans be
  have ca : CheckSPAlignment c := by
    simpa only [c, CheckSPAlignment, read_gpr, BitVec.setWidth_eq, Lower.sp] using ba
  have hd : run 10 c = d := successStatus_run c base (code.congr cp) ce ca
    (by simp [c, Lower.finish])
  have dp : d.program = s.program := (Lower.program _ _ _).trans cp
  have de : read_err d = .None := (Lower.error _ _ _).trans ce
  have dpc : read_pc d = base + 4272#64 := by simp [d, Lower.finish]
  have he : run 1 d = w .PC (base + 4116#64) d := by
    have follows : Follows base [p4272] d := ⟨de, dpc, trivial⟩
    rw [show 1 = [p4272].length by rfl, runs _ d base (code.congr dp) follows]
    change r .PC d = _ at dpc
    simp (config := {decide := true, instances := true})
      [effect, p4272, Op.effect, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, dpc, BitVec.add_assoc]
  rw [show 33 = 2 + 10 + 10 + 10 + 1 by decide,
    run_plus, run_plus, run_plus, run_plus, ha, hb, hc, hd, he]
  simp only [successResult, a, b, c, d]

@[simp] theorem success_program (s : ArmState) (base : BitVec 64) :
    (successResult s base).program = s.program := by
  simp [successResult, successPrefix, state_simp_rules]

@[simp] theorem success_error (s : ArmState) (base : BitVec 64) :
    read_err (successResult s base) = read_err s := by
  simp [successResult, Lower.result, Lower.memory, Lower.kind,
    Payload.store, savedPair, successPrefix, state_simp_rules]

@[simp] theorem success_pc (s : ArmState) (base : BitVec 64) :
    read_pc (successResult s base) = base + 4116#64 := by
  simp [successResult, state_simp_rules]

@[simp] theorem success_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (successResult s base) = r (.GPR 31#5) s := by
  simp (config := {decide := true}) [successResult, successPrefix, state_simp_rules]

theorem success_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (eight : reg ≠ 8#5) (nine : reg ≠ 9#5) (ten : reg ≠ 10#5) :
    r (.GPR reg) (successResult s base) = r (.GPR reg) s := by
  simp [successResult, successPrefix, Lower.register, Lower.tmp,
    eight, nine, ten, NatExact.r_gpr_w, state_simp_rules]

@[simp] theorem success_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (successResult s base) = r (.SFP reg) s := by
  simp [successResult, successPrefix, state_simp_rules]

end SszArm.Measure.Result
