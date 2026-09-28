import SszArm.MeasureBitsLimitReserved
import SszArm.MeasureBitsLimitHeader

namespace SszArm.Measure.Bits.Limit

open Result

@[irreducible] def initial (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 1748#64) (w (.GPR 8#5) 1#64 s)

theorem initial_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 1744#64) : run 1 s = initial s base := by
  have follows : Follows base [p1744] s := ⟨error, pc, trivial⟩
  rw [show 1 = [p1744].length by rfl, runs _ s base code follows]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, p1744, Result.p3924, Op.effect, exec_inst, initial, state_simp_rules,
      bitvec_rules, minimal_theory, pc, BitVec.add_assoc, NatExact.gpr_w_pc]

@[irreducible] def suffix (s : ArmState) (base : BitVec 64) : ArmState :=
  statusResult (w (.GPR 8#5) 2#64
    (write_mem_bytes 16 (r (.GPR 19#5) s + 32#64) (r (.GPR 24#5) s ++ r (.GPR 21#5) s)
      (write_mem_bytes 16 (r (.GPR 19#5) s + 16#64) (r (.GPR 23#5) s ++ r (.GPR 22#5) s) s))) base

theorem suffix_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 1836#64) : run 6 s = suffix s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p1836, p1840, p1844, p1848, p3896, p3900] s := by
    simp (config := {decide := true, instances := true})
      [Follows, p1836, p1840, p1844, p1848, p3896, p3900, Op.effect, exec_inst,
        state_simp_rules, bitvec_rules, minimal_theory, pc, error, BitVec.add_assoc]
  rw [show 6 = [p1836, p1840, p1844, p1848, p3896, p3900].length by rfl,
    runs _ s base code follows]
  simp (config := {decide := true, instances := true})
    [effect, p1836, p1840, p1844, p1848, p3896, p3900, Op.effect, exec_inst,
      suffix, statusResult, state_simp_rules, bitvec_rules, minimal_theory,
      pc, BitVec.add_assoc]
  simp only [NatExact.store_w, w_of_w_shadow]

@[irreducible] def result (s : ArmState) (base : BitVec 64) : ArmState :=
  suffix (headerResult (reservedResult (initial s base) base) base) base

private theorem limit_error_pc (s : ArmState) (pc : BitVec 64) :
    r .ERR (w .PC pc s) = r .ERR s :=
  r_of_w_different (by decide)

private theorem limit_stack_pc (s : ArmState) (pc : BitVec 64) :
    r (.GPR 31#5) (w .PC pc s) = r (.GPR 31#5) s :=
  r_of_w_different (by decide)

private theorem limit_reserved_error (s : ArmState) (base : BitVec 64) :
    read_err (reservedResult s base) = read_err s := by
  simpa only [reservedResult, read_err, limit_error_pc] using Lower.error .wrongReserved s base

private theorem limit_header_error (s : ArmState) (base : BitVec 64) :
    read_err (headerResult s base) = read_err s := by
  simpa only [headerResult, read_err, limit_error_pc] using Lower.error .wrongHeader s base

private theorem limit_suffix_error (s : ArmState) (base : BitVec 64) :
    read_err (suffix s base) = read_err s := by
  unfold suffix
  rw [status_error]
  simp [state_simp_rules]

theorem executes (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1744#64) : run 29 s = result s base := by
  let a := initial s base
  let b := reservedResult a base
  let c := headerResult b base
  have arun : run 1 s = a := initial_run s base code error pc
  have ap : a.program = s.program := by simp [a, initial, state_simp_rules]
  have ae : read_err a = .None := by simpa [a, initial, state_simp_rules] using error
  have aa : CheckSPAlignment a := by
    simpa (config := {decide := true}) [a, initial, CheckSPAlignment, state_simp_rules] using aligned
  have brun : run 12 a = b := reserved_run a base (code.congr ap) ae aa
    (by simp [a, initial, state_simp_rules])
  have bp : b.program = s.program := by simp [b, reservedResult, state_simp_rules, ap]
  have be : read_err b = .None := (limit_reserved_error a base).trans ae
  have ba : CheckSPAlignment b := by
    simpa only [b, reservedResult, CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
      limit_stack_pc, Lower.sp] using aa
  have crun : run 10 b = c := header_run b base (code.congr bp) be ba
    (by simp [b, reservedResult, state_simp_rules])
  have cp : c.program = s.program := by simp [c, headerResult, state_simp_rules, bp]
  have ce : read_err c = .None := (limit_header_error b base).trans be
  have drun : run 6 c = suffix c base := suffix_run c base (code.congr cp) ce
    (by simp [c, headerResult, state_simp_rules])
  rw [show 29 = 1 + 12 + 10 + 6 by decide,
    run_plus, run_plus, run_plus, arun, brun, crun, drun]
  simp only [result, a, b, c]

@[simp] theorem result_program (s : ArmState) (base : BitVec 64) :
    (result s base).program = s.program := by
  simp [result, suffix, headerResult, reservedResult, initial, state_simp_rules]
@[simp] theorem result_error (s : ArmState) (base : BitVec 64) :
    read_err (result s base) = read_err s := by
  unfold result
  rw [limit_suffix_error, limit_header_error, limit_reserved_error]
  simp [initial, state_simp_rules]
@[simp] theorem result_pc (s : ArmState) (base : BitVec 64) :
    read_pc (result s base) = base + 4116#64 := by
  unfold result suffix
  exact status_pc _ base
@[simp] theorem result_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (result s base) = r (.GPR 31#5) s := by
  simp (config := {decide := true})
    [result, suffix, headerResult, reservedResult, initial, state_simp_rules]
@[simp] theorem result_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (result s base) = r (.SFP reg) s := by
  simp [result, suffix, headerResult, reservedResult, initial, state_simp_rules]

theorem result_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (eight : reg ≠ 8#5) (nine : reg ≠ 9#5) (ten : reg ≠ 10#5) :
    r (.GPR reg) (result s base) = r (.GPR reg) s := by
  simp [result, suffix, headerResult, reservedResult, initial, Lower.register, Lower.tmp,
    eight, nine, ten, NatExact.r_gpr_w, state_simp_rules]

end SszArm.Measure.Bits.Limit
