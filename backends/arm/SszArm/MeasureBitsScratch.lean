import SszArm.MeasureBitsScratchReserved
import SszArm.MeasureBitsScratchHeader
import SszArm.MeasureBitsScratchActual
import SszArm.MeasureBitsScratchExpected

namespace SszArm.Measure.Bits.Scratch

open Result
open Delimited (MemoryFrame)
open UintCodec (widthLoad)

@[irreducible] def initialResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3532#64) (w (.GPR 8#5) 1#64 s)

@[irreducible] def statusReady (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3624#64) (w (.GPR 8#5) 32768#64 s)

private theorem err_pc (s : ArmState) (pc : BitVec 64) :
    r .ERR (w .PC pc s) = r .ERR s :=
  r_of_w_different (by decide)

private theorem err_gpr (s : ArmState) (reg : BitVec 5) (value : BitVec 64) :
    r .ERR (w (.GPR reg) value s) = r .ERR s :=
  r_of_w_different (by intro equal; cases equal)

theorem initial_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3528#64) : run 1 s = initialResult s base := by
  have follows : Follows base [p3528] s := ⟨error, pc, trivial⟩
  rw [show 1 = [p3528].length by rfl, runs _ s base code follows]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, p3528, Result.p3924, Op.effect, exec_inst, initialResult,
      state_simp_rules, bitvec_rules, minimal_theory, pc, BitVec.add_assoc, NatExact.gpr_w_pc]

theorem statusReady_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3620#64) : run 1 s = statusReady s base := by
  have follows : Follows base [p3620] s := ⟨error, pc, trivial⟩
  rw [show 1 = [p3620].length by rfl, runs _ s base code follows]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, p3620, Op.effect, exec_inst, statusReady,
      state_simp_rules, bitvec_rules, minimal_theory, pc, BitVec.add_assoc, NatExact.gpr_w_pc]

theorem suffix_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3720#64) : run 3 s = statusResult s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p3720, Result.p3896, Result.p3900] s := by
    simp (config := {decide := true, instances := true})
      [Follows, p3720, Result.p3896, Result.p3900, Op.effect, exec_inst,
        state_simp_rules, bitvec_rules, minimal_theory, error, pc, BitVec.add_assoc]
  rw [show 3 = [p3720, Result.p3896, Result.p3900].length by rfl,
    runs _ s base code follows]
  simp (config := {decide := true, instances := true})
    [effect, p3720, Result.p3896, Result.p3900, Op.effect, exec_inst, statusResult,
      state_simp_rules, bitvec_rules, minimal_theory, pc, BitVec.add_assoc, NatExact.store_w]

@[irreducible] def finalResult (s : ArmState) (base : BitVec 64) : ArmState :=
  statusResult (expectedResult (actualResult (statusReady
    (headerResult (reservedResult (initialResult s base) base) base) base) base) base) base

theorem executes (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3528#64) : run 51 s = finalResult s base := by
  let a := initialResult s base
  let b := reservedResult a base
  let c := headerResult b base
  let d := statusReady c base
  let e := actualResult d base
  let f := expectedResult e base
  have ap : a.program = s.program := by simp [a, initialResult, state_simp_rules]
  have ae : read_err a = .None := by simpa [a, initialResult, state_simp_rules] using error
  have aa : CheckSPAlignment a := by
    simpa [a, initialResult, CheckSPAlignment, state_simp_rules] using aligned
  have ra : run 1 s = a := initial_run s base code error pc
  have rb : run 12 a = b := reserved_run a base (code.congr ap) ae aa
    (by simp [a, initialResult, state_simp_rules])
  have bp : b.program = s.program := by simp [b, reservedResult, ap, state_simp_rules]
  have be : read_err b = .None := by
    simpa only [b, reservedResult, read_err, err_pc] using
      (Lower.error .wrongReserved a base).trans ae
  have ba : CheckSPAlignment b := by
    simpa [b, reservedResult, CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
      state_simp_rules] using aa
  have rc : run 10 b = c := header_run b base (code.congr bp) be ba
    (by simp [b, reservedResult, state_simp_rules])
  have cp : c.program = s.program := by simp [c, headerResult, bp, state_simp_rules]
  have ce : read_err c = .None := by
    simpa only [c, headerResult, read_err, err_pc] using
      (Lower.error .wrongHeader b base).trans be
  have ca : CheckSPAlignment c := by
    simpa [c, headerResult, CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
      state_simp_rules] using ba
  have rd : run 1 c = d := statusReady_run c base (code.congr cp) ce
    (by simp [c, headerResult, state_simp_rules])
  have dp : d.program = s.program := by simp [d, statusReady, cp, state_simp_rules]
  have de : read_err d = .None := by
    simpa only [d, statusReady, read_err, err_pc, err_gpr] using ce
  have da : CheckSPAlignment d := by
    simpa [d, statusReady, CheckSPAlignment, state_simp_rules] using ca
  have re : run 12 d = e := actual_run d base (code.congr dp) de da
    (by simp [d, statusReady, state_simp_rules])
  have ep : e.program = s.program := by simp [e, actualResult, dp, state_simp_rules]
  have ee : read_err e = .None := by
    simpa only [e, actualResult, read_err, err_pc] using
      (Lower.error .wrongActual d base).trans de
  have ea : CheckSPAlignment e := by
    simpa [e, actualResult, CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
      state_simp_rules] using da
  have rf : run 12 e = f := expected_run e base (code.congr ep) ee ea
    (by simp [e, actualResult, state_simp_rules])
  have fp : f.program = s.program := by simp [f, expectedResult, ep, state_simp_rules]
  have fe : read_err f = .None := by
    simpa only [f, expectedResult, read_err, err_pc] using
      (Lower.error .wrongExpected e base).trans ee
  have rg : run 3 f = statusResult f base := suffix_run f base (code.congr fp) fe
    (by simp [f, expectedResult, state_simp_rules])
  rw [show 51 = 1 + 12 + 10 + 1 + 12 + 12 + 3 by decide,
    run_plus, run_plus, run_plus, run_plus, run_plus, run_plus, ra, rb, rc, rd, re, rf, rg]
  simp only [finalResult, a, b, c, d, e, f]

@[simp] theorem final_program (s : ArmState) (base : BitVec 64) :
    (finalResult s base).program = s.program := by
  simp [finalResult, expectedResult, actualResult, statusReady,
    headerResult, reservedResult, initialResult, state_simp_rules]

@[simp] theorem final_error (s : ArmState) (base : BitVec 64) :
    read_err (finalResult s base) = read_err s := by
  have lowerError (kind : Lower) (u : ArmState) :
      r .ERR (kind.result u base) = r .ERR u := Lower.error kind u base
  have endError (u : ArmState) :
      r .ERR (statusResult u base) = r .ERR u := status_error u base
  simp only [finalResult, expectedResult, actualResult, statusReady, headerResult,
    reservedResult, initialResult, read_err, err_pc, err_gpr, lowerError, endError]

@[simp] theorem final_pc (s : ArmState) (base : BitVec 64) :
    read_pc (finalResult s base) = base + 4116#64 := by
  simp [finalResult]

@[simp] theorem final_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (finalResult s base) = r (.GPR 31#5) s := by
  simp [finalResult, expectedResult, actualResult, statusReady,
    headerResult, reservedResult, initialResult, state_simp_rules]

theorem final_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (eight : reg ≠ 8#5) (nine : reg ≠ 9#5) (ten : reg ≠ 10#5) :
    r (.GPR reg) (finalResult s base) = r (.GPR reg) s := by
  simp [finalResult, expectedResult, actualResult, statusReady, headerResult, reservedResult,
    initialResult, Lower.register, Lower.tmp, eight, nine, ten,
    NatExact.r_gpr_w, state_simp_rules]

@[simp] theorem final_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (finalResult s base) = r (.SFP reg) s := by
  simp [finalResult, expectedResult, actualResult, statusReady,
    headerResult, reservedResult, initialResult, state_simp_rules]

end SszArm.Measure.Bits.Scratch
