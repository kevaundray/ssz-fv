import SszArm.MeasureBitsWidthPrepareStages

namespace SszArm.Measure.Bits.Width

open Result

def prepareOps : List Op := [p1876, p1880, p1884, p1888, p1892, p1896]

@[irreducible] def prepareResult (s : ArmState) (base : BitVec 64) : ArmState :=
  let flags := (AddWithCarry (r (.GPR 8#5) s) 1#64 0#1).2
  w .PC (if flags.c = 1#1 then base + 1908#64 else base + 1900#64)
    (write_pstate flags (w (.GPR 2#5) (r (.GPR 8#5) s + 1#64)
      (w (.GPR 23#5) (r (.GPR 31#5) s + 120#64)
        (w (.GPR 4#5) (r (.GPR 20#5) s)
          (w (.GPR 0#5) (r (.GPR 31#5) s + 120#64)
            (w (.GPR 9#5) (r (.GPR 25#5) s >>> (3 : Nat)) s))))))

theorem prepare_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 1876#64) : run 6 s = prepareResult s base := by
  let flags := (AddWithCarry (r (.GPR 8#5) s) 1#64 0#1).2
  have arguments := prepareArguments_run s base code error pc
  have added : stepi (prepareArguments s base) = prepareMarked s base flags :=
    (Op.step p1892 _ base (code.congr (prepareArguments_program s base))
      ((prepareArguments_error s base).trans error) (prepareArguments_pc s base)).trans
        (prepareArguments_add s base)
  have branched : stepi (prepareMarked s base flags) = prepareBranched s base flags :=
    (Op.step p1896 _ base (code.congr (prepareMarked_program s base flags))
      ((prepareMarked_error s base flags).trans error) (prepareMarked_pc s base flags)).trans
        (prepareMarked_branch s base flags)
  rw [show 6 = 4 + 2 from rfl, run_plus, arguments,
    prepare_two_steps _ _ _ added branched]
  simp only [prepareBranched, prepareResult, prepareRegisters]
  rfl

@[irreducible] def finishResult (carry : Bool) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 1912#64)
    (w (.GPR 3#5) (if carry then r (.GPR 9#5) s + 1#64 else r (.GPR 9#5) s) s)

def finishOps : Bool → List Op
  | false => [p1900, p1904]
  | true => [p1908]

theorem finish_run (carry : Bool) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + (if carry then 1908#64 else 1900#64)) :
    run (finishOps carry).length s = finishResult carry s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base (finishOps carry) s := by
    cases carry <;>
      simp (config := {decide := true, instances := true})
        [Follows, finishOps, prepare1900_effect, prepare1904_effect, prepare1908_effect,
          state_simp_rules, error, pc, BitVec.add_assoc]
    all_goals simp [p1900, p1904, p1908]
  rw [runs _ s base code follows]
  cases carry <;>
    simp (config := {decide := true, instances := true})
      [finishResult, effect, finishOps, prepare1900_effect, prepare1904_effect,
        prepare1908_effect, state_simp_rules, NatExact.gpr_w_pc, pc, BitVec.add_assoc]

end SszArm.Measure.Bits.Width
