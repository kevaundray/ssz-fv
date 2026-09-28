import SszArm.BitVectorValueState
import SszArm.BitVectorValueArithmetic

namespace SszArm.BitVector.ValueTail

open Block

def roundStage (s : ArmState) : ArithStage :=
  if r (.GPR 9#5) s &&& 7#64 = 0#64 then .roundZero else .roundOne

def roundedState (s : ArmState) (base : BitVec 64) : ArmState :=
  (roundStage s).result (ArithStage.test.result s base) base

def roundFuel (s : ArmState) : Nat :=
  3 + (roundStage s).ops.length

theorem round_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 6664#64) :
    run (roundFuel s) s = roundedState s base := by
  have first := arith_executes .test s base code error pc
  have second := arith_executes (roundStage s) (ArithStage.test.result s base) base
    (by simpa only [CodeAt, arith_program] using code)
    (by simpa only [arith_error] using error)
    (by by_cases zero : r (.GPR 9#5) s &&& 7#64 = 0#64 <;>
        simp [roundStage, ArithStage.start, ArithStage.result, state_simp_rules, zero])
  change run 3 s = _ at first
  rw [roundFuel, run_plus, first, second]
  rfl

@[simp] theorem rounded_pc (s : ArmState) (base : BitVec 64) :
    read_pc (roundedState s base) = base + 6688#64 := by
  by_cases zero : r (.GPR 9#5) s &&& 7#64 = 0#64 <;>
    simp [roundedState, roundStage, ArithStage.result, state_simp_rules, zero]

@[simp] theorem rounded_low (s : ArmState) (base : BitVec 64) :
    r (.GPR 10#5) (roundedState s base) = r (.GPR 10#5) s := by
  by_cases zero : r (.GPR 9#5) s &&& 7#64 = 0#64 <;>
    simp [roundedState, roundStage, ArithStage.result, state_simp_rules, zero]

@[simp] theorem rounded_high (s : ArmState) (base : BitVec 64) :
    r (.GPR 11#5) (roundedState s base) = shift3 (r (.GPR 8#5) s) := by
  by_cases zero : r (.GPR 9#5) s &&& 7#64 = 0#64 <;>
    simp [roundedState, roundStage, ArithStage.result, state_simp_rules, zero]

@[simp] theorem rounded_bit (s : ArmState) (base : BitVec 64) :
    r (.GPR 12#5) (roundedState s base) = roundWord (r (.GPR 9#5) s) := by
  by_cases zero : r (.GPR 9#5) s &&& 7#64 = 0#64 <;>
    simp [roundedState, roundStage, roundWord, ArithStage.result, state_simp_rules, zero]

def guardResult (s : ArmState) (base : BitVec 64) : ArmState :=
  ArithStage.guard.result
    (ArithStage.noCarry.result (ArithStage.add.result (roundedState s base) base) base) base

/-- Scope success supplies this numeric premise through shared scope_narrows;
the proof does not assume either native guard or carry branch outcome. -/
theorem guard_run (s : ArmState) (base : BitVec 64) (count : BitVec 128)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 6664#64)
    (low : r (.GPR 9#5) s = countLow count)
    (high : r (.GPR 8#5) s = countHigh count)
    (quotient : r (.GPR 10#5) s = quotientWord (countLow count) (countHigh count))
    (scope : (r (.GPR 20#5) s).toNat = (count.toNat + 7) / 8) :
    run (roundFuel s + (2 + (2 + 3))) s = guardResult s base := by
  have facts := scope_registers count (r (.GPR 20#5) s) scope
  have first := round_run s base code error pc
  have added := arith_executes .add (roundedState s base) base
    (by simpa only [roundedState, CodeAt, arith_program] using code)
    (by simpa only [roundedState, arith_error] using error)
    (rounded_pc s base)
  have next := arith_executes .noCarry (ArithStage.add.result (roundedState s base) base) base
    (by simpa only [roundedState, CodeAt, arith_program] using code)
    (by simpa only [roundedState, arith_error] using error)
    (by simp [ArithStage.result, ArithStage.start, state_simp_rules,
      rounded_low, rounded_bit, low, quotient, facts.2.2])
  have last := arith_executes .guard
    (ArithStage.noCarry.result (ArithStage.add.result (roundedState s base) base) base) base
    (by simpa only [roundedState, CodeAt, arith_program] using code)
    (by simpa only [roundedState, arith_error] using error)
    (by simp [ArithStage.result, ArithStage.start, state_simp_rules])
  change run 2 (roundedState s base) = _ at added
  change run 2 (ArithStage.add.result (roundedState s base) base) = _ at next
  change run 3 _ = _ at last
  rw [run_plus, first, run_plus, added, run_plus, next, last]
  rfl

theorem guard_pc (s : ArmState) (base : BitVec 64) (count : BitVec 128)
    (low : r (.GPR 9#5) s = countLow count)
    (high : r (.GPR 8#5) s = countHigh count)
    (quotient : r (.GPR 10#5) s = quotientWord (countLow count) (countHigh count))
    (scope : (r (.GPR 20#5) s).toNat = (count.toNat + 7) / 8) :
    read_pc (guardResult s base) = base + 6720#64 := by
  have facts := scope_registers count (r (.GPR 20#5) s) scope
  have actual : r (.GPR 20#5) (roundedState s base) = r (.GPR 20#5) s := by
    simp only [roundedState, arith_register _ _ _ 20#5 (by decide) (by decide) (by decide)]
  simp [guardResult, ArithStage.result, state_simp_rules, rounded_low, rounded_high,
    rounded_bit, actual, low, high, quotient, facts.1, facts.2.1]

@[simp] theorem guard_program (s : ArmState) (base : BitVec 64) :
    (guardResult s base).program = s.program := by
  simp [guardResult, roundedState]

@[simp] theorem guard_error (s : ArmState) (base : BitVec 64) :
    read_err (guardResult s base) = read_err s := by
  simp [guardResult, roundedState]

@[simp] theorem guard_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (guardResult s base) = r (.GPR 31#5) s := by
  simp [guardResult, roundedState]

@[simp] theorem guard_mem (s : ArmState) (base : BitVec 64) :
    (guardResult s base).mem = s.mem := by
  simp [guardResult, roundedState]

theorem guard_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (r10 : reg ≠ 10#5) (r11 : reg ≠ 11#5) (r12 : reg ≠ 12#5) :
    r (.GPR reg) (guardResult s base) = r (.GPR reg) s := by
  simp only [guardResult, roundedState, arith_register _ _ _ _ r10 r11 r12]

@[simp] theorem guard_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (guardResult s base) = r (.SFP reg) s := by
  simp [guardResult, roundedState]

end SszArm.BitVector.ValueTail
