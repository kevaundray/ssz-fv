import SszArm.NatMulWordHighFrame
import SszArm.NatMulWordStore
import SszArm.NatMulWordRoundTail

namespace SszArm.NatMulWord

def roundLow (s : ArmState) (base : BitVec 64) : ArmState := Op.p632.effect base s

def roundHigh (s : ArmState) (base : BitVec 64) : ArmState :=
  highCompleted .loop (roundLow s base) base

def roundAdded (s : ArmState) (base : BitVec 64) : ArmState :=
  Op.p748.effect base (roundHigh s base)

def roundStored (s : ArmState) (base : BitVec 64) : ArmState :=
  block base storeOps (roundAdded s base)

def roundCompleted (s : ArmState) (base : BitVec 64) : ArmState :=
  roundTail (roundStored s base) base

def roundFuel (s : ArmState) (base : BitVec 64) : Nat :=
  38 + (roundTailOps (roundStored s base)).length

theorem round_low_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 632#64) : run 1 s = roundLow s base := by
  have single := step s base .p632 code pc error aligned
  simpa only [run, roundLow] using single

@[simp] theorem high_completed_program (site : HighSite) (s : ArmState) (base : BitVec 64) :
    (highCompleted site s base).program = s.program := by
  simp only [highCompleted, block_program]

@[simp] theorem high_completed_error (site : HighSite) (s : ArmState) (base : BitVec 64) :
    read_err (highCompleted site s base) = read_err s := by
  simp only [highCompleted, block_error]

theorem high_completed_aligned (site : HighSite) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (highCompleted site s base) := by
  exact block_aligned _ _ _ (block_aligned _ _ _ (block_aligned _ _ _ aligned))

@[simp] theorem round_low_pc (s : ArmState) (base : BitVec 64) :
    read_pc (roundLow s base) = read_pc s + 4#64 := by
  simp [roundLow, Op.effect, put, next, state_simp_rules]

@[simp] theorem round_high_pc (s : ArmState) (base : BitVec 64) :
    read_pc (roundHigh s base) = read_pc s + 116#64 := by
  rw [roundHigh, high_completed_pc, round_low_pc]
  simp [BitVec.add_assoc]

@[simp] theorem round_added_pc (s : ArmState) (base : BitVec 64) :
    read_pc (roundAdded s base) = read_pc s + 120#64 := by
  simp [roundAdded, Op.effect, put, next, state_simp_rules, round_high_pc, BitVec.add_assoc]

@[simp] theorem round_stored_pc (s : ArmState) (base : BitVec 64) :
    read_pc (roundStored s base) = read_pc s + 152#64 := by
  have storePC (t : ArmState) : read_pc (block base storeOps t) = read_pc t + 32#64 := by
    simp [storeOps, block, Op.effect, put, next, state_simp_rules, BitVec.add_assoc]
  rw [roundStored, storePC, round_added_pc]
  simp [BitVec.add_assoc]

/-- Every real instruction of a noninitial multiplication round, including
both paths of the carry increment and the true loop-exit branch. -/
theorem round_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 632#64) :
    run (roundFuel s base) s = roundCompleted s base := by
  have lowCode : CodeAt (roundLow s base) base := by
    simpa only [CodeAt, roundLow, Op.program] using code
  have lowError : read_err (roundLow s base) = .None := by
    simpa only [roundLow, Op.error] using error
  have lowAligned := Op.aligned .p632 base s aligned
  have lowPC : read_pc (roundLow s base) = base + 636#64 := by
    rw [round_low_pc, pc]; simp [BitVec.add_assoc]
  have highCode : CodeAt (roundHigh s base) base := by
    simpa only [CodeAt, roundHigh, high_completed_program] using lowCode
  have highError : read_err (roundHigh s base) = .None := by
    simpa only [roundHigh, high_completed_error] using lowError
  have highAligned := high_completed_aligned .loop (roundLow s base) base lowAligned
  have highPC : read_pc (roundHigh s base) = base + 748#64 := by
    rw [round_high_pc, pc]; simp [BitVec.add_assoc]
  have addRun : run 1 (roundHigh s base) = roundAdded s base := by
    simpa only [run, roundAdded] using
      step (roundHigh s base) base .p748 highCode highPC highError highAligned
  have addedCode : CodeAt (roundAdded s base) base := by
    simpa only [CodeAt, roundAdded, Op.program] using highCode
  have addedError : read_err (roundAdded s base) = .None := by
    simpa only [roundAdded, Op.error] using highError
  have addedAligned := Op.aligned .p748 base (roundHigh s base) highAligned
  have addedPC : read_pc (roundAdded s base) = base + 752#64 := by
    rw [round_added_pc, pc]; simp [BitVec.add_assoc]
  have storedCode : CodeAt (roundStored s base) base := by
    simpa only [CodeAt, roundStored, block_program] using addedCode
  have storedError : read_err (roundStored s base) = .None := by
    simpa only [roundStored, block_error] using addedError
  have storedAligned := block_aligned base storeOps (roundAdded s base) addedAligned
  have storedPC : read_pc (roundStored s base) = base + 784#64 := by
    rw [round_stored_pc, pc]; simp [BitVec.add_assoc]
  have amount : roundFuel s base =
      1 + (28 + (1 + (8 + (roundTailOps (roundStored s base)).length))) := by
    unfold roundFuel
    omega
  rw [amount, run_plus, round_low_run s base code error aligned pc,
    run_plus, high_run .loop (roundLow s base) base lowCode lowError lowAligned lowPC,
    run_plus, addRun, run_plus,
    store_run (roundAdded s base) base addedCode addedError addedAligned addedPC,
    round_tail_run (roundStored s base) base storedCode storedError storedAligned storedPC]
  rfl

end SszArm.NatMulWord
