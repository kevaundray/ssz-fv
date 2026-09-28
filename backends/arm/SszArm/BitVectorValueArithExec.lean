import SszArm.BitVectorValueLoadExec

namespace SszArm.BitVector.ValueTail

open Block

inductive ArithStage where
  | test | roundZero | roundOne | add | noCarry | carry | guard
  deriving DecidableEq

def ArithStage.ops : ArithStage → List Op
  | .test => [p6664, p6668, p6672]
  | .roundZero => [p6676, p6680]
  | .roundOne => [p6684]
  | .add => [p6688, p6692]
  | .noCarry => [p6696, p6700]
  | .carry => [p6704]
  | .guard => [p6708, p6712, p6716]

def ArithStage.start : ArithStage → Nat
  | .test => 6664
  | .roundZero => 6676
  | .roundOne => 6684
  | .add => 6688
  | .noCarry => 6696
  | .carry => 6704
  | .guard => 6708

@[irreducible] def ArithStage.result (stage : ArithStage) (s : ArmState)
    (base : BitVec 64) : ArmState :=
  match stage with
  | .test =>
    let rem := r (.GPR 9#5) s &&& 7#64
    w .PC (if rem = 0#64 then base + 6676#64 else base + 6684#64)
      (w (.GPR 11#5) (shift3 (r (.GPR 8#5) s))
        (write_pstate (DPI.update_logical_imm_pstate rem) s))
  | .roundZero => w .PC (base + 6688#64) (w (.GPR 12#5) 0#64 s)
  | .roundOne => w .PC (base + 6688#64) (w (.GPR 12#5) 1#64 s)
  | .add =>
    let sum := AddWithCarry (r (.GPR 10#5) s) (r (.GPR 12#5) s) 0#1
    w .PC (if sum.2.c = 1#1 then base + 6704#64 else base + 6696#64)
      (w (.GPR 10#5) (r (.GPR 10#5) s + r (.GPR 12#5) s)
        (write_pstate sum.2 s))
  | .noCarry => w .PC (base + 6708#64) s
  | .carry => w .PC (base + 6708#64) (w (.GPR 11#5) (r (.GPR 11#5) s + 1#64) s)
  | .guard =>
    let mismatch := (r (.GPR 10#5) s ^^^ r (.GPR 20#5) s) ||| r (.GPR 11#5) s
    w .PC (if mismatch = 0#64 then base + 6720#64 else base + 7932#64)
      (w (.GPR 10#5) mismatch s)

private theorem arith_follows (stage : ArithStage) (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) :
    Follows base stage.ops s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  cases stage <;>
    simp (config := {decide := true, instances := true})
      [Follows, ArithStage.ops, ArithStage.start, p6664, p6668, p6672, p6676, p6680,
       p6684, p6688, p6692, p6696, p6700, p6704, p6708, p6712, p6716,
       Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       error, pc, BitVec.add_assoc]

private theorem arith_test_summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 6664#64) :
    effect ArithStage.test.ops s = ArithStage.test.result s base := by
  change r .PC s = _ at pc
  by_cases zero : r (.GPR 9#5) s &&& 7#64 = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [effect, ArithStage.ops, ArithStage.result, shift3, p6664, p6668, p6672,
       Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       DPI.update_logical_imm_pstate, zero_flag_spec, zero, pc, BitVec.add_assoc, and_ones] <;>
    simp only [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem zero_move32 : BitVec.partInstall 0 16 0#16 0#32 = 0#32 := by decide

private theorem arith_zero_summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 6676#64) :
    effect ArithStage.roundZero.ops s = ArithStage.roundZero.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, ArithStage.ops, ArithStage.result, p6676, p6680,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, zero_move32] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem arith_one_summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 6684#64) :
    effect ArithStage.roundOne.ops s = ArithStage.roundOne.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, ArithStage.ops, ArithStage.result, p6684,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc]

private theorem arith_add_summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 6688#64) :
    effect ArithStage.add.ops s = ArithStage.add.result s base := by
  change r .PC s = _ at pc
  by_cases carry : (AddWithCarry (r (.GPR 10#5) s) (r (.GPR 12#5) s) 0#1).2.c = 1#1 <;>
    simp (config := {decide := true, instances := true})
      [effect, ArithStage.ops, ArithStage.result, p6688, p6692,
       Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pc, BitVec.add_assoc, carry] <;>
    simp only [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem arith_no_carry_summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 6696#64) :
    effect ArithStage.noCarry.ops s = ArithStage.noCarry.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, ArithStage.ops, ArithStage.result, p6696, p6700,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr, r, read_base_gpr, store_write_irrelevant]

private theorem arith_carry_summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 6704#64) :
    effect ArithStage.carry.ops s = ArithStage.carry.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, ArithStage.ops, ArithStage.result, p6704,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem arith_guard_summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 6708#64) :
    effect ArithStage.guard.ops s = ArithStage.guard.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, ArithStage.ops, ArithStage.result, p6708, p6712, p6716,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc]
  simp only [w, write_base_pc, write_base_gpr, store_write_over_write_shadow]
  by_cases same : r (.GPR 10#5) s = r (.GPR 20#5) s <;>
    by_cases zero : r (.GPR 11#5) s = 0#64 <;> simp [same, zero]

theorem arith_executes (stage : ArithStage) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) :
    run stage.ops.length s = stage.result s base := by
  rw [runs stage.ops s base code (arith_follows stage s base error pc)]
  cases stage with
  | test => exact arith_test_summary s base pc
  | roundZero => exact arith_zero_summary s base pc
  | roundOne => exact arith_one_summary s base pc
  | add => exact arith_add_summary s base pc
  | noCarry => exact arith_no_carry_summary s base pc
  | carry => exact arith_carry_summary s base pc
  | guard => exact arith_guard_summary s base pc

end SszArm.BitVector.ValueTail
