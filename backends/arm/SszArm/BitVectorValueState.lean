import SszArm.BitVectorValueArithExec
import SszArm.BitVectorValueStoreExec

namespace SszArm.BitVector.ValueTail

@[simp] theorem load_program (stage : LoadStage) (s : ArmState) (base : BitVec 64) :
    (stage.result s base).program = s.program := by
  cases stage <;> simp [LoadStage.result, state_simp_rules]

@[simp] theorem load_error (stage : LoadStage) (s : ArmState) (base : BitVec 64) :
    read_err (stage.result s base) = read_err s := by
  cases stage <;> simp [LoadStage.result, state_simp_rules]

theorem load_aligned (stage : LoadStage) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (stage.result s base) := by
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have upper := BoolCodec.aligned_add16 _ stack
  cases stage <;>
    simp_all [LoadStage.result, CheckSPAlignment, state_simp_rules, bitvec_rules, minimal_theory]

@[simp] theorem store_program (stage : StoreStage) (s : ArmState) (base : BitVec 64) :
    (stage.result s base).program = s.program := by
  cases stage <;> simp [StoreStage.result, state_simp_rules]

@[simp] theorem store_error (stage : StoreStage) (s : ArmState) (base : BitVec 64) :
    read_err (stage.result s base) = read_err s := by
  cases stage <;> simp [StoreStage.result, state_simp_rules]

theorem store_aligned (stage : StoreStage) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (stage.result s base) := by
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have upper := BoolCodec.aligned_add16 _ stack
  cases stage <;>
    simp_all [StoreStage.result, CheckSPAlignment, state_simp_rules, bitvec_rules, minimal_theory]

@[simp] theorem arith_program (stage : ArithStage) (s : ArmState) (base : BitVec 64) :
    (stage.result s base).program = s.program := by
  cases stage <;> simp [ArithStage.result, state_simp_rules]

@[simp] theorem arith_error (stage : ArithStage) (s : ArmState) (base : BitVec 64) :
    read_err (stage.result s base) = read_err s := by
  cases stage <;> simp [ArithStage.result, state_simp_rules]

@[simp] theorem arith_sp (stage : ArithStage) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (stage.result s base) = r (.GPR 31#5) s := by
  cases stage <;> simp [ArithStage.result, state_simp_rules]

@[simp] theorem arith_mem (stage : ArithStage) (s : ArmState) (base : BitVec 64) :
    (stage.result s base).mem = s.mem := by
  cases stage <;> simp [ArithStage.result, state_simp_rules, ArmState.mem_w_eq_mem]

@[simp] theorem arith_aligned (stage : ArithStage) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (stage.result s base) := by
  simpa only [CheckSPAlignment, state_simp_rules, arith_sp] using aligned

theorem load_register (stage : LoadStage) (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (r8 : reg ≠ 8#5) (r9 : reg ≠ 9#5) (r10 : reg ≠ 10#5)
    (r11 : reg ≠ 11#5) (rsp : reg ≠ 31#5) :
    r (.GPR reg) (stage.result s base) = r (.GPR reg) s := by
  cases stage <;> simp [LoadStage.result, state_simp_rules, r8, r9, r10, r11, rsp]

theorem store_register (stage : StoreStage) (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (r9 : reg ≠ 9#5) (r10 : reg ≠ 10#5) (rsp : reg ≠ 31#5) :
    r (.GPR reg) (stage.result s base) = r (.GPR reg) s := by
  cases stage <;> simp [StoreStage.result, state_simp_rules, r9, r10, rsp]

theorem arith_register (stage : ArithStage) (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (r10 : reg ≠ 10#5) (r11 : reg ≠ 11#5) (r12 : reg ≠ 12#5) :
    r (.GPR reg) (stage.result s base) = r (.GPR reg) s := by
  cases stage <;> simp [ArithStage.result, state_simp_rules, r10, r11, r12]

@[simp] theorem load_vector (stage : LoadStage) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (stage.result s base) = r (.SFP reg) s := by
  cases stage <;> simp [LoadStage.result, state_simp_rules]

@[simp] theorem store_vector (stage : StoreStage) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (stage.result s base) = r (.SFP reg) s := by
  cases stage <;> simp [StoreStage.result, state_simp_rules]

@[simp] theorem arith_vector (stage : ArithStage) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (stage.result s base) = r (.SFP reg) s := by
  cases stage <;> simp [ArithStage.result, state_simp_rules]

end SszArm.BitVector.ValueTail
