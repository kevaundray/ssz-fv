import SszArm.NatMulActivation
import SszArm.NatMulContract
import SszArm.BitVectorMemory

namespace SszArm.NatMul

open Delimited (MemoryFrame Protected)

def activationWrites (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 31#5) s).toNat - 96, 96)]

@[simp] theorem activated_program (s : ArmState) : (activated s).program = s.program := by
  simp [activated, saveMemory, state_simp_rules]

@[simp] theorem activated_error (s : ArmState) : read_err (activated s) = read_err s := by
  simp [activated, saveMemory, state_simp_rules]

@[simp] theorem activated_pc (s : ArmState) : read_pc (activated s) = read_pc s + 28#64 := by
  simp [activated, saveMemory, state_simp_rules]

@[simp] theorem activated_sp (s : ArmState) :
    r (.GPR 31#5) (activated s) = r (.GPR 31#5) s - 96#64 := by
  simp [activated, state_simp_rules]

theorem activated_registers (s : ArmState) (reg : BitVec 5) (notSP : reg ≠ 31#5) :
    r (.GPR reg) (activated s) = r (.GPR reg) s := by
  simp [activated, saveMemory, state_simp_rules, notSP]

theorem activated_vectors (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (activated s) = r (.SFP reg) s := by
  simp [activated, saveMemory, state_simp_rules]

theorem activation_frame (s : ArmState) (stack : 96 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame (activationWrites s) s (activated s) := by
  intro address outside
  have away := outside ((r (.GPR 31#5) s).toNat - 96, 96) (by simp [activationWrites])
  simp only [activated, ArmState.mem_w_eq_mem]
  simp (disch := bv_omega) [saveMemory, BoolCodec.write_mem_bytes_frame]

theorem activation_covered (s : ArmState) (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) :
    BitVector.Covers (writesFor s result) (activationWrites s) := by
  intro span member
  simp only [activationWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  subst span
  refine ⟨((r (.GPR 31#5) s).toNat - 144, 144), ?_, by omega, by omega⟩
  cases allocation : result.allocation <;> cases value : result.result <;>
    simp [writesFor, localWrites, allocation, value]

theorem activation_input {s : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right) :
    left.At (UintCodec.widthLoad (activated s)) ∧ right.At (UintCodec.widthLoad (activated s)) := by
  have frame := (activation_covered s (outcome s left right)).frame
    (activation_frame s (by have bound := owned.stackBound; omega))
  exact ⟨NatAdd.operand_at_preserved frame left owned.leftAt owned.leftOwned,
    NatAdd.operand_at_preserved frame right owned.rightAt owned.rightOwned⟩

end SszArm.NatMul
