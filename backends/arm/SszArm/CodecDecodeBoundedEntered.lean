import SszArm.CodecDecodeBoundedInvariantCompare
import SszArm.CodecDecodeBoundedPreservation

namespace SszArm.Codec.Decode.Bounded

open SszNative
open Delimited (MemoryFrame)

@[irreducible] def entered (s : ArmState) (base : BitVec 64) : ArmState :=
  tagRead (prologue s base) base

@[simp] theorem entered_program (s : ArmState) (base : BitVec 64) :
    (entered s base).program = s.program := by simp [entered, tagRead, state_simp_rules]

@[simp] theorem entered_error (s : ArmState) (base : BitVec 64) :
    read_err (entered s base) = read_err s := by simp [entered, tagRead, state_simp_rules]

@[simp] theorem entered_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (entered s base) = bodySP s := by simp [entered, tagRead, state_simp_rules]

@[simp] theorem entered_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (eight : reg ≠ 8#5) (nineteen : reg ≠ 19#5) (stack : reg ≠ 31#5) :
    r (.GPR reg) (entered s base) = r (.GPR reg) s := by
  simp [entered, tagRead, state_simp_rules, eight, nineteen, stack]

@[simp] theorem entered_output (s : ArmState) (base : BitVec 64) :
    r (.GPR 19#5) (entered s base) = r (.GPR 0#5) s := by
  simp [entered, tagRead, state_simp_rules]

@[simp] theorem entered_memory (s : ArmState) (base : BitVec 64) :
    (entered s base).mem = (prologue s base).mem := by simp [entered, tagRead, state_simp_rules]

theorem entered_run (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    run 8 s = entered s base := by
  have first := prologue_run s base code error aligned pc
  have nextCode : CodeAt (prologue s base) base := by
    simpa only [CodeAt, Linked.Bounded.CodeAt, Linked.WordsAt, prologue_program] using code
  rw [show 8 = 4 + 4 by decide, run_plus, first]
  simpa only [entered] using tag_run (prologue s base) base nextCode
    (by simpa using error) (prologue_aligned s base aligned) (by simp [pc])

theorem entered_frame (s : ArmState) (base : BitVec 64)
    (low : 64 ≤ (r (.GPR 31#5) s).toNat) : MemoryFrame (stackWrites s) s (entered s base) := by
  intro address outside
  rw [entered_memory]
  exact prologue_frame s base low address outside

theorem entered_inputs (s : ArmState) (base : BitVec 64) (limit : Option NatOperand)
    (actual : NatOperand) (owned : Owned s limit actual) :
    LimitAt (entered s base) (r (.GPR 1#5) (entered s base)) limit ∧
    ActualAt (entered s base) (r (.GPR 2#5) (entered s base)) actual := by
  have frame : MemoryFrame (localWrites s) s (entered s base) :=
    (entered_frame s base owned.stackBound).weaken (by
      intro span member; simp only [localWrites, List.mem_cons]; exact Or.inr member)
  simpa only [entered_register s base 1#5 (by decide) (by decide) (by decide),
    entered_register s base 2#5 (by decide) (by decide) (by decide)] using inputs_preserved owned frame

theorem entered_aligned (s : ArmState) (base : BitVec 64) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (entered s base) :=
  CheckSPAlignment_of_r_sp_aligned (entered_sp s base)
    (aligned_sub48 _ (BoolCodec.stack_aligned s aligned))

theorem entered_active (s : ArmState) (base : BitVec 64)
    (low : 64 ≤ (r (.GPR 31#5) s).toNat) (error : read_err s = .None) :
    Activation s (entered s base) := by
  simpa only [entered] using activation_entered s base low error

theorem entered_lowering (s : ArmState) (base : BitVec 64)
    (low : 64 ≤ (r (.GPR 31#5) s).toNat) (operand : NatOperand)
    (owned : NatDivision.OperandOwned (localWrites s) operand) :
    NatDivision.OperandOwned (SszArm.Measure.Helpers.loweringWrites (entered s base)) operand := by
  have address : (r (.GPR 31#5) (entered s base)).toNat - 16 =
      (r (.GPR 31#5) s).toNat - 64 := by
    rw [entered_sp]
    simp only [bodySP]
    bv_omega
  cases operand with
  | small word => trivial
  | large pointer words =>
    apply Delimited.Protected.weaken_emit owned
    intro span member
    have same : span = ((r (.GPR 31#5) s).toNat - 64, 16) := by
      simpa only [SszArm.Measure.Helpers.loweringWrites, address, List.mem_cons,
        List.not_mem_nil, or_false] using member
    subst span
    simp [localWrites, stackWrites]

end SszArm.Codec.Decode.Bounded
