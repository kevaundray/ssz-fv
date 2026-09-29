import SszArm.IndicesGeneralizedIndexEmptyOps
import SszArm.BoolAlignment

namespace SszArm.Indices.GeneralizedIndex.Empty

open Dispatch.Block (next put save branch)

private theorem aligned_sub224 (sp : BitVec 64) (aligned : Aligned sp 4) :
    Aligned (sp - 224#64) 4 := by
  have a := BoolCodec.aligned_sub32 sp aligned
  have b := BoolCodec.aligned_sub32 _ a
  have c := BoolCodec.aligned_sub32 _ b
  have d := BoolCodec.aligned_sub32 _ c
  have e := BoolCodec.aligned_sub32 _ d
  have f := BoolCodec.aligned_sub32 _ e
  have g := BoolCodec.aligned_sub32 _ f
  simpa (config := {decide := true}) only [BitVec.sub_eq_add_neg, BitVec.add_assoc] using g

private theorem aligned_add224 (sp : BitVec 64) (aligned : Aligned sp 4) :
    Aligned (sp + 224#64) 4 := by
  have a := BoolCodec.aligned_add32 sp aligned
  have b := BoolCodec.aligned_add32 _ a
  have c := BoolCodec.aligned_add32 _ b
  have d := BoolCodec.aligned_add32 _ c
  have e := BoolCodec.aligned_add32 _ d
  have f := BoolCodec.aligned_add32 _ e
  have g := BoolCodec.aligned_add32 _ f
  simpa (config := {decide := true}) only [BitVec.add_assoc] using g

def Op.stackValue : Op → BitVec 64 → BitVec 64
  | .p0, sp => sp - 224#64
  | .p136, sp | .p176, sp => sp - 16#64
  | .p172, sp | .p212, sp => sp + 16#64
  | .p236, sp => sp + 224#64
  | _, sp => sp

@[simp] theorem Op.sp (op : Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = op.stackValue (r (.GPR 31#5) s) := by
  cases op <;> simp [Op.effect, Op.stackValue, next, put, save, branch, loadPair,
    state_simp_rules]

theorem Op.aligned (op : Op) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect s) := by
  apply CheckSPAlignment_of_r_sp_aligned (op.sp s)
  have original := BoolCodec.stack_aligned s aligned
  cases op <;> simp only [Op.stackValue]
  all_goals first
    | exact original
    | exact aligned_sub224 _ original
    | exact aligned_add224 _ original
    | exact BoolCodec.aligned_sub16 _ original
    | exact BoolCodec.aligned_add16 _ original

def ControlFlow (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      ControlFlow base ops (op.effect s)

theorem follows_of_control (ops : List Op) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (control : ControlFlow base ops s) : Follows base ops s := by
  induction ops generalizing s with
  | nil => trivial
  | cons op ops ih => exact ⟨aligned, control.1, ih _ (op.aligned s aligned) control.2⟩

def emptyOps : List Op := [
  .p0, .p4, .p8, .p12, .p16, .p20, .p24, .p28,
  .p132, .p136, .p140, .p144, .p148, .p152, .p156, .p160,
  .p164, .p168, .p172, .p176, .p180, .p184, .p188, .p192,
  .p196, .p200, .p204, .p208, .p212, .p216, .p220, .p224,
  .p228, .p232, .p236, .p240]

/-- This is the complete real empty-path execution, not a callee oracle.
The physical separation obligations needed to recover the original saved values
belong to the ownership-to-result theorem, not to this instruction equation. -/
@[irreducible] def emptyReturned (s : ArmState) : ArmState := block emptyOps s

theorem empty_control (s : ArmState) (base : BitVec 64)
    (entry : read_pc s = base) (empty : r (.GPR 3#5) s = 0#64) :
    ControlFlow base emptyOps s := by
  change r .PC s = _ at entry
  simp (config := {decide := true}) [ControlFlow, emptyOps, Op.row, Op.effect,
    next, put, save, branch, loadPair, state_simp_rules, entry, empty,
    BitVec.add_assoc]

theorem empty_run (s : ArmState) (base : BitVec 64)
    (code : Linked.GeneralizedIndex.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (entry : read_pc s = base)
    (empty : r (.GPR 3#5) s = 0#64) : run 36 s = emptyReturned s := by
  exact block_run emptyOps s base code error
    (follows_of_control emptyOps s base aligned (empty_control s base entry empty))

@[simp] theorem emptyReturned_program (s : ArmState) :
    (emptyReturned s).program = s.program := by
  simp [emptyReturned]

@[simp] theorem emptyReturned_error (s : ArmState) :
    read_err (emptyReturned s) = read_err s := by
  simp [emptyReturned]

@[simp] theorem emptyReturned_sp (s : ArmState) :
    r (.GPR 31#5) (emptyReturned s) = r (.GPR 31#5) s := by
  simp [emptyReturned, emptyOps, block, Op.effect, next, put, save, branch,
    loadPair, state_simp_rules, BitVec.sub_eq_add_neg, BitVec.add_assoc]

@[simp] theorem emptyReturned_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (emptyReturned s) = r (.SFP reg) s := by
  simp [emptyReturned]

end SszArm.Indices.GeneralizedIndex.Empty
