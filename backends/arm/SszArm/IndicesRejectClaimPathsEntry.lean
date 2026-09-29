import SszArm.IndicesLinkedRejectClaimPaths
import SszArm.DispatchBlocks
import SszArm.BoolAlignment

namespace SszArm.Indices.RejectClaimPaths.Entry

open Dispatch.Block (next put save)

inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44 | p48 | p52
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xd10283ff#32)
  | .p4 => (4, 0xa9047bfd#32)
  | .p8 => (8, 0xa9056ffc#32)
  | .p12 => (12, 0xa90667fa#32)
  | .p16 => (16, 0xa9075ff8#32)
  | .p20 => (20, 0xa90857f6#32)
  | .p24 => (24, 0xa9094ff4#32)
  | .p28 => (28, 0xaa0303f6#32)
  | .p32 => (32, 0xaa0003f3#32)
  | .p36 => (36, 0x8b04106c#32)
  | .p40 => (40, 0x8b021039#32)
  | .p44 => (44, 0x5280080d#32)
  | .p48 => (48, 0x5280002e#32)
  | .p52 => (52, 0x9280001c#32)

def Op.effect : Op → ArmState → ArmState
  | .p0, s => put 31 (r (.GPR 31#5) s - 160#64) s
  | .p4, s => save 29 30 64#64 s
  | .p8, s => save 28 27 80#64 s
  | .p12, s => save 26 25 96#64 s
  | .p16, s => save 24 23 112#64 s
  | .p20, s => save 22 21 128#64 s
  | .p24, s => save 20 19 144#64 s
  | .p28, s => put 22 (r (.GPR 3#5) s) s
  | .p32, s => put 19 (r (.GPR 0#5) s) s
  | .p36, s => put 12 (r (.GPR 3#5) s + (r (.GPR 4#5) s <<< 4)) s
  | .p40, s => put 25 (r (.GPR 1#5) s + (r (.GPR 2#5) s <<< 4)) s
  | .p44, s => put 13 64#64 s
  | .p48, s => put 14 1#64 s
  | .p52, s => put 28 0xffffffffffffffff#64 s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := Linked.RejectClaimPaths.chunk0_codeAt code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, save, exec_inst, state_simp_rules, bitvec_rules,
        minimal_theory, aligned, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  all_goals first | rfl | exact w_of_w_commute (by decide)

@[simp] theorem Op.program (op : Op) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, save, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, save, state_simp_rules]

private theorem aligned_sub160 (sp : BitVec 64) (aligned : Aligned sp 4) :
    Aligned (sp - 160#64) 4 := by
  have a := BoolCodec.aligned_sub32 sp aligned
  have b := BoolCodec.aligned_sub32 _ a
  have c := BoolCodec.aligned_sub32 _ b
  have d := BoolCodec.aligned_sub32 _ c
  have e := BoolCodec.aligned_sub32 _ d
  simpa (config := {decide := true}) only [BitVec.sub_eq_add_neg, BitVec.add_assoc] using e

theorem Op.aligned (op : Op) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect s) := by
  cases op
  · apply CheckSPAlignment_of_r_sp_aligned
      (show r (.GPR 31#5) (Op.p0.effect s) = r (.GPR 31#5) s - 160#64 by
        simp [Op.effect, put, next, state_simp_rules])
    exact aligned_sub160 _ (BoolCodec.stack_aligned s aligned)
  all_goals simpa [Op.effect, next, put, save, CheckSPAlignment, state_simp_rules] using aligned

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def Control (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: rest, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Control base rest (op.effect s)

theorem block_run (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (control : Control base ops s) :
    run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
      change run (rest.length + 1) s = block rest (op.effect s)
      rw [run, step op s base code error aligned control.1]
      exact ih _ (Codec.Linked.WordsAt.preserve code (op.program s))
        ((op.error s).trans error) (op.aligned s aligned) control.2

def ops : List Op :=
  [.p0, .p4, .p8, .p12, .p16, .p20, .p24, .p28, .p32, .p36, .p40, .p44, .p48, .p52]

@[irreducible] def entered (s : ArmState) : ArmState := block ops s

/-- The unmodified fourteen-instruction prologue starts at the original entry. -/
theorem entry_run (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) : run 14 s = entered s := by
  apply block_run ops s base code error aligned
  change r .PC s = _ at pc
  simp (config := {decide := true}) [Control, ops, Op.row, Op.effect,
    next, put, save, state_simp_rules, pc, BitVec.add_assoc]

@[simp] theorem entered_program (s : ArmState) : (entered s).program = s.program := by
  simp [entered, block, ops]

@[simp] theorem entered_error (s : ArmState) : read_err (entered s) = read_err s := by
  simp [entered, block, ops]

@[simp] theorem entered_sp (s : ArmState) :
    r (.GPR 31#5) (entered s) = r (.GPR 31#5) s - 160#64 := by
  simp [entered, block, ops, Op.effect, next, put, save, state_simp_rules]

@[simp] theorem entered_pc (s : ArmState) : read_pc (entered s) = read_pc s + 56#64 := by
  simp [entered, block, ops, Op.effect, next, put, save, state_simp_rules, BitVec.add_assoc]

@[simp] theorem entered_claims (s : ArmState) :
    r (.GPR 22#5) (entered s) = r (.GPR 3#5) s := by
  simp [entered, block, ops, Op.effect, next, put, save, state_simp_rules]

@[simp] theorem entered_output (s : ArmState) :
    r (.GPR 19#5) (entered s) = r (.GPR 0#5) s := by
  simp [entered, block, ops, Op.effect, next, put, save, state_simp_rules]

@[simp] theorem entered_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (entered s) = r (.SFP reg) s := by
  simp [entered, block, ops, Op.effect, next, put, save, state_simp_rules]

end SszArm.Indices.RejectClaimPaths.Entry
