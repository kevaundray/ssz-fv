import SszArm.IndicesLinkedChunkCount
import SszArm.DispatchBlocks
import SszArm.BoolAlignment
import SszArm.BoolMemory

set_option autoImplicit false

namespace SszArm.Indices.ChunkCount.Entry

open SszArm.Dispatch.Block (next put save)

inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xd10243ff#32)
  | .p4 => (4, 0xf9002bfe#32)
  | .p8 => (8, 0xa9065ff8#32)
  | .p12 => (12, 0xa90757f6#32)
  | .p16 => (16, 0xa9084ff4#32)
  | .p20 => (20, 0xf9400028#32)
  | .p24 => (24, 0xaa0203f3#32)

def Op.effect : Op → ArmState → ArmState
  | .p0, s => put 31 (r (.GPR 31#5) s - 144#64) s
  | .p4, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 80#64) (r (.GPR 30#5) s) s)
  | .p8, s => save 24 23 96#64 s
  | .p12, s => save 22 21 112#64 s
  | .p16, s => save 20 19 128#64 s
  | .p20, s => put 8 (read_mem_bytes 8 (r (.GPR 1#5) s) s) s
  | .p24, s => put 19 (r (.GPR 2#5) s) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkCount.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := Linked.ChunkCount.chunk0_codeAt code op.row (by cases op <;> decide)
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

private theorem aligned_sub144 (sp : BitVec 64) (aligned : Aligned sp 4) :
    Aligned (sp - 144#64) 4 := by
  have a := BoolCodec.aligned_sub32 sp aligned
  have b := BoolCodec.aligned_sub32 _ a
  have c := BoolCodec.aligned_sub32 _ b
  have d := BoolCodec.aligned_sub32 _ c
  have e := BoolCodec.aligned_sub16 _ d
  simpa (config := {decide := true}) only [BitVec.sub_eq_add_neg, BitVec.add_assoc] using e

theorem Op.aligned (op : Op) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect s) := by
  have original := BoolCodec.stack_aligned s aligned
  cases op
  case p0 =>
    apply CheckSPAlignment_of_r_sp_aligned
      (show r (.GPR 31#5) (Op.p0.effect s) = r (.GPR 31#5) s - 144#64 by
        simp [Op.effect, put, next, state_simp_rules])
    exact aligned_sub144 _ original
  all_goals simpa [Op.effect, next, put, save, CheckSPAlignment, state_simp_rules] using aligned

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def Control (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Control base ops (op.effect s)

theorem block_run (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkCount.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (control : Control base ops s) :
    run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error aligned control.1]
    exact ih _ (Codec.Linked.WordsAt.preserve code (op.program s))
      ((op.error s).trans error) (op.aligned s aligned) control.2

def ops : List Op := [.p0, .p4, .p8, .p12, .p16, .p20, .p24]

def entered (s : ArmState) : ArmState := block ops s

/-- Actual original-entry execution, before descriptor dispatch. -/
theorem original_entry (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkCount.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    run 7 s = entered s := by
  apply block_run ops s base code error aligned
  change r .PC s = _ at pc
  simp [Control, ops, Op.row, Op.effect, next, put, save, state_simp_rules,
    pc, BitVec.add_assoc]

@[simp] theorem entered_program (s : ArmState) : (entered s).program = s.program := by
  simp [entered, block, ops, Op.effect, next, put, save, state_simp_rules]

@[simp] theorem entered_error (s : ArmState) : read_err (entered s) = read_err s := by
  simp [entered, block, ops, Op.effect, next, put, save, state_simp_rules]

@[simp] theorem entered_pc (s : ArmState) : read_pc (entered s) = read_pc s + 28#64 := by
  simp [entered, block, ops, Op.effect, next, put, save, state_simp_rules, BitVec.add_assoc]

@[simp] theorem entered_sp (s : ArmState) :
    r (.GPR 31#5) (entered s) = r (.GPR 31#5) s - 144#64 := by
  simp [entered, block, ops, Op.effect, next, put, save, state_simp_rules]

@[simp] theorem entered_arena (s : ArmState) :
    r (.GPR 19#5) (entered s) = r (.GPR 2#5) s := by
  simp [entered, block, ops, Op.effect, next, put, save, state_simp_rules]

theorem entered_descriptor (s : ArmState) :
    r (.GPR 8#5) (entered s) = read_mem_bytes 8 (r (.GPR 1#5) s) (entered s) := by
  simp [entered, block, ops, Op.effect, next, put, save, state_simp_rules]

end SszArm.Indices.ChunkCount.Entry
