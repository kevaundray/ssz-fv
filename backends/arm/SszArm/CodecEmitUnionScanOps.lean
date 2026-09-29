import SszArm.CodecLinkedEmit
import SszArm.EmitActivationReturnOps
import SszArm.EmitDispatchOps

namespace SszArm.Codec.Emit.Union.Scan

open SszArm.Emit.Activation (next put)
open SszArm.Emit.Dispatch (branch)

inductive Op where
  | p1636 | p1640 | p1644 | p1648 | p1656 | p1660 | p1664 | p1668
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p1636 => (1636, 0xb400039b#32)
  | .p1640 => (1640, 0xa9420740#32)
  | .p1644 => (1644, 0xaa1703e2#32)
  | .p1648 => (1648, 0xaa1803e3#32)
  | .p1656 => (1656, 0x12001c08#32)
  | .p1660 => (1660, 0x9100635a#32)
  | .p1664 => (1664, 0xd100637b#32)
  | .p1668 => (1668, 0x35ffff08#32)

def Op.effect : Op → ArmState → ArmState
  | .p1636, s => branch (r (.GPR 27#5) s = 0#64) 112#64 s
  | .p1640, s =>
      w (.GPR 1#5) (read_mem_bytes 8 (r (.GPR 26#5) s + 40#64) s)
        (put 0 (read_mem_bytes 8 (r (.GPR 26#5) s + 32#64) s) s)
  | .p1644, s => put 2 (r (.GPR 23#5) s) s
  | .p1648, s => put 3 (r (.GPR 24#5) s) s
  | .p1656, s => put 8 (((r (.GPR 0#5) s).setWidth 8).setWidth 64) s
  | .p1660, s => put 26 (r (.GPR 26#5) s + 24#64) s
  | .p1664, s => put 27 (r (.GPR 27#5) s - 24#64) s
  | .p1668, s => branch ((r (.GPR 8#5) s).setWidth 32 ≠ 0#32) (-32#64) s

private theorem low_byte_mask (word : BitVec 64) :
    (word.setWidth 32).setWidth 64 &&& 255#64 = (word.setWidth 8).setWidth 64 := by
  rw [show 255#64 = (BitVec.allOnes 8).setWidth 64 by decide]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro bit bound
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_allOnes]
  by_cases low : bit < 8
  · simp [low, bound, show bit < 32 by omega]
  · simp [low]

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.Emit.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := Linked.Emit.chunk6_codeAt code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, branch, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, BitVec.setWidth_eq, BoolCodec.pair_read_low,
       BoolCodec.pair_read_high, BitVec.add_assoc, BitVec.sub_eq_add_neg,
       low_byte_mask, apply_ite]
  all_goals first
    | exact w_of_w_commute (by decide)
    | simp only [w, write_base_pc, write_base_gpr]
    | (split <;> simp_all)

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, branch, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, branch, state_simp_rules]

@[simp] theorem Op.memory (op : Op) (s : ArmState) : (op.effect s).mem = s.mem := by
  cases op <;> simp [Op.effect, put, next, branch, state_simp_rules]

@[simp] theorem Op.register (op : Op) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [0#5, 1#5, 2#5, 3#5, 8#5, 26#5, 27#5]) :
    r (.GPR reg) (op.effect s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.mem_singleton, not_or] at untouched
  cases op <;> simp [Op.effect, put, next, branch, state_simp_rules,
    untouched.1, untouched.2.1, untouched.2.2.1, untouched.2.2.2.1,
    untouched.2.2.2.2.1, untouched.2.2.2.2.2.1, untouched.2.2.2.2.2.2]

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, put, next, branch, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState := ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.Emit.CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error follows.1]
    exact ih _ (Linked.WordsAt.preserve code (op.program s))
      ((op.error s).trans error) follows.2

def prepareOps : List Op := [.p1636, .p1640, .p1644, .p1648]
def checkOps : List Op := [.p1656, .p1660, .p1664, .p1668]

@[irreducible] def prepared (s : ArmState) : ArmState := block prepareOps s
@[irreducible] def checked (s : ArmState) : ArmState := block checkOps s

theorem prepared_run (s : ArmState) (base : BitVec 64)
    (code : Linked.Emit.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 1636#64) (nonempty : r (.GPR 27#5) s ≠ 0#64) :
    run 4 s = prepared s := by
  rw [prepared]
  apply runs prepareOps s base code error
  change r .PC s = _ at pc
  simp [prepareOps, Follows, Op.row, Op.effect, next, put, branch,
    state_simp_rules, pc, nonempty, BitVec.add_assoc]

theorem prepared_pc (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 1636#64) (nonempty : r (.GPR 27#5) s ≠ 0#64) :
    read_pc (prepared s) = base + 1652#64 := by
  change r .PC s = _ at pc
  simp [prepared, prepareOps, block, Op.effect, next, put, branch,
    state_simp_rules, pc, nonempty, BitVec.add_assoc]

theorem checked_run (s : ArmState) (base : BitVec 64)
    (code : Linked.Emit.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 1656#64) : run 4 s = checked s := by
  rw [checked]
  apply runs checkOps s base code error
  change r .PC s = _ at pc
  simp [checkOps, Follows, Op.row, Op.effect, next, put, branch,
    state_simp_rules, pc, BitVec.add_assoc]

theorem checked_pc (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 1656#64) :
    read_pc (checked s) = base +
      (if (r (.GPR 0#5) s).setWidth 8 = 0#8 then 1672#64 else 1636#64) := by
  change r .PC s = _ at pc
  simp [checked, checkOps, block, Op.effect, next, put, branch,
    state_simp_rules, pc, BitVec.add_assoc, apply_ite]
  split <;> (try simp_all) <;> bv_omega

@[simp] theorem prepared_arguments (s : ArmState) :
    r (.GPR 0#5) (prepared s) = read_mem_bytes 8 (r (.GPR 26#5) s + 32#64) s ∧
      r (.GPR 1#5) (prepared s) = read_mem_bytes 8 (r (.GPR 26#5) s + 40#64) s ∧
      r (.GPR 2#5) (prepared s) = r (.GPR 23#5) s ∧
      r (.GPR 3#5) (prepared s) = r (.GPR 24#5) s := by
  simp [prepared, prepareOps, block, Op.effect, next, put, branch, state_simp_rules]

@[simp] theorem checked_cursor (s : ArmState) :
    r (.GPR 26#5) (checked s) = r (.GPR 26#5) s + 24#64 ∧
      r (.GPR 27#5) (checked s) = r (.GPR 27#5) s - 24#64 := by
  simp [checked, checkOps, block, Op.effect, next, put, branch, state_simp_rules]

@[simp] theorem prepared_memory (s : ArmState) : (prepared s).mem = s.mem := by
  simp [prepared, prepareOps, block, Op.effect, next, put, branch, state_simp_rules]

@[simp] theorem checked_memory (s : ArmState) : (checked s).mem = s.mem := by
  simp [checked, checkOps, block, Op.effect, next, put, branch, state_simp_rules]

end SszArm.Codec.Emit.Union.Scan
