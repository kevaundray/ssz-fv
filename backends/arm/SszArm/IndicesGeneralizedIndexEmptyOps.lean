import SszArm.IndicesLinkedGeneralizedIndex
import SszArm.DispatchBlocks
import SszArm.BoolMemory

namespace SszArm.Indices.GeneralizedIndex.Empty

open Dispatch.Block (next put save branch)

/-- The actual original-entry empty-path route, including its original return. -/
inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p132 | p136 | p140 | p144 | p148 | p152 | p156 | p160 | p164 | p168 | p172 | p176 | p180 | p184 | p188 | p192 | p196 | p200 | p204 | p208 | p212 | p216 | p220 | p224 | p228 | p232 | p236 | p240
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xd10383ff#32)
  | .p4 => (4, 0xf9004bfe#32)
  | .p8 => (8, 0xa90a67fa#32)
  | .p12 => (12, 0xa90b5ff8#32)
  | .p16 => (16, 0xa90c57f6#32)
  | .p20 => (20, 0xa90d4ff4#32)
  | .p24 => (24, 0xaa0003f3#32)
  | .p28 => (28, 0xb4000343#32)
  | .p132 => (132, 0x52800028#32)
  | .p136 => (136, 0xd10043ff#32)
  | .p140 => (140, 0xf90003e9#32)
  | .p144 => (144, 0xf90007ea#32)
  | .p148 => (148, 0x91000269#32)
  | .p152 => (152, 0xd280000a#32)
  | .p156 => (156, 0xf900012a#32)
  | .p160 => (160, 0xf9000528#32)
  | .p164 => (164, 0xf94007ea#32)
  | .p168 => (168, 0xf94003e9#32)
  | .p172 => (172, 0x910043ff#32)
  | .p176 => (176, 0xd10043ff#32)
  | .p180 => (180, 0xf90003e9#32)
  | .p184 => (184, 0xf90007ea#32)
  | .p188 => (188, 0x91000269#32)
  | .p192 => (192, 0x91010129#32)
  | .p196 => (196, 0x5280000a#32)
  | .p200 => (200, 0xb900012a#32)
  | .p204 => (204, 0xf94007ea#32)
  | .p208 => (208, 0xf94003e9#32)
  | .p212 => (212, 0x910043ff#32)
  | .p216 => (216, 0xa94d4ff4#32)
  | .p220 => (220, 0xf9404bfe#32)
  | .p224 => (224, 0xa94c57f6#32)
  | .p228 => (228, 0xa94b5ff8#32)
  | .p232 => (232, 0xa94a67fa#32)
  | .p236 => (236, 0x910383ff#32)
  | .p240 => (240, 0xd65f03c0#32)

def loadPair (first second : BitVec 5) (offset : BitVec 64)
    (s : ArmState) : ArmState :=
  next (w (.GPR second) (read_mem_bytes 8 (r (.GPR 31#5) s + offset + 8#64) s)
    (w (.GPR first) (read_mem_bytes 8 (r (.GPR 31#5) s + offset) s) s))

def Op.effect : Op → ArmState → ArmState
  | .p0, s => put 31 (r (.GPR 31#5) s - 224#64) s
  | .p4, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 144#64) (r (.GPR 30#5) s) s)
  | .p8, s => save 26 25 160#64 s
  | .p12, s => save 24 23 176#64 s
  | .p16, s => save 22 21 192#64 s
  | .p20, s => save 20 19 208#64 s
  | .p24, s => put 19 (r (.GPR 0#5) s) s
  | .p28, s => branch (r (.GPR 3#5) s = 0#64) 104#64 s
  | .p132, s => put 8 1#64 s
  | .p136, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p140, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p144, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p148, s => put 9 (r (.GPR 19#5) s) s
  | .p152, s => put 10 0#64 s
  | .p156, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p160, s => next (write_mem_bytes 8 (r (.GPR 9#5) s + 8#64) (r (.GPR 8#5) s) s)
  | .p164, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p168, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p172, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p176, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p180, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p184, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p188, s => put 9 (r (.GPR 19#5) s) s
  | .p192, s => put 9 (r (.GPR 9#5) s + 64#64) s
  | .p196, s => put 10 0#64 s
  | .p200, s => next (write_mem_bytes 4 (r (.GPR 9#5) s) ((r (.GPR 10#5) s).setWidth 32) s)
  | .p204, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p208, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p212, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p216, s => loadPair 20 19 208#64 s
  | .p220, s => put 30 (read_mem_bytes 8 (r (.GPR 31#5) s + 144#64) s) s
  | .p224, s => loadPair 22 21 192#64 s
  | .p228, s => loadPair 24 23 176#64 s
  | .p232, s => loadPair 26 25 160#64 s
  | .p236, s => put 31 (r (.GPR 31#5) s + 224#64) s
  | .p240, s => w .PC (r (.GPR 30#5) s) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.GeneralizedIndex.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (entry : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := Linked.GeneralizedIndex.chunk0_codeAt code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at entry fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, save, branch, loadPair, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, aligned, BitVec.sub_eq_add_neg, BitVec.add_assoc,
       apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

@[simp] theorem Op.program (op : Op) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, save, branch, loadPair, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, save, branch, loadPair, state_simp_rules]

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, next, put, save, branch, loadPair, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => CheckSPAlignment s ∧
      read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ Follows base ops (op.effect s)

theorem block_run (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.GeneralizedIndex.CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error follows.1 follows.2.1]
    exact ih _ (SszArm.Codec.Linked.WordsAt.preserve code (op.program s))
      ((op.error s).trans error) follows.2.2

@[simp] theorem block_program (ops : List Op) (s : ArmState) :
    (block ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.program s)

@[simp] theorem block_error (ops : List Op) (s : ArmState) :
    read_err (block ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.error s)

@[simp] theorem block_vector (ops : List Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (block ops s) = r (.SFP reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.vector s reg)

end SszArm.Indices.GeneralizedIndex.Empty
