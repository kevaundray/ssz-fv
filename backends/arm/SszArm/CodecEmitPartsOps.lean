import SszArm.CodecLinkedEmitParts
import SszArm.EmitActivationReturnOps
import SszArm.EmitDispatchOps

namespace SszArm.Codec.Emit.Parts

open SszArm.Emit.Activation (next put save)
open SszArm.Emit.ReturnBlock (restore)
open SszArm.Emit.Dispatch (branch)

/-- Actual activation and success-return instructions of emit_parts. -/
inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36
  | p40 | p44 | p48 | p516
  | p736 | p740 | p744 | p748 | p752 | p756 | p760 | p764
  | p768 | p772 | p776 | p780 | p784
  | p788 | p792 | p796 | p800 | p804 | p808 | p812 | p816
  | p820 | p824 | p828 | p832 | p836 | p840
  | p1088 | p1092 | p1096 | p1100 | p1104 | p1108 | p1112 | p1116
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xd10383ff#32)
  | .p4 => (4, 0xa9087bfd#32)
  | .p8 => (8, 0xa9096ffc#32)
  | .p12 => (12, 0xa90a67fa#32)
  | .p16 => (16, 0xa90b5ff8#32)
  | .p20 => (20, 0xa90c57f6#32)
  | .p24 => (24, 0xa90d4ff4#32)
  | .p28 => (28, 0xaa0203f6#32)
  | .p32 => (32, 0xaa0003fa#32)
  | .p36 => (36, 0xa9029be5#32)
  | .p40 => (40, 0xb4000ee4#32)
  | .p44 => (44, 0xf9400488#32)
  | .p48 => (48, 0xb4000ea8#32)
  | .p516 => (516, 0xb40006e3#32)
  | .p736 => (736, 0xaa1f03f8#32)
  | .p740 => (740, 0xf9000358#32)
  | .p744 => (744, 0xd10043ff#32)
  | .p748 => (748, 0xf90003e9#32)
  | .p752 => (752, 0xf90007ea#32)
  | .p756 => (756, 0x91000349#32)
  | .p760 => (760, 0x91010129#32)
  | .p764 => (764, 0x5280000a#32)
  | .p768 => (768, 0xb900012a#32)
  | .p772 => (772, 0xf94007ea#32)
  | .p776 => (776, 0xf94003e9#32)
  | .p780 => (780, 0x910043ff#32)
  | .p784 => (784, 0x1400004c#32)
  | .p788 => (788, 0xaa1403f9#32)
  | .p792 => (792, 0xf94003e8#32)
  | .p796 => (796, 0xf9000119#32)
  | .p800 => (800, 0xd10043ff#32)
  | .p804 => (804, 0xf90003e9#32)
  | .p808 => (808, 0xf90007ea#32)
  | .p812 => (812, 0x91000109#32)
  | .p816 => (816, 0x91010129#32)
  | .p820 => (820, 0x5280000a#32)
  | .p824 => (824, 0xb900012a#32)
  | .p828 => (828, 0xf94007ea#32)
  | .p832 => (832, 0xf94003e9#32)
  | .p836 => (836, 0x910043ff#32)
  | .p840 => (840, 0x1400003e#32)
  | .p1088 => (1088, 0xa94d4ff4#32)
  | .p1092 => (1092, 0xa94c57f6#32)
  | .p1096 => (1096, 0xa94b5ff8#32)
  | .p1100 => (1100, 0xa94a67fa#32)
  | .p1104 => (1104, 0xa9496ffc#32)
  | .p1108 => (1108, 0xa9487bfd#32)
  | .p1112 => (1112, 0x910383ff#32)
  | .p1116 => (1116, 0xd65f03c0#32)

def Op.effect : Op → ArmState → ArmState
  | .p0, s => put 31 (r (.GPR 31#5) s - 224#64) s
  | .p4, s => save 29 30 128#64 s
  | .p8, s => save 28 27 144#64 s
  | .p12, s => save 26 25 160#64 s
  | .p16, s => save 24 23 176#64 s
  | .p20, s => save 22 21 192#64 s
  | .p24, s => save 20 19 208#64 s
  | .p28, s => put 22 (r (.GPR 2#5) s) s
  | .p32, s => put 26 (r (.GPR 0#5) s) s
  | .p36, s => save 5 6 40#64 s
  | .p40, s => branch (r (.GPR 4#5) s = 0#64) 476#64 s
  | .p44, s => put 8 (read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s) s
  | .p48, s => branch (r (.GPR 8#5) s = 0#64) 468#64 s
  | .p516, s => branch (r (.GPR 3#5) s = 0#64) 220#64 s
  | .p736, s => put 24 0#64 s
  | .p740, s => next (write_mem_bytes 8 (r (.GPR 26#5) s) (r (.GPR 24#5) s) s)
  | .p744, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p748, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p752, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p756, s => put 9 (r (.GPR 26#5) s) s
  | .p760, s => put 9 (r (.GPR 9#5) s + 64#64) s
  | .p764, s => put 10 0#64 s
  | .p768, s => next (write_mem_bytes 4 (r (.GPR 9#5) s) ((r (.GPR 10#5) s).setWidth 32) s)
  | .p772, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p776, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p780, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p784, s => w .PC (read_pc s + 304#64) s
  | .p788, s => put 25 (r (.GPR 20#5) s) s
  | .p792, s => put 8 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p796, s => next (write_mem_bytes 8 (r (.GPR 8#5) s) (r (.GPR 25#5) s) s)
  | .p800, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p804, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p808, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p812, s => put 9 (r (.GPR 8#5) s) s
  | .p816, s => put 9 (r (.GPR 9#5) s + 64#64) s
  | .p820, s => put 10 0#64 s
  | .p824, s => next (write_mem_bytes 4 (r (.GPR 9#5) s) ((r (.GPR 10#5) s).setWidth 32) s)
  | .p828, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p832, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p836, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p840, s => w .PC (read_pc s + 248#64) s
  | .p1088, s => restore 20 19 208#64 s
  | .p1092, s => restore 22 21 192#64 s
  | .p1096, s => restore 24 23 176#64 s
  | .p1100, s => restore 26 25 160#64 s
  | .p1104, s => restore 28 27 144#64 s
  | .p1108, s => restore 29 30 128#64 s
  | .p1112, s => put 31 (r (.GPR 31#5) s + 224#64) s
  | .p1116, s => w .PC (r (.GPR 30#5) s) s

theorem fetched (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) :
    s.program.find? (base + BitVec.ofNat 64 op.row.1) = some op.row.2 := by
  cases op <;> first
    | exact Linked.EmitParts.chunk0_codeAt code _ (by decide)
    | exact Linked.EmitParts.chunk2_codeAt code _ (by decide)
    | exact Linked.EmitParts.chunk3_codeAt code _ (by decide)
    | exact Linked.EmitParts.chunk4_codeAt code _ (by decide)

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have word := fetched op s base code
  cases op
  all_goals
    simp only [Op.row] at pc word
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans word) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, save, restore, branch, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, aligned, BitVec.sub_eq_add_neg,
       BitVec.setWidth_eq, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
       BitVec.add_assoc, apply_ite]
  all_goals first
    | exact w_of_w_commute (by decide)
    | simp only [w, write_base_pc, write_base_gpr]
    | (split <;> simp_all)

@[simp] theorem Op.program (op : Op) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, save, restore, branch, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, save, restore, branch, state_simp_rules]

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, next, put, save, restore, branch, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => CheckSPAlignment s ∧
      read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error follows.1 follows.2.1]
    exact ih _ (Linked.WordsAt.preserve code (op.program s))
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

end SszArm.Codec.Emit.Parts
