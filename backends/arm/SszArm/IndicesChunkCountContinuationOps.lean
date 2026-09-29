import SszArm.IndicesLinkedChunkCount
import SszArm.DispatchBlocks
import SszArm.BoolAlignment
import SszArm.BoolMemory

set_option autoImplicit false

namespace SszArm.Indices.ChunkCount.Continuation

open SszArm.Dispatch.Block (next put branch)

/-- Local instructions surrounding the real NatMul/memcpy calls and ceil tail.
The linked B/BL certificates remain in IndicesLinkedBranches. -/
inductive Op where
  | p64 | p68 | p104 | p148 | p152 | p156 | p384
  | p360 | p364 | p368 | p372 | p376 | p380
  | p468 | p472 | p476 | p480 | p484 | p488
  | p824 | p828 | p832 | p836 | p840 | p844 | p848
  | p856 | p860 | p864 | p868 | p872 | p876
  | p884 | p888 | p892 | p896 | p900 | p904
  | p912 | p916 | p920 | p924 | p928 | p932 | p936 | p940 | p944
  | p948 | p952 | p956
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p64 => (64, 0xa9408828#32)
  | .p68 => (68, 0x52800103#32)
  | .p104 => (104, 0x52800028#32)
  | .p148 => (148, 0xa9408828#32)
  | .p152 => (152, 0xaa0803e1#32)
  | .p156 => (156, 0x528000a3#32)
  | .p384 => (384, 0xf9400828#32)
  | .p360 => (360, 0xa9484ff4#32)
  | .p364 => (364, 0xf9402bfe#32)
  | .p368 => (368, 0xa94757f6#32)
  | .p372 => (372, 0xa9465ff8#32)
  | .p376 => (376, 0x910243ff#32)
  | .p380 => (380, 0xd65f03c0#32)
  | .p468 => (468, 0xa9484ff4#32)
  | .p472 => (472, 0xf9402bfe#32)
  | .p476 => (476, 0xa94757f6#32)
  | .p480 => (480, 0xa9465ff8#32)
  | .p484 => (484, 0x910243ff#32)
  | .p488 => (488, 0xd65f03c0#32)
  | .p824 => (824, 0xaa0803e1#32)
  | .p828 => (828, 0xaa1303e4#32)
  | .p832 => (832, 0xa9484ff4#32)
  | .p836 => (836, 0xa94757f6#32)
  | .p840 => (840, 0xf9402bfe#32)
  | .p844 => (844, 0xa9465ff8#32)
  | .p848 => (848, 0x910243ff#32)
  | .p856 => (856, 0xa9408828#32)
  | .p860 => (860, 0xaa0003f4#32)
  | .p864 => (864, 0x910023e0#32)
  | .p868 => (868, 0xaa1303e5#32)
  | .p872 => (872, 0x910023f8#32)
  | .p876 => (876, 0xaa0803e1#32)
  | .p884 => (884, 0xa940d7f6#32)
  | .p888 => (888, 0xb9404bf7#32)
  | .p892 => (892, 0x340001d7#32)
  | .p896 => (896, 0x91004280#32)
  | .p900 => (900, 0x91004301#32)
  | .p904 => (904, 0x52800602#32)
  | .p912 => (912, 0xb9404fe8#32)
  | .p916 => (916, 0xa9005696#32)
  | .p920 => (920, 0x29082297#32)
  | .p924 => (924, 0xa9484ff4#32)
  | .p928 => (928, 0xf9402bfe#32)
  | .p932 => (932, 0xa94757f6#32)
  | .p936 => (936, 0xa9465ff8#32)
  | .p940 => (940, 0x910243ff#32)
  | .p944 => (944, 0xd65f03c0#32)
  | .p948 => (948, 0xaa1403e0#32)
  | .p952 => (952, 0xaa1603e1#32)
  | .p956 => (956, 0xaa1503e2#32)

def loadPair (first second source : BitVec 5) (offset : BitVec 64)
    (s : ArmState) : ArmState :=
  next (w (.GPR second) (read_mem_bytes 8 (r (.GPR source) s + offset + 8#64) s)
    (w (.GPR first) (read_mem_bytes 8 (r (.GPR source) s + offset) s) s))

def Op.effect : Op → ArmState → ArmState
  | .p64, s | .p148, s | .p856, s => loadPair 8 2 1 8#64 s
  | .p68, s => put 3 8#64 s
  | .p104, s => put 8 1#64 s
  | .p152, s | .p824, s | .p876, s => put 1 (r (.GPR 8#5) s) s
  | .p156, s => put 3 5#64 s
  | .p384, s => put 8 (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s) s
  | .p360, s | .p468, s | .p832, s | .p924, s => loadPair 20 19 31 128#64 s
  | .p364, s | .p472, s | .p840, s | .p928, s =>
      put 30 (read_mem_bytes 8 (r (.GPR 31#5) s + 80#64) s) s
  | .p368, s | .p476, s | .p836, s | .p932, s => loadPair 22 21 31 112#64 s
  | .p372, s | .p480, s | .p844, s | .p936, s => loadPair 24 23 31 96#64 s
  | .p376, s | .p484, s | .p848, s | .p940, s => put 31 (r (.GPR 31#5) s + 144#64) s
  | .p380, s | .p488, s | .p944, s => w .PC (r (.GPR 30#5) s) s
  | .p828, s => put 4 (r (.GPR 19#5) s) s
  | .p860, s => put 20 (r (.GPR 0#5) s) s
  | .p864, s => put 0 (r (.GPR 31#5) s + 8#64) s
  | .p868, s => put 5 (r (.GPR 19#5) s) s
  | .p872, s => put 24 (r (.GPR 31#5) s + 8#64) s
  | .p884, s => loadPair 22 21 31 8#64 s
  | .p888, s => put 23 ((read_mem_bytes 4 (r (.GPR 31#5) s + 72#64) s).zeroExtend 64) s
  | .p892, s => branch ((r (.GPR 23#5) s).setWidth 32 = 0#32) 56#64 s
  | .p896, s => put 0 (r (.GPR 20#5) s + 16#64) s
  | .p900, s => put 1 (r (.GPR 24#5) s + 16#64) s
  | .p904, s => put 2 48#64 s
  | .p912, s => put 8 ((read_mem_bytes 4 (r (.GPR 31#5) s + 76#64) s).zeroExtend 64) s
  | .p916, s => next (write_mem_bytes 16 (r (.GPR 20#5) s)
      (r (.GPR 21#5) s ++ r (.GPR 22#5) s) s)
  | .p920, s => next (write_mem_bytes 8 (r (.GPR 20#5) s + 64#64)
      ((r (.GPR 8#5) s).setWidth 32 ++ (r (.GPR 23#5) s).setWidth 32) s)
  | .p948, s => put 0 (r (.GPR 20#5) s) s
  | .p952, s => put 1 (r (.GPR 22#5) s) s
  | .p956, s => put 2 (r (.GPR 21#5) s) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkCount.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, branch, loadPair, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, aligned, BitVec.add_assoc,
       apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

@[simp] theorem Op.program (op : Op) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, branch, loadPair, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, branch, loadPair, state_simp_rules]

private theorem aligned_add144 (sp : BitVec 64) (aligned : Aligned sp 4) :
    Aligned (sp + 144#64) 4 := by
  have a := BoolCodec.aligned_add32 sp aligned
  have b := BoolCodec.aligned_add32 _ a
  have c := BoolCodec.aligned_add32 _ b
  have d := BoolCodec.aligned_add32 _ c
  have e := BoolCodec.aligned_add16 _ d
  simpa (config := {decide := true}) only [BitVec.add_assoc] using e

def Op.stackValue : Op → BitVec 64 → BitVec 64
  | .p376, sp | .p484, sp | .p848, sp | .p940, sp => sp + 144#64
  | _, sp => sp

@[simp] theorem Op.sp (op : Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = op.stackValue (r (.GPR 31#5) s) := by
  cases op <;> simp [Op.effect, Op.stackValue, next, put, branch, loadPair, state_simp_rules]

theorem Op.aligned (op : Op) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect s) := by
  apply CheckSPAlignment_of_r_sp_aligned (op.sp s)
  have original := BoolCodec.stack_aligned s aligned
  cases op <;> simp only [Op.stackValue]
  all_goals first | exact original | exact aligned_add144 _ original

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

end SszArm.Indices.ChunkCount.Continuation
