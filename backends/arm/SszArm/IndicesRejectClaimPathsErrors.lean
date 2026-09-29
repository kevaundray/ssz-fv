import SszArm.IndicesRejectClaimPathsZero
import SszArm.IndicesRejectClaimPathsReturn
import SszArm.CodecSimd

namespace SszArm.Indices.RejectClaimPaths.Errors

open Dispatch.Block (next put)

inductive Op where
  | p676 | p680 | p684 | p688 | p692 | p696
  | p860 | p864 | p868 | p872 | p876 | p880 | p884 | p888 | p892 | p896 | p900 | p904
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p676 => (676, 0x6f00e400#32)
  | .p680 => (680, 0xaa1f03f4#32)
  | .p684 => (684, 0xaa1f03e8#32)
  | .p688 => (688, 0xaa1f03f5#32)
  | .p692 => (692, 0x52800509#32)
  | .p696 => (696, 0x1400002c#32)
  | .p860 => (860, 0x6f00e400#32)
  | .p864 => (864, 0xaa1f03e8#32)
  | .p868 => (868, 0x528004e9#32)
  | .p872 => (872, 0xad0103e0#32)
  | .p876 => (876, 0x5280002a#32)
  | .p880 => (880, 0xa9015275#32)
  | .p884 => (884, 0xa900226a#32)
  | .p888 => (888, 0xa9422be8#32)
  | .p892 => (892, 0xb9004269#32)
  | .p896 => (896, 0xa9022a68#32)
  | .p900 => (900, 0xa94323eb#32)
  | .p904 => (904, 0xa903226b#32)

def Op.effect : Op → ArmState → ArmState
  | .p676, s | .p860, s => next (w (.SFP 0#5) 0#128 s)
  | .p680, s => put 20 0#64 s
  | .p684, s | .p864, s => put 8 0#64 s
  | .p688, s => put 21 0#64 s
  | .p692, s => put 9 40#64 s
  | .p696, s => w .PC (read_pc s + 176#64) s
  | .p868, s => put 9 39#64 s
  | .p872, s => next (write_mem_bytes 32 (r (.GPR 31#5) s + 32#64)
      (r (.SFP 0#5) s ++ r (.SFP 0#5) s) s)
  | .p876, s => put 10 1#64 s
  | .p880, s => next (write_mem_bytes 16 (r (.GPR 19#5) s + 16#64)
      (r (.GPR 20#5) s ++ r (.GPR 21#5) s) s)
  | .p884, s => next (write_mem_bytes 16 (r (.GPR 19#5) s)
      (r (.GPR 8#5) s ++ r (.GPR 10#5) s) s)
  | .p888, s => next (w (.GPR 10#5)
      (read_mem_bytes 8 (r (.GPR 31#5) s + 40#64) s)
      (w (.GPR 8#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 32#64) s) s))
  | .p892, s => next (write_mem_bytes 4 (r (.GPR 19#5) s + 64#64)
      ((r (.GPR 9#5) s).setWidth 32) s)
  | .p896, s => next (write_mem_bytes 16 (r (.GPR 19#5) s + 32#64)
      (r (.GPR 10#5) s ++ r (.GPR 8#5) s) s)
  | .p900, s => next (w (.GPR 8#5)
      (read_mem_bytes 8 (r (.GPR 31#5) s + 56#64) s)
      (w (.GPR 11#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 48#64) s) s))
  | .p904, s => next (write_mem_bytes 16 (r (.GPR 19#5) s + 48#64)
      (r (.GPR 8#5) s ++ r (.GPR 11#5) s) s)

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := code op.row (by cases op <;> decide)
  cases op with
  | p676 =>
      simpa only [Op.effect, next] using Codec.Linked.Simd.word_6f00e400 s error aligned
        (by simpa only [pc, Op.row] using fetched)
  | p860 =>
      simpa only [Op.effect, next] using Codec.Linked.Simd.word_6f00e400 s error aligned
        (by simpa only [pc, Op.row] using fetched)
  | p872 =>
      simpa only [Op.effect, next] using Codec.Linked.Simd.word_ad0103e0 s error aligned
        (by simpa only [pc, Op.row] using fetched)
  | _ =>
      simp only [Op.row] at pc fetched
      rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
        (fetch_inst_from_program.trans fetched) rfl]
      simp (config := {decide := true, instances := true})
        [Op.effect, next, put, exec_inst, state_simp_rules, bitvec_rules,
          minimal_theory, aligned, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
          BitVec.add_assoc]
      all_goals first | rfl | exact w_of_w_commute (by decide)

@[simp] theorem Op.program (op : Op) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, state_simp_rules]

@[simp] theorem Op.sp (op : Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = r (.GPR 31#5) s := by
  cases op <;> simp [Op.effect, next, put, state_simp_rules]

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
      apply ih _ (Codec.Linked.WordsAt.preserve code (op.program s))
        ((op.error s).trans error) _ control.2
      exact CheckSPAlignment_of_r_sp_aligned (op.sp s) (BoolCodec.stack_aligned s aligned)

def notGindexOps : List Op :=
  [.p860, .p864, .p868, .p872, .p876, .p880, .p884, .p888, .p892, .p896, .p900, .p904]

def rootOps : List Op :=
  [.p676, .p680, .p684, .p688, .p692, .p696, .p872, .p876, .p880, .p884,
    .p888, .p892, .p896, .p900, .p904]

@[irreducible] def notGindex (s : ArmState) : ArmState := block notGindexOps s

@[irreducible] def root (s : ArmState) : ArmState := block rootOps s

theorem notGindex_run (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 860#64) :
    run 12 s = notGindex s := by
  apply block_run notGindexOps s base code error aligned
  change r .PC s = _ at pc
  simp [Control, notGindexOps, Op.row, Op.effect, next, put, state_simp_rules,
    pc, BitVec.add_assoc]

theorem root_run (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 676#64) :
    run 15 s = root s := by
  apply block_run rootOps s base code error aligned
  change r .PC s = _ at pc
  simp [Control, rootOps, Op.row, Op.effect, next, put, state_simp_rules,
    pc, BitVec.add_assoc]

/-- In particular the noncanonical Large pair is never replaced by Small zero. -/
theorem notGindex_raw_pair (s : ArmState) :
    r (.GPR 21#5) (notGindex s) = r (.GPR 21#5) s ∧
      r (.GPR 20#5) (notGindex s) = r (.GPR 20#5) s := by
  simp [notGindex, block, notGindexOps, Op.effect, next, put, state_simp_rules]

/-- The actual zero-Large edge enters 860, not the Small pointer write at 856. -/
theorem large_notGindex_run (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 72#64)
    (exhausted : r (.GPR 9#5) s = 0#64) :
    run 13 s = notGindex (w .PC (base + 860#64) s) := by
  change run 12 (stepi s) = _
  rw [Zero.large_guard s base code error pc exhausted]
  apply notGindex_run _ base
  · exact Codec.Linked.WordsAt.preserve code (by simp [state_simp_rules])
  · simpa [state_simp_rules] using error
  · simpa [CheckSPAlignment, state_simp_rules] using aligned
  · simp [state_simp_rules]

end SszArm.Indices.RejectClaimPaths.Errors
