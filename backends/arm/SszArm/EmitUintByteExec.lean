import SszArm.EmitUintByteOps

namespace SszArm.Emit.Uint

open UintCodec

theorem signed_shift_remainder (word : BitVec 64) :
    (word.toInt % 64).toNat = word.toNat % 64 := by
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

theorem byte_step (s : ArmState) (base : BitVec 64) (op : ByteOp)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (he : read_err s = .None) (ha : CheckSPAlignment s) :
    stepi s = op.effect base s := by
  have hf := body_codeAt hc op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [ByteOp.row] at hp hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    change r .PC s = _ at hp
    simp (config := {decide := true, instances := true})
      [ByteOp.effect, put, next, Dispatch.next, Dispatch.compare64,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BoolCodec.pair_read_low, BoolCodec.pair_read_high, ha, hp, BitVec.add_assoc,
       BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_lsr3_mask,
       uint_and_ones, signed_shift_remainder, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr]

@[simp] theorem ByteOp.program (op : ByteOp) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [ByteOp.effect, put, next, Dispatch.next,
    Dispatch.compare64, state_simp_rules]

@[simp] theorem ByteOp.error (op : ByteOp) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [ByteOp.effect, put, next, Dispatch.next,
    Dispatch.compare64, state_simp_rules]

theorem ByteOp.aligned (op : ByteOp) (base : BitVec 64) (s : ArmState)
    (ha : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  cases op <;> simp [ByteOp.effect, put, next, Dispatch.next,
    Dispatch.compare64, state_simp_rules, ha]
  all_goals first
    | exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s ha)
    | exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s ha)

@[simp] theorem ByteOp.vector (op : ByteOp) (base : BitVec 64) (s : ArmState)
    (reg : BitVec 5) : r (.SFP reg) (op.effect base s) = r (.SFP reg) s := by
  cases op <;> simp [ByteOp.effect, put, next, Dispatch.next,
    Dispatch.compare64, state_simp_rules]

def byteBlock (base : BitVec 64) (ops : List ByteOp) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def ByteFollows (base : BitVec 64) : List ByteOp → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      ByteFollows base ops (op.effect base s)

theorem byte_run (base : BitVec 64) (ops : List ByteOp) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : ByteFollows base ops s) : run ops.length s = byteBlock base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = byteBlock base ops (op.effect base s)
    rw [run, byte_step s base op hc hf.1 he ha]
    exact ih _ (by simpa only [CodeAt, ByteOp.program] using hc)
      ((op.error base s).trans he) (op.aligned base s ha) hf.2

@[simp] theorem byteBlock_program (base : BitVec 64) (ops : List ByteOp) (s : ArmState) :
    (byteBlock base ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.program base s)

@[simp] theorem byteBlock_error (base : BitVec 64) (ops : List ByteOp) (s : ArmState) :
    read_err (byteBlock base ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.error base s)

end SszArm.Emit.Uint
