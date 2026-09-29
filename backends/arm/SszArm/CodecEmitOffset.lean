import SszArm.CodecLinkedEmitParts
import SszArm.EmitActivationReturnOps
import SszArm.EmitDispatchOps

namespace SszArm.Codec.Emit.Offset

open SszArm.Emit.Activation (next put)
open SszArm.Emit.Dispatch (branch compare64)

inductive Op where
  | p396 | p400 | p404 | p408 | p412 | p416 | p420 | p424
  | p428 | p432 | p436 | p440 | p444 | p448
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p396 => (396, 0xf9401be8#32)
  | .p400 => (400, 0x9100135b#32)
  | .p404 => (404, 0xeb08037f#32)
  | .p408 => (408, 0x54001748#32)
  | .p412 => (412, 0xf94017e8#32)
  | .p416 => (416, 0xd358fe89#32)
  | .p420 => (420, 0xd350fe8a#32)
  | .p424 => (424, 0xd348fe8b#32)
  | .p428 => (428, 0xab140279#32)
  | .p432 => (432, 0x8b1a0108#32)
  | .p436 => (436, 0x39000114#32)
  | .p440 => (440, 0x39000d09#32)
  | .p444 => (444, 0x3900090a#32)
  | .p448 => (448, 0x3900050b#32)

def Op.effect : Op → ArmState → ArmState
  | .p396, s => put 8 (read_mem_bytes 8 (r (.GPR 31#5) s + 48#64) s) s
  | .p400, s => put 27 (r (.GPR 26#5) s + 4#64) s
  | .p404, s => compare64 (r (.GPR 27#5) s) (r (.GPR 8#5) s) s
  | .p408, s => branch (r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1) 744#64 s
  | .p412, s => put 8 (read_mem_bytes 8 (r (.GPR 31#5) s + 40#64) s) s
  | .p416, s => put 9 (r (.GPR 20#5) s >>> 24) s
  | .p420, s => put 10 (r (.GPR 20#5) s >>> 16) s
  | .p424, s => put 11 (r (.GPR 20#5) s >>> 8) s
  | .p428, s =>
      let sum := AddWithCarry (r (.GPR 19#5) s) (r (.GPR 20#5) s) 0#1
      write_pstate sum.2 (put 25 sum.1 s)
  | .p432, s => put 8 (r (.GPR 8#5) s + r (.GPR 26#5) s) s
  | .p436, s => next (write_mem_bytes 1 (r (.GPR 8#5) s) ((r (.GPR 20#5) s).setWidth 8) s)
  | .p440, s => next (write_mem_bytes 1 (r (.GPR 8#5) s + 3#64) ((r (.GPR 9#5) s).setWidth 8) s)
  | .p444, s => next (write_mem_bytes 1 (r (.GPR 8#5) s + 2#64) ((r (.GPR 10#5) s).setWidth 8) s)
  | .p448, s => next (write_mem_bytes 1 (r (.GPR 8#5) s + 1#64) ((r (.GPR 11#5) s).setWidth 8) s)

private theorem lsr_mask (value : BitVec 64) (shift : Nat) (below : shift ≤ 64) :
    value.rotateRight shift &&& (BitVec.allOnes 64) &&&
      (BitVec.allOnes (64 - shift)).setWidth 64 = value >>> shift := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro bit bound
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, BitVec.getLsbD_ushiftRight]
  by_cases low : bit < 64 - shift
  · simp [low, bound, show shift + bit < 64 by omega]
  · have outside : value.getLsbD (shift + bit) = false :=
      BitVec.getLsbD_of_ge value (shift + bit) (by omega)
    simp [low, bound, outside]

private theorem lsr8_mask (value : BitVec 64) :
    value.rotateRight 8 &&& 18446744073709551615#64 &&& 72057594037927935#64 = value >>> 8 := by
  exact lsr_mask value 8 (by decide)

private theorem lsr16_mask (value : BitVec 64) :
    value.rotateRight 16 &&& 18446744073709551615#64 &&& 281474976710655#64 = value >>> 16 := by
  exact lsr_mask value 16 (by decide)

private theorem lsr24_mask (value : BitVec 64) :
    value.rotateRight 24 &&& 18446744073709551615#64 &&& 1099511627775#64 = value >>> 24 := by
  exact lsr_mask value 24 (by decide)

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := Linked.EmitParts.chunk1_codeAt code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, SszArm.Emit.Dispatch.next, put, branch, compare64, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, aligned, BitVec.setWidth_eq, BitVec.add_assoc, apply_ite,
       lsr8_mask, lsr16_mask, lsr24_mask]
  all_goals first
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr, write_pstate, write_base_flag]

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, SszArm.Emit.Dispatch.next, branch, compare64, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, SszArm.Emit.Dispatch.next, branch, compare64, state_simp_rules]

@[simp] theorem Op.stack (op : Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = r (.GPR 31#5) s := by
  cases op <;> simp [Op.effect, put, next, SszArm.Emit.Dispatch.next, branch, compare64, state_simp_rules]

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, put, next, SszArm.Emit.Dispatch.next, branch, compare64, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState := ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (follows : Follows base ops s) :
    run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error aligned follows.1]
    apply ih _ (Linked.WordsAt.preserve code (op.program s)) ((op.error s).trans error) _ follows.2
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, Op.stack] using aligned

def ops : List Op :=
  [.p396, .p400, .p404, .p408, .p412, .p416, .p420, .p424, .p428, .p432, .p436, .p440, .p444, .p448]

@[irreducible] def stored (s : ArmState) : ArmState := block ops s

def address (s : ArmState) : BitVec 64 :=
  read_mem_bytes 8 (r (.GPR 31#5) s + 40#64) s + r (.GPR 26#5) s

/-- Native store order is low, high, middle-high, middle-low; all four stores
precede the child-body bounds branch and the recursive call. -/
def memory (s : ArmState) : ArmState :=
  write_mem_bytes 1 (address s + 1#64) ((r (.GPR 20#5) s >>> 8).setWidth 8)
  (write_mem_bytes 1 (address s + 2#64) ((r (.GPR 20#5) s >>> 16).setWidth 8)
  (write_mem_bytes 1 (address s + 3#64) ((r (.GPR 20#5) s >>> 24).setWidth 8)
  (write_mem_bytes 1 (address s) ((r (.GPR 20#5) s).setWidth 8) s)))

@[simp] theorem stored_memory (s : ArmState) : (stored s).mem = (memory s).mem := by
  simp [stored, ops, block, Op.effect, put, next, SszArm.Emit.Dispatch.next, branch, compare64,
    memory, address, state_simp_rules]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem stored_frame (s : ArmState) (bound : (address s).toNat + 4 ≤ 2 ^ 64) :
    Delimited.MemoryFrame [((address s).toNat, 4)] s (stored s) := by
  intro target outside
  have apart := outside ((address s).toNat, 4) (by simp)
  simp only [Prod.fst, Prod.snd] at apart
  rw [stored_memory]
  simp only [memory]
  repeat' rw [BoolCodec.write_mem_bytes_frame _ _ 1 _ target (by bv_omega) (by bv_omega)]

/-- Register observations needed to discharge the following body bounds checks. -/
theorem stored_cursors (s : ArmState) :
    r (.GPR 27#5) (stored s) = r (.GPR 26#5) s + 4#64 ∧
      r (.GPR 25#5) (stored s) =
        (AddWithCarry (r (.GPR 19#5) s) (r (.GPR 20#5) s) 0#1).1 ∧
      r (.FLAG .C) (stored s) =
        (AddWithCarry (r (.GPR 19#5) s) (r (.GPR 20#5) s) 0#1).2.c := by
  simp [stored, ops, block, Op.effect, put, next, SszArm.Emit.Dispatch.next, branch, compare64, state_simp_rules]

private theorem head_guard (head capacity : BitVec 64)
    (fits : head.toNat + 4 ≤ capacity.toNat) :
    ¬ ((AddWithCarry (head + 4#64) (~~~capacity) 1#1).2.c = 1#1 ∧
      (AddWithCarry (head + 4#64) (~~~capacity) 1#1).2.z = 0#1) := by
  rw [Udivti3.cmp_high]
  have count : (head + 4#64).toNat = head.toNat + 4 := by bv_omega
  rw [count]
  omega

theorem stored_run (s : ArmState) (base : BitVec 64)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 396#64)
    (fits : (r (.GPR 26#5) s).toNat + 4 ≤
      (read_mem_bytes 8 (r (.GPR 31#5) s + 48#64) s).toNat) :
    run 14 s = stored s := by
  have guard := head_guard _ _ fits
  rw [stored]
  apply runs ops s base code error aligned
  change r .PC s = _ at pc
  simp [ops, Follows, Op.row, Op.effect, put, next, SszArm.Emit.Dispatch.next, branch, compare64,
    state_simp_rules, pc, guard, BitVec.add_assoc]

theorem stored_pc (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 396#64)
    (fits : (r (.GPR 26#5) s).toNat + 4 ≤
      (read_mem_bytes 8 (r (.GPR 31#5) s + 48#64) s).toNat) :
    read_pc (stored s) = base + 452#64 := by
  have guard := head_guard _ _ fits
  change r .PC s = _ at pc
  simp [stored, ops, block, Op.effect, put, next, SszArm.Emit.Dispatch.next, branch, compare64,
    state_simp_rules, pc, guard, BitVec.add_assoc]

/-- Exact little-endian bytes, proved without reading any previous output byte. -/
theorem stored_byte (s : ArmState) (index : Nat) (inside : index < 4)
    (bound : (address s).toNat + 4 ≤ 2 ^ 64) :
    read_mem_bytes 1 (address s + BitVec.ofNat 64 index) (stored s) =
      ((r (.GPR 20#5) s >>> (8 * index)).setWidth 8) := by
  have positions : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp (stored_memory s)]
  simp only [memory]
  rcases positions with rfl | rfl | rfl | rfl
  · rw [show address s + BitVec.ofNat 64 0 = address s by simp]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 1 1 _ _ _
      (by bv_omega) (by bv_omega) (by bv_omega)]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 1 1 _ _ _
      (by bv_omega) (by bv_omega) (by bv_omega)]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 1 1 _ _ _
      (by bv_omega) (by bv_omega) (by bv_omega)]
    simpa using BoolCodec.read_mem_bytes_write_mem_bytes_same s 1 (address s)
      ((r (.GPR 20#5) s).setWidth 8) (by bv_omega)
  · exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 1 _ _ (by bv_omega)
  · rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 1 1 _ _ _
      (by bv_omega) (by bv_omega) (by bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 1 _ _ (by bv_omega)
  · rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 1 1 _ _ _
      (by bv_omega) (by bv_omega) (by bv_omega)]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 1 1 _ _ _
      (by bv_omega) (by bv_omega) (by bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 1 _ _ (by bv_omega)

end SszArm.Codec.Emit.Offset
