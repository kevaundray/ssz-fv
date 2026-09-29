import SszArm.IndicesLinkedRebase
import SszArm.IndicesRebaseFillArithmetic

set_option autoImplicit false

namespace SszArm.Indices.Rebase.Fill.Mask

inductive Op where
  | p952 | p956 | p960 | p964 | p968 | p972 | p976 | p980 | p984 | p988
  | p992 | p996 | p1000 | p1004 | p1008 | p1012 | p1016 | p1020 | p1024
  | p1028 | p1032 | p1036 | p1040 | p1044 | p1048 | p1052 | p1056 | p1060 | p1064
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p952 => (952, 0xf101009f#32)
  | .p956 => (956, 0x5280080c#32)
  | .p960 => (960, 0x9a8c308d#32)
  | .p964 => (964, 0xf10000bf#32)
  | .p968 => (968, 0x1a8c01af#32)
  | .p972 => (972, 0xf101013f#32)
  | .p976 => (976, 0x9280000d#32)
  | .p980 => (980, 0x9a8c3130#32)
  | .p984 => (984, 0xf100011f#32)
  | .p988 => (988, 0x9acf21b2#32)
  | .p992 => (992, 0x1a8c0210#32)
  | .p996 => (996, 0x9ad021b1#32)
  | .p1000 => (1000, 0x7101021f#32)
  | .p1004 => (1004, 0x54000060#32)
  | .p1008 => (1008, 0xaa3103f0#32)
  | .p1012 => (1012, 0x14000002#32)
  | .p1016 => (1016, 0xaa0d03f0#32)
  | .p1020 => (1020, 0x710101ff#32)
  | .p1024 => (1024, 0x54000060#32)
  | .p1028 => (1028, 0xaa3203ef#32)
  | .p1032 => (1032, 0x14000002#32)
  | .p1036 => (1036, 0xaa0d03ef#32)
  | .p1040 => (1040, 0x9a9203f1#32)
  | .p1044 => (1044, 0x8a0f01ce#32)
  | .p1048 => (1048, 0x8a11020f#32)
  | .p1052 => (1052, 0xaa0f01ce#32)
  | .p1056 => (1056, 0xf900016e#32)
  | .p1060 => (1060, 0x5280002e#32)
  | .p1064 => (1064, 0xb5000d61#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def cmp64 (left right : BitVec 64) (s : ArmState) : ArmState :=
  write_pstate (AddWithCarry left (~~~right) 1#1).2 (next s)

def cmp32 (left right : BitVec 32) (s : ArmState) : ArmState :=
  write_pstate (AddWithCarry left (~~~right) 1#1).2 (next s)

def branch (condition : Prop) [Decidable condition] (offset : BitVec 64)
    (s : ArmState) : ArmState :=
  w .PC (read_pc s + if condition then offset else 4#64) s

def Op.effect : Op → ArmState → ArmState
  | .p952, s => cmp64 (r (.GPR 4#5) s) 64 s
  | .p956, s => put 12 64 s
  | .p960, s => put 13 (if r (.FLAG .C) s = 0#1 then r (.GPR 4#5) s else r (.GPR 12#5) s) s
  | .p964, s => cmp64 (r (.GPR 5#5) s) 0 s
  | .p968, s => put 15 ((if r (.FLAG .Z) s = 1#1 then (r (.GPR 13#5) s).setWidth 32
      else (r (.GPR 12#5) s).setWidth 32).setWidth 64) s
  | .p972, s => cmp64 (r (.GPR 9#5) s) 64 s
  | .p976, s => put 13 (-1) s
  | .p980, s => put 16 (if r (.FLAG .C) s = 0#1 then r (.GPR 9#5) s else r (.GPR 12#5) s) s
  | .p984, s => cmp64 (r (.GPR 8#5) s) 0 s
  | .p988, s => put 18 (r (.GPR 13#5) s <<< ((r (.GPR 15#5) s).toNat % 64)) s
  | .p992, s => put 16 ((if r (.FLAG .Z) s = 1#1 then (r (.GPR 16#5) s).setWidth 32
      else (r (.GPR 12#5) s).setWidth 32).setWidth 64) s
  | .p996, s => put 17 (r (.GPR 13#5) s <<< ((r (.GPR 16#5) s).toNat % 64)) s
  | .p1000, s => cmp32 ((r (.GPR 16#5) s).setWidth 32) 64 s
  | .p1004, s | .p1024, s => branch (r (.FLAG .Z) s = 1#1) 12 s
  | .p1008, s => put 16 (~~~r (.GPR 17#5) s) s
  | .p1012, s | .p1032, s => w .PC (read_pc s + 8#64) s
  | .p1016, s => put 16 (r (.GPR 13#5) s) s
  | .p1020, s => cmp32 ((r (.GPR 15#5) s).setWidth 32) 64 s
  | .p1028, s => put 15 (~~~r (.GPR 18#5) s) s
  | .p1036, s => put 15 (r (.GPR 13#5) s) s
  | .p1040, s => put 17 (if r (.FLAG .Z) s = 1#1 then 0 else r (.GPR 18#5) s) s
  | .p1044, s => put 14 (r (.GPR 14#5) s &&& r (.GPR 15#5) s) s
  | .p1048, s => put 15 (r (.GPR 16#5) s &&& r (.GPR 17#5) s) s
  | .p1052, s => put 14 (r (.GPR 14#5) s ||| r (.GPR 15#5) s) s
  | .p1056, s => next (write_mem_bytes 8 (r (.GPR 11#5) s) (r (.GPR 14#5) s) s)
  | .p1060, s => put 14 1 s
  | .p1064, s => branch (r (.GPR 1#5) s ≠ 0#64) 428 s

private theorem signed_shift_remainder (number : Nat) :
    (((number : Int).bmod 18446744073709551616 % 64 % 64).toNat) = number % 64 := by
  rw [Int.bmod_def]
  split <;> omega

/-- Each equation uses the literal linked opcode, including the whole-limb
branches and the first committed output write. -/
theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.Rebase.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) : stepi s = op.effect s := by
  have fetched : fetch_inst (base + BitVec.ofNat 64 op.row.1) s = some op.row.2 := by
    rw [fetch_inst_from_program]
    cases op
    all_goals first
      | exact Linked.Rebase.chunk3_codeAt code _ (by decide)
      | exact Linked.Rebase.chunk4_codeAt code _ (by decide)
  have carry : r (.FLAG .C) s ≠ 1#1 ↔ r (.FLAG .C) s = 0#1 := by bv_omega
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc fetched rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, cmp64, cmp32, branch, exec_inst,
        state_simp_rules, bitvec_rules, minimal_theory, carry, signed_shift_remainder]
  all_goals first | rfl | exact w_of_w_commute (by decide) | (split <;> simp_all)

@[simp] theorem Op.program (op : Op) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, cmp64, cmp32, branch, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, cmp64, cmp32, branch, state_simp_rules]

/-- The scratch mask includes X18: it is not an AAPCS callee-save register. -/
theorem Op.callee (op : Op) (s : ArmState) (reg : BitVec 5)
    (lower : 19 ≤ reg.toNat) : r (.GPR reg) (op.effect s) = r (.GPR reg) s := by
  have n12 : reg ≠ 12#5 := by intro h; subst reg; contradiction
  have n13 : reg ≠ 13#5 := by intro h; subst reg; contradiction
  have n14 : reg ≠ 14#5 := by intro h; subst reg; contradiction
  have n15 : reg ≠ 15#5 := by intro h; subst reg; contradiction
  have n16 : reg ≠ 16#5 := by intro h; subst reg; contradiction
  have n17 : reg ≠ 17#5 := by intro h; subst reg; contradiction
  have n18 : reg ≠ 18#5 := by intro h; subst reg; contradiction
  cases op <;> simp [Op.effect, put, next, cmp64, cmp32, branch, state_simp_rules,
    n12, n13, n14, n15, n16, n17, n18]

@[simp] theorem Op.simd (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, put, next, cmp64, cmp32, branch, state_simp_rules]

end SszArm.Indices.Rebase.Fill.Mask
