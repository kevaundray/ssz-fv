import SszArm.EmitBitsOps

namespace SszArm.Emit.Bits.Tail

open Dispatch (next branch compare64)
open Activation (put)

inductive Op where
  | p652 | p656 | p660 | p664 | p668 | p672 | p676 | p680 | p684 | p688 | p692
  | p696 | p700 | p704 | p708 | p712 | p716 | p720 | p724 | p728 | p732 | p736
  | p1256 | p1260 | p1264 | p1268 | p1272 | p1276 | p1280 | p1284 | p1288
  | p1292 | p1296 | p1300 | p1304 | p1308 | p1312 | p1316 | p1320 | p1324
  | p1328 | p1332 | p1336 | p1340 | p1344 | p1348 | p1352 | p1356 | p1360 | p1364
  | p1484 | p1488 | p1492 | p1496 | p1500 | p1504 | p1508 | p1512 | p1516
  | p1520 | p1524 | p1528 | p1532 | p1580 | p1584
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p652 => (652, 0x34001a19#32)
  | .p656 => (656, 0xeb17031f#32)
  | .p660 => (660, 0x54002969#32)
  | .p664 => (664, 0x910006e9#32)
  | .p668 => (668, 0xd10043ff#32)
  | .p672 => (672, 0xf90003e9#32)
  | .p676 => (676, 0xaa1703e9#32)
  | .p680 => (680, 0x8b0902c9#32)
  | .p684 => (684, 0x39400128#32)
  | .p688 => (688, 0xf94003e9#32)
  | .p692 => (692, 0x910043ff#32)
  | .p696 => (696, 0xeb18013f#32)
  | .p700 => (700, 0x540000c1#32)
  | .p704 => (704, 0xf2400b49#32)
  | .p708 => (708, 0x54000080#32)
  | .p712 => (712, 0x1280000a#32)
  | .p716 => (716, 0x1ac92149#32)
  | .p720 => (720, 0x0a290108#32)
  | .p724 => (724, 0x52800029#32)
  | .p728 => (728, 0x1ad92129#32)
  | .p732 => (732, 0x2a090108#32)
  | .p736 => (736, 0x140000bc#32)
  | .p1256 => (1256, 0xeb17031f#32)
  | .p1260 => (1260, 0x54000a09#32)
  | .p1264 => (1264, 0xeb1702bf#32)
  | .p1268 => (1268, 0x54001609#32)
  | .p1272 => (1272, 0x910006e9#32)
  | .p1276 => (1276, 0xd10043ff#32)
  | .p1280 => (1280, 0xf90003e9#32)
  | .p1284 => (1284, 0xaa1703e9#32)
  | .p1288 => (1288, 0x8b0902c9#32)
  | .p1292 => (1292, 0x39400128#32)
  | .p1296 => (1296, 0xf94003e9#32)
  | .p1300 => (1300, 0x910043ff#32)
  | .p1304 => (1304, 0xeb18013f#32)
  | .p1308 => (1308, 0x540000c1#32)
  | .p1312 => (1312, 0xf2400b29#32)
  | .p1316 => (1316, 0x54000080#32)
  | .p1320 => (1320, 0x1280000a#32)
  | .p1324 => (1324, 0x1ac92149#32)
  | .p1328 => (1328, 0x0a290108#32)
  | .p1332 => (1332, 0xd10043ff#32)
  | .p1336 => (1336, 0xf90003e9#32)
  | .p1340 => (1340, 0xaa1703e9#32)
  | .p1344 => (1344, 0x8b090289#32)
  | .p1348 => (1348, 0x39000128#32)
  | .p1352 => (1352, 0xf94003e9#32)
  | .p1356 => (1356, 0x910043ff#32)
  | .p1360 => (1360, 0xf9000278#32)
  | .p1364 => (1364, 0x17ffffa6#32)
  | .p1484 => (1484, 0x52800028#32)
  | .p1488 => (1488, 0xeb1702bf#32)
  | .p1492 => (1492, 0x54000f09#32)
  | .p1496 => (1496, 0xd10043ff#32)
  | .p1500 => (1500, 0xf90003e9#32)
  | .p1504 => (1504, 0xaa1703e9#32)
  | .p1508 => (1508, 0x8b090289#32)
  | .p1512 => (1512, 0x39000128#32)
  | .p1516 => (1516, 0xf94003e9#32)
  | .p1520 => (1520, 0x910043ff#32)
  | .p1524 => (1524, 0x910006e8#32)
  | .p1528 => (1528, 0xf9000268#32)
  | .p1532 => (1532, 0x17ffff7c#32)
  | .p1580 => (1580, 0xf9000278#32)
  | .p1584 => (1584, 0x17ffff6f#32)

def lowerOrSame (s : ArmState) : Prop :=
  ¬(r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1)

instance (s : ArmState) : Decidable (lowerOrSame s) := inferInstanceAs (Decidable (¬(_ ∧ _)))

def maskRemainder (reg : BitVec 5) (s : ArmState) : ArmState :=
  let masked := r (.GPR reg) s &&& 7#64
  w (.GPR 9#5) masked (write_pstate (DPI.update_logical_imm_pstate masked) (next s))

def shift32 (source amount : BitVec 64) : BitVec 64 :=
  ((source.setWidth 32) <<< ((amount.setWidth 32).toNat % 32)).setWidth 64

theorem signed_shift_remainder32 (number : Nat) :
    (((number : Int).bmod 4294967296 % 32 % 64).toNat) = number % 32 := by
  rw [Int.bmod_def]
  split <;> omega

private theorem move_not_zero :
    (~~~(BitVec.partInstall 0 16 0#16 0#32)).setWidth 64 = 4294967295#64 := by decide

def Op.effect : Op → ArmState → ArmState
  | .p652, s => branch ((r (.GPR 25#5) s).setWidth 32 = 0#32) 832#64 s
  | .p656, s | .p1256, s => compare64 (r (.GPR 24#5) s) (r (.GPR 23#5) s) s
  | .p660, s => branch (lowerOrSame s) 1324#64 s
  | .p1260, s => branch (lowerOrSame s) 320#64 s
  | .p1264, s | .p1488, s => compare64 (r (.GPR 21#5) s) (r (.GPR 23#5) s) s
  | .p1268, s => branch (lowerOrSame s) 704#64 s
  | .p1492, s => branch (lowerOrSame s) 480#64 s
  | .p664, s | .p1272, s => put 9 (r (.GPR 23#5) s + 1#64) s
  | .p668, s | .p1276, s | .p1332, s | .p1496, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p672, s | .p1280, s | .p1336, s | .p1500, s =>
    next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p676, s | .p1284, s | .p1340, s | .p1504, s => put 9 (r (.GPR 23#5) s) s
  | .p680, s | .p1288, s => put 9 (r (.GPR 22#5) s + r (.GPR 9#5) s) s
  | .p684, s | .p1292, s => put 8 ((read_mem_bytes 1 (r (.GPR 9#5) s) s).setWidth 64) s
  | .p688, s | .p1296, s | .p1352, s | .p1516, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p692, s | .p1300, s | .p1356, s | .p1520, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p696, s | .p1304, s => compare64 (r (.GPR 9#5) s) (r (.GPR 24#5) s) s
  | .p700, s | .p1308, s => branch (r (.FLAG .Z) s ≠ 1#1) 24#64 s
  | .p704, s => maskRemainder 26 s
  | .p1312, s => maskRemainder 25 s
  | .p708, s | .p1316, s => branch (r (.FLAG .Z) s = 1#1) 16#64 s
  | .p712, s | .p1320, s => put 10 4294967295#64 s
  | .p716, s | .p1324, s => put 9 (shift32 (r (.GPR 10#5) s) (r (.GPR 9#5) s)) s
  | .p720, s | .p1328, s =>
    put 8 (((r (.GPR 8#5) s).setWidth 32 &&& ~~~((r (.GPR 9#5) s).setWidth 32)).setWidth 64) s
  | .p724, s => put 9 1#64 s
  | .p728, s => put 9 (shift32 (r (.GPR 9#5) s) (r (.GPR 25#5) s)) s
  | .p732, s =>
    put 8 (((r (.GPR 8#5) s).setWidth 32 ||| (r (.GPR 9#5) s).setWidth 32).setWidth 64) s
  | .p736, s => w .PC (read_pc s + 752#64) s
  | .p1344, s | .p1508, s => put 9 (r (.GPR 20#5) s + r (.GPR 9#5) s) s
  | .p1348, s | .p1512, s =>
    next (write_mem_bytes 1 (r (.GPR 9#5) s) ((r (.GPR 8#5) s).setWidth 8) s)
  | .p1360, s | .p1580, s => next (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 24#5) s) s)
  | .p1364, s => w .PC (read_pc s - 360#64) s
  | .p1484, s => put 8 1#64 s
  | .p1524, s => put 8 (r (.GPR 23#5) s + 1#64) s
  | .p1528, s => next (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 8#5) s) s)
  | .p1532, s => w .PC (read_pc s - 528#64) s
  | .p1584, s => w .PC (read_pc s - 580#64) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) : stepi s = op.effect s := by
  have fetched := body_codeAt code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, Activation.put, Activation.next, Dispatch.next, branch, compare64,
       lowerOrSame, maskRemainder, shift32, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, aligned, BitVec.add_assoc,
       BitVec.sub_eq_add_neg, BitVec.setWidth_eq, apply_ite,
       signed_shift_remainder32, move_not_zero, NatAdd.load_gpr_pc]
  all_goals
    by_cases carry : r (.FLAG .C) s = 1#1 <;>
      by_cases zero : r (.FLAG .Z) s = 0#1 <;>
      by_cases one : r (.FLAG .Z) s = 1#1 <;> simp_all

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, Activation.put, Activation.next, Dispatch.next,
    branch, compare64, maskRemainder, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, Activation.put, Activation.next, Dispatch.next,
    branch, compare64, maskRemainder, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState := ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => CheckSPAlignment s ∧
      read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error follows.1 follows.2.1]
    exact induction _ (by simpa only [CodeAt, Op.program] using code)
      ((op.error s).trans error) follows.2.2

end SszArm.Emit.Bits.Tail
