import SszArm.EmitDispatchOps
import SszArm.EmitActivationOps
import SszArm.BoolMemory
import SszArm.UintShifts
import SszArm.NatAddLoadState

namespace SszArm.Emit.Bits

open Dispatch (next branch compare64)
open Activation (put)

inductive Op where
  | p568 | p572 | p576 | p580 | p584 | p588 | p592 | p596 | p600 | p604
  | p608 | p612 | p616 | p620 | p624 | p628 | p632 | p636 | p640 | p644
  | p1180 | p1184 | p1188 | p1192 | p1196 | p1200 | p1204 | p1208 | p1212
  | p1216 | p1220 | p1224 | p1228 | p1232 | p1236 | p1240 | p1244 | p1248
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p568 => (568, 0xd1001509#32)
  | .p572 => (572, 0xf100093f#32)
  | .p576 => (576, 0x540012e2#32)
  | .p580 => (580, 0xa94222da#32)
  | .p584 => (584, 0xd10043ff#32)
  | .p588 => (588, 0xf90003e9#32)
  | .p592 => (592, 0xd343ff49#32)
  | .p596 => (596, 0xaa08f537#32)
  | .p600 => (600, 0xf94003e9#32)
  | .p604 => (604, 0x910043ff#32)
  | .p608 => (608, 0xeb1702bf#32)
  | .p612 => (612, 0x54002923#32)
  | .p616 => (616, 0xf9400ed8#32)
  | .p620 => (620, 0xeb17031f#32)
  | .p624 => (624, 0x54002943#32)
  | .p628 => (628, 0xf9400ad6#32)
  | .p632 => (632, 0xaa1403e0#32)
  | .p636 => (636, 0xaa1703e2#32)
  | .p640 => (640, 0x12000b59#32)
  | .p644 => (644, 0xaa1603e1#32)
  | .p1180 => (1180, 0xf100111f#32)
  | .p1184 => (1184, 0x54ffe5e1#32)
  | .p1188 => (1188, 0xa94222d9#32)
  | .p1192 => (1192, 0xd10043ff#32)
  | .p1196 => (1196, 0xf90003e9#32)
  | .p1200 => (1200, 0xd343ff29#32)
  | .p1204 => (1204, 0xaa08f537#32)
  | .p1208 => (1208, 0xf94003e9#32)
  | .p1212 => (1212, 0x910043ff#32)
  | .p1216 => (1216, 0xeb1702bf#32)
  | .p1220 => (1220, 0x54001623#32)
  | .p1224 => (1224, 0xf9400ed8#32)
  | .p1228 => (1228, 0xeb17031f#32)
  | .p1232 => (1232, 0x54001643#32)
  | .p1236 => (1236, 0xf9400ad6#32)
  | .p1240 => (1240, 0xaa1403e0#32)
  | .p1244 => (1244, 0xaa1703e2#32)
  | .p1248 => (1248, 0xaa1603e1#32)

def countPair (low : BitVec 5) (s : ArmState) : ArmState :=
  w (.GPR 8#5) (read_mem_bytes 8 (r (.GPR 22#5) s + 40#64) s)
    (put low (read_mem_bytes 8 (r (.GPR 22#5) s + 32#64) s) s)

def Op.effect : Op → ArmState → ArmState
  | .p568, s => put 9 (r (.GPR 8#5) s - 5#64) s
  | .p572, s => compare64 (r (.GPR 9#5) s) 2#64 s
  | .p576, s => branch (r (.FLAG .C) s = 1#1) 604#64 s
  | .p580, s => countPair 26 s
  | .p1188, s => countPair 25 s
  | .p584, s | .p1192, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p588, s | .p1196, s =>
    next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p592, s => put 9 (r (.GPR 26#5) s >>> (3 : Nat)) s
  | .p1200, s => put 9 (r (.GPR 25#5) s >>> (3 : Nat)) s
  | .p596, s | .p1204, s =>
    put 23 (r (.GPR 9#5) s ||| (r (.GPR 8#5) s <<< (61 : Nat))) s
  | .p600, s | .p1208, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p604, s | .p1212, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p608, s | .p1216, s => compare64 (r (.GPR 21#5) s) (r (.GPR 23#5) s) s
  | .p612, s => branch (r (.FLAG .C) s ≠ 1#1) 1316#64 s
  | .p1220, s => branch (r (.FLAG .C) s ≠ 1#1) 708#64 s
  | .p616, s | .p1224, s => put 24 (read_mem_bytes 8 (r (.GPR 22#5) s + 24#64) s) s
  | .p620, s | .p1228, s => compare64 (r (.GPR 24#5) s) (r (.GPR 23#5) s) s
  | .p624, s => branch (r (.FLAG .C) s ≠ 1#1) 1320#64 s
  | .p1232, s => branch (r (.FLAG .C) s ≠ 1#1) 712#64 s
  | .p628, s | .p1236, s => put 22 (read_mem_bytes 8 (r (.GPR 22#5) s + 16#64) s) s
  | .p632, s | .p1240, s => put 0 (r (.GPR 20#5) s) s
  | .p636, s | .p1244, s => put 2 (r (.GPR 23#5) s) s
  | .p640, s => put 25 (((r (.GPR 26#5) s).setWidth 32 &&& 7#32).setWidth 64) s
  | .p644, s | .p1248, s => put 1 (r (.GPR 22#5) s) s
  | .p1180, s => compare64 (r (.GPR 8#5) s) 4#64 s
  | .p1184, s => branch (r (.FLAG .Z) s ≠ 1#1) (-836#64) s

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
      [Op.effect, countPair, Activation.put, Activation.next, Dispatch.next,
       branch, compare64, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       aligned, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
       BitVec.add_assoc, BitVec.sub_eq_add_neg, BitVec.setWidth_eq, apply_ite,
       UintCodec.uint_and_ones, UintCodec.uint_lsr3_mask, NatAdd.load_gpr_pc]
  all_goals first | exact w_of_w_commute (by decide) | (split <;> simp_all)

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, countPair, Activation.put, Activation.next, Dispatch.next,
    branch, compare64, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, countPair, Activation.put, Activation.next, Dispatch.next,
    branch, compare64, state_simp_rules]

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

end SszArm.Emit.Bits
