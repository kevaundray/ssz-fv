import SszArm.CodecFixedOps
import SszArm.CodecLinkedMeasureFixed

namespace SszArm.Codec.Fixed.MeasureFixed.Return

open Dispatch.Block (next put)
open IsFixed (loadPair)

inductive Op where
  | p624 | p628 | p632 | p636 | p640 | p644 | p648 | p652 | p656 | p660
  | p664 | p668 | p672 | p676 | p680 | p684 | p688 | p692 | p696 | p700
  | p704 | p708 | p712 | p716 | p720 | p724 | p728 | p732 | p736 | p740
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p624 => (624, 0x52800028#32)
  | .p628 => (628, 0xa900da75#32)
  | .p632 => (632, 0xf9000268#32)
  | .p636 => (636, 0x1400000a#32)
  | .p640 => (640, 0xd10043ff#32)
  | .p644 => (644, 0xf90003e9#32)
  | .p648 => (648, 0xf90007ea#32)
  | .p652 => (652, 0x91000269#32)
  | .p656 => (656, 0xd280000a#32)
  | .p660 => (660, 0xf900012a#32)
  | .p664 => (664, 0xf94007ea#32)
  | .p668 => (668, 0xf94003e9#32)
  | .p672 => (672, 0x910043ff#32)
  | .p676 => (676, 0xd10043ff#32)
  | .p680 => (680, 0xf90003e9#32)
  | .p684 => (684, 0xf90007ea#32)
  | .p688 => (688, 0x91000269#32)
  | .p692 => (692, 0x91010129#32)
  | .p696 => (696, 0x5280000a#32)
  | .p700 => (700, 0xb900012a#32)
  | .p704 => (704, 0xf94007ea#32)
  | .p708 => (708, 0xf94003e9#32)
  | .p712 => (712, 0x910043ff#32)
  | .p716 => (716, 0xa9494ff4#32)
  | .p720 => (720, 0xf9402bfe#32)
  | .p724 => (724, 0xa94857f6#32)
  | .p728 => (728, 0xa9475ff8#32)
  | .p732 => (732, 0xa94667fa#32)
  | .p736 => (736, 0x910283ff#32)
  | .p740 => (740, 0xd65f03c0#32)

def Op.effect : Op → ArmState → ArmState
  | .p624, s => put 8 1#64 s
  | .p628, s => next (write_mem_bytes 16 (r (.GPR 19#5) s + 8#64)
      (r (.GPR 22#5) s ++ r (.GPR 21#5) s) s)
  | .p632, s => next (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 8#5) s) s)
  | .p636, s => w .PC (read_pc s + 40#64) s
  | .p640, s | .p676, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p644, s | .p680, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p648, s | .p684, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p652, s | .p688, s => put 9 (r (.GPR 19#5) s) s
  | .p656, s | .p696, s => put 10 0#64 s
  | .p660, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p664, s | .p704, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p668, s | .p708, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p672, s | .p712, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p692, s => put 9 (r (.GPR 9#5) s + 64#64) s
  | .p700, s => next (write_mem_bytes 4 (r (.GPR 9#5) s) ((r (.GPR 10#5) s).setWidth 32) s)
  | .p716, s => loadPair 20 19 31 144#64 s
  | .p720, s => put 30 (read_mem_bytes 8 (r (.GPR 31#5) s + 80#64) s) s
  | .p724, s => loadPair 22 21 31 128#64 s
  | .p728, s => loadPair 24 23 31 112#64 s
  | .p732, s => loadPair 26 25 31 96#64 s
  | .p736, s => put 31 (r (.GPR 31#5) s + 160#64) s
  | .p740, s => w .PC (r (.GPR 30#5) s) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureFixed.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := Linked.MeasureFixed.chunk2_codeAt code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true}) [Op.effect, next, put, loadPair,
      exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned,
      BitVec.sub_eq_add_neg, BitVec.add_assoc, BoolCodec.pair_read_low, BoolCodec.pair_read_high]
  all_goals first | rfl | exact w_of_w_commute (by decide)

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, loadPair, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, loadPair, state_simp_rules]

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, next, put, loadPair, state_simp_rules]

end SszArm.Codec.Fixed.MeasureFixed.Return
