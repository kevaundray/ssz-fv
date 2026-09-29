import SszArm.CodecFixedMeasureOpsCommon
import SszArm.CodecLinkedMeasureFixed

namespace SszArm.Codec.Fixed.MeasureFixed.Bits

open Dispatch.Block (next put branch)
open IsFixed (loadPair)

inductive Op where
  | p228 | p232 | p236 | p240 | p244 | p248 | p252 | p256 | p260 | p264
  | p268 | p272 | p276 | p280 | p284 | p288 | p292 | p296 | p300 | p304
  | p464 | p468 | p472 | p476 | p480 | p484 | p488 | p492 | p496 | p500
  | p504 | p508 | p512 | p516 | p520 | p524 | p528 | p532 | p536 | p540
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p228 => (228, 0xa9408828#32)
  | .p232 => (232, 0x910023e0#32)
  | .p236 => (236, 0x52800103#32)
  | .p240 => (240, 0xaa1403e4#32)
  | .p244 => (244, 0x910023f9#32)
  | .p248 => (248, 0xaa0803e1#32)
  | .p252 => (252, 0x97ffa832#32)
  | .p256 => (256, 0xa940dbf5#32)
  | .p260 => (260, 0xb9404bf7#32)
  | .p264 => (264, 0xf9400ff8#32)
  | .p268 => (268, 0x34000637#32)
  | .p272 => (272, 0x91006260#32)
  | .p276 => (276, 0x91006321#32)
  | .p280 => (280, 0x52800502#32)
  | .p284 => (284, 0x94005a38#32)
  | .p288 => (288, 0xb9404fe8#32)
  | .p292 => (292, 0xa9005a75#32)
  | .p296 => (296, 0xf9000a78#32)
  | .p300 => (300, 0x29082277#32)
  | .p304 => (304, 0x14000067#32)
  | .p464 => (464, 0xb4000518#32)
  | .p468 => (468, 0x910023e0#32)
  | .p472 => (472, 0xaa1503e1#32)
  | .p476 => (476, 0xaa1603e2#32)
  | .p480 => (480, 0xaa1f03e3#32)
  | .p484 => (484, 0x52800024#32)
  | .p488 => (488, 0xaa1403e5#32)
  | .p492 => (492, 0x910023f7#32)
  | .p496 => (496, 0x97ffb2da#32)
  | .p500 => (500, 0xa940dbf5#32)
  | .p504 => (504, 0xb9404bf4#32)
  | .p508 => (508, 0x340003b4#32)
  | .p512 => (512, 0x91004260#32)
  | .p516 => (516, 0x910042e1#32)
  | .p520 => (520, 0x52800602#32)
  | .p524 => (524, 0x940059fc#32)
  | .p528 => (528, 0xb9404fe8#32)
  | .p532 => (532, 0xa9005a75#32)
  | .p536 => (536, 0x29082274#32)
  | .p540 => (540, 0x1400002c#32)

def Op.effect : Op → ArmState → ArmState
  | .p228, s => loadPair 8 2 1 8#64 s
  | .p232, s | .p468, s => put 0 (r (.GPR 31#5) s + 8#64) s
  | .p236, s => put 3 8#64 s
  | .p240, s => put 4 (r (.GPR 20#5) s) s
  | .p244, s => put 25 (r (.GPR 31#5) s + 8#64) s
  | .p248, s => put 1 (r (.GPR 8#5) s) s
  | .p252, s => call (-89912#64) s
  | .p256, s | .p500, s => loadPair 21 22 31 8#64 s
  | .p260, s => load32 23 31 72#64 s
  | .p264, s => put 24 (read_mem_bytes 8 (r (.GPR 31#5) s + 24#64) s) s
  | .p268, s => branch ((r (.GPR 23#5) s).setWidth 32 = 0#32) 196#64 s
  | .p272, s => put 0 (r (.GPR 19#5) s + 24#64) s
  | .p276, s => put 1 (r (.GPR 25#5) s + 24#64) s
  | .p280, s => put 2 40#64 s
  | .p284, s => call 92384#64 s
  | .p288, s | .p528, s => load32 8 31 76#64 s
  | .p292, s | .p532, s => storePair 21 22 19 0#64 s
  | .p296, s => next (write_mem_bytes 8 (r (.GPR 19#5) s + 16#64) (r (.GPR 24#5) s) s)
  | .p300, s => storePair32 23 8 19 64#64 s
  | .p304, s => w .PC (read_pc s + 412#64) s
  | .p464, s => branch (r (.GPR 24#5) s = 0#64) 160#64 s
  | .p472, s => put 1 (r (.GPR 21#5) s) s
  | .p476, s => put 2 (r (.GPR 22#5) s) s
  | .p480, s => put 3 0#64 s
  | .p484, s => put 4 1#64 s
  | .p488, s => put 5 (r (.GPR 20#5) s) s
  | .p492, s => put 23 (r (.GPR 31#5) s + 8#64) s
  | .p496, s => call (-79000#64) s
  | .p504, s => load32 20 31 72#64 s
  | .p508, s => branch ((r (.GPR 20#5) s).setWidth 32 = 0#32) 116#64 s
  | .p512, s => put 0 (r (.GPR 19#5) s + 16#64) s
  | .p516, s => put 1 (r (.GPR 23#5) s + 16#64) s
  | .p520, s => put 2 48#64 s
  | .p524, s => call 92144#64 s
  | .p536, s => storePair32 20 8 19 64#64 s
  | .p540, s => w .PC (read_pc s + 176#64) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureFixed.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched : s.program.find? (base + BitVec.ofNat 64 op.row.1) = some op.row.2 := by
    cases op
    all_goals first
      | exact Linked.MeasureFixed.chunk0_codeAt code _ (by decide)
      | exact Linked.MeasureFixed.chunk1_codeAt code _ (by decide)
      | exact Linked.MeasureFixed.chunk2_codeAt code _ (by decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true}) [Op.effect, next, put, branch,
      loadPair, load32, storePair, storePair32, call, exec_inst, state_simp_rules,
      bitvec_rules, minimal_theory, aligned, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BoolCodec.pair_read_low, BoolCodec.pair_read_high, apply_ite]
  all_goals first | rfl | exact w_of_w_commute (by decide) | (split <;> simp_all)

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, branch, loadPair, load32, storePair, storePair32, call, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, branch, loadPair, load32, storePair, storePair32, call, state_simp_rules]

end SszArm.Codec.Fixed.MeasureFixed.Bits
