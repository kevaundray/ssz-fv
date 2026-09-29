import SszArm.CodecFixedMeasureOpsCommon
import SszArm.CodecLinkedMeasureFixed

namespace SszArm.Codec.Fixed.MeasureFixed.Vector

open Dispatch.Block (next put branch)
open IsFixed (loadPair)

inductive Op where
  | p68 | p72 | p76 | p80 | p84 | p88 | p92 | p96 | p100 | p104
  | p108 | p112 | p116 | p120 | p124 | p128 | p132 | p136 | p140
  | p544 | p548 | p552 | p556 | p560 | p564 | p568 | p572 | p576 | p580
  | p584 | p588 | p592 | p596 | p600 | p604 | p608 | p612 | p616 | p620
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p68 => (68, 0xaa0103f9#32)
  | .p72 => (72, 0xf9400c21#32)
  | .p76 => (76, 0x910023e0#32)
  | .p80 => (80, 0xaa1403e2#32)
  | .p84 => (84, 0x910023fa#32)
  | .p88 => (88, 0x97ffffea#32)
  | .p92 => (92, 0xa940dbf7#32)
  | .p96 => (96, 0xb9404bf8#32)
  | .p100 => (100, 0xf9400ff5#32)
  | .p104 => (104, 0x34000dd8#32)
  | .p108 => (108, 0x91006260#32)
  | .p112 => (112, 0x91006341#32)
  | .p116 => (116, 0x52800502#32)
  | .p120 => (120, 0x94005a61#32)
  | .p124 => (124, 0xb9404fe8#32)
  | .p128 => (128, 0xa900d676#32)
  | .p132 => (132, 0xf9000277#32)
  | .p136 => (136, 0x29082278#32)
  | .p140 => (140, 0x14000090#32)
  | .p544 => (544, 0xd10043ff#32)
  | .p548 => (548, 0xf90003e9#32)
  | .p552 => (552, 0x120002e9#32)
  | .p556 => (556, 0x34000089#32)
  | .p560 => (560, 0xf94003e9#32)
  | .p564 => (564, 0x910043ff#32)
  | .p568 => (568, 0x14000004#32)
  | .p572 => (572, 0xf94003e9#32)
  | .p576 => (576, 0x910043ff#32)
  | .p580 => (580, 0x1400000f#32)
  | .p584 => (584, 0xa9409323#32)
  | .p588 => (588, 0x910023e0#32)
  | .p592 => (592, 0xaa1603e1#32)
  | .p596 => (596, 0xaa1503e2#32)
  | .p600 => (600, 0xaa1403e5#32)
  | .p604 => (604, 0x910023f7#32)
  | .p608 => (608, 0x97ffb6d2#32)
  | .p612 => (612, 0xa940dbf5#32)
  | .p616 => (616, 0xb9404bf4#32)
  | .p620 => (620, 0x35fffcb4#32)

def Op.effect : Op → ArmState → ArmState
  | .p68, s => put 25 (r (.GPR 1#5) s) s
  | .p72, s => put 1 (read_mem_bytes 8 (r (.GPR 1#5) s + 24#64) s) s
  | .p76, s | .p588, s => put 0 (r (.GPR 31#5) s + 8#64) s
  | .p80, s => put 2 (r (.GPR 20#5) s) s
  | .p84, s => put 26 (r (.GPR 31#5) s + 8#64) s
  | .p88, s => call (-88#64) s
  | .p92, s => loadPair 23 22 31 8#64 s
  | .p96, s => load32 24 31 72#64 s
  | .p100, s => put 21 (read_mem_bytes 8 (r (.GPR 31#5) s + 24#64) s) s
  | .p104, s => branch ((r (.GPR 24#5) s).setWidth 32 = 0#32) 440#64 s
  | .p108, s => put 0 (r (.GPR 19#5) s + 24#64) s
  | .p112, s => put 1 (r (.GPR 26#5) s + 24#64) s
  | .p116, s => put 2 40#64 s
  | .p120, s => call 92548#64 s
  | .p124, s => load32 8 31 76#64 s
  | .p128, s => storePair 22 21 19 8#64 s
  | .p132, s => next (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 23#5) s) s)
  | .p136, s => storePair32 24 8 19 64#64 s
  | .p140, s => w .PC (read_pc s + 576#64) s
  | .p544, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p548, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p552, s => put 9 (((r (.GPR 23#5) s).setWidth 32 &&& 1#32).setWidth 64) s
  | .p556, s => branch ((r (.GPR 9#5) s).setWidth 32 = 0#32) 16#64 s
  | .p560, s | .p572, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p564, s | .p576, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p568, s => w .PC (read_pc s + 16#64) s
  | .p580, s => w .PC (read_pc s + 60#64) s
  | .p584, s => loadPair 3 4 25 8#64 s
  | .p592, s => put 1 (r (.GPR 22#5) s) s
  | .p596, s => put 2 (r (.GPR 21#5) s) s
  | .p600, s => put 5 (r (.GPR 20#5) s) s
  | .p604, s => put 23 (r (.GPR 31#5) s + 8#64) s
  | .p608, s => call (-74936#64) s
  | .p612, s => loadPair 21 22 31 8#64 s
  | .p616, s => load32 20 31 72#64 s
  | .p620, s => branch ((r (.GPR 20#5) s).setWidth 32 ≠ 0#32) (-108#64) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureFixed.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched : s.program.find? (base + BitVec.ofNat 64 op.row.1) = some op.row.2 := by
    cases op
    all_goals first
      | exact Linked.MeasureFixed.chunk0_codeAt code _ (by decide)
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

end SszArm.Codec.Fixed.MeasureFixed.Vector
