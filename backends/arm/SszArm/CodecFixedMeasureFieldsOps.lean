import SszArm.CodecFixedMeasureOpsCommon
import SszArm.CodecLinkedMeasureFixed
import SszArm.UintShifts

namespace SszArm.Codec.Fixed.MeasureFixed.Fields

open Dispatch.Block (next put branch)
open IsFixed (loadPair)

inductive Op where
  | p308 | p312 | p316 | p320 | p324 | p328 | p332 | p336 | p340 | p344
  | p348 | p352 | p356 | p360 | p364 | p368 | p372 | p376 | p380 | p384
  | p388 | p392 | p396 | p400 | p404 | p408 | p412 | p416 | p420 | p424
  | p428 | p432 | p436 | p440 | p444 | p448 | p452 | p456 | p460
  | p744 | p748 | p752 | p756 | p760 | p764 | p768 | p772 | p776 | p780
  | p784 | p788 | p792 | p796 | p800 | p804 | p808 | p812 | p816 | p820 | p824
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p308 => (308, 0x52800108#32)
  | .p312 => (312, 0x8b080028#32)
  | .p316 => (316, 0xf9400509#32)
  | .p320 => (320, 0xb4fffc69#32)
  | .p324 => (324, 0x8b090529#32)
  | .p328 => (328, 0xf9400108#32)
  | .p332 => (332, 0xaa1f03f5#32)
  | .p336 => (336, 0xaa1f03f6#32)
  | .p340 => (340, 0xd37df137#32)
  | .p344 => (344, 0x91004118#32)
  | .p348 => (348, 0xf8418701#32)
  | .p352 => (352, 0x910023e0#32)
  | .p356 => (356, 0xaa1403e2#32)
  | .p360 => (360, 0x97ffffa6#32)
  | .p364 => (364, 0xa9408ff9#32)
  | .p368 => (368, 0xb9404bfa#32)
  | .p372 => (372, 0xf9400fe4#32)
  | .p376 => (376, 0x35000b9a#32)
  | .p380 => (380, 0xd10043ff#32)
  | .p384 => (384, 0xf90003e9#32)
  | .p388 => (388, 0x12000329#32)
  | .p392 => (392, 0x34000089#32)
  | .p396 => (396, 0xf94003e9#32)
  | .p400 => (400, 0x910043ff#32)
  | .p404 => (404, 0x14000004#32)
  | .p408 => (408, 0xf94003e9#32)
  | .p412 => (412, 0x910043ff#32)
  | .p416 => (416, 0x14000038#32)
  | .p420 => (420, 0x910023e0#32)
  | .p424 => (424, 0xaa1503e1#32)
  | .p428 => (428, 0xaa1603e2#32)
  | .p432 => (432, 0xaa1403e5#32)
  | .p436 => (436, 0x97ffb2e9#32)
  | .p440 => (440, 0xa940dbf5#32)
  | .p444 => (444, 0xb9404bf9#32)
  | .p448 => (448, 0x35000ad9#32)
  | .p452 => (452, 0xf10062f7#32)
  | .p456 => (456, 0x54fffca1#32)
  | .p460 => (460, 0x14000029#32)
  | .p744 => (744, 0x910023e8#32)
  | .p748 => (748, 0x91006260#32)
  | .p752 => (752, 0x52800502#32)
  | .p756 => (756, 0x91006101#32)
  | .p760 => (760, 0xaa0403f4#32)
  | .p764 => (764, 0xaa0303f5#32)
  | .p768 => (768, 0x940059bf#32)
  | .p772 => (772, 0xb9404fe8#32)
  | .p776 => (776, 0xa900d275#32)
  | .p780 => (780, 0xf9000279#32)
  | .p784 => (784, 0x2908227a#32)
  | .p788 => (788, 0x17ffffee#32)
  | .p792 => (792, 0x910023e8#32)
  | .p796 => (796, 0x91004260#32)
  | .p800 => (800, 0x52800602#32)
  | .p804 => (804, 0x91004101#32)
  | .p808 => (808, 0x940059b5#32)
  | .p812 => (812, 0xb9404fe8#32)
  | .p816 => (816, 0xa9005a75#32)
  | .p820 => (820, 0x29082279#32)
  | .p824 => (824, 0x17ffffe5#32)

def Op.effect : Op → ArmState → ArmState
  | .p308, s => put 8 8#64 s
  | .p312, s => put 8 (r (.GPR 1#5) s + r (.GPR 8#5) s) s
  | .p316, s => put 9 (read_mem_bytes 8 (r (.GPR 8#5) s + 8#64) s) s
  | .p320, s => branch (r (.GPR 9#5) s = 0#64) (-116#64) s
  | .p324, s => put 9 (r (.GPR 9#5) s + (r (.GPR 9#5) s <<< 1)) s
  | .p328, s => put 8 (read_mem_bytes 8 (r (.GPR 8#5) s) s) s
  | .p332, s => put 21 0#64 s
  | .p336, s => put 22 0#64 s
  | .p340, s => put 23 (r (.GPR 9#5) s <<< 3) s
  | .p344, s => put 24 (r (.GPR 8#5) s + 16#64) s
  | .p348, s => next (w (.GPR 24#5) (r (.GPR 24#5) s + 24#64)
      (w (.GPR 1#5) (read_mem_bytes 8 (r (.GPR 24#5) s) s) s))
  | .p352, s | .p420, s => put 0 (r (.GPR 31#5) s + 8#64) s
  | .p356, s => put 2 (r (.GPR 20#5) s) s
  | .p360, s => call (-360#64) s
  | .p364, s => loadPair 25 3 31 8#64 s
  | .p368, s => load32 26 31 72#64 s
  | .p372, s => put 4 (read_mem_bytes 8 (r (.GPR 31#5) s + 24#64) s) s
  | .p376, s => branch ((r (.GPR 26#5) s).setWidth 32 ≠ 0#32) 368#64 s
  | .p380, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p384, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p388, s => put 9 (((r (.GPR 25#5) s).setWidth 32 &&& 1#32).setWidth 64) s
  | .p392, s => branch ((r (.GPR 9#5) s).setWidth 32 = 0#32) 16#64 s
  | .p396, s | .p408, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p400, s | .p412, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p404, s => w .PC (read_pc s + 16#64) s
  | .p416, s => w .PC (read_pc s + 224#64) s
  | .p424, s => put 1 (r (.GPR 21#5) s) s
  | .p428, s => put 2 (r (.GPR 22#5) s) s
  | .p432, s => put 5 (r (.GPR 20#5) s) s
  | .p436, s => call (-78940#64) s
  | .p440, s => loadPair 21 22 31 8#64 s
  | .p444, s => load32 25 31 72#64 s
  | .p448, s => branch ((r (.GPR 25#5) s).setWidth 32 ≠ 0#32) 344#64 s
  | .p452, s => w (.GPR 23#5) (r (.GPR 23#5) s - 24#64)
      (Udivti3.compare (r (.GPR 23#5) s) 24#64 s)
  | .p456, s => branch (r (.FLAG .Z) s ≠ 1#1) (-108#64) s
  | .p460, s => w .PC (read_pc s + 164#64) s
  | .p744, s | .p792, s => put 8 (r (.GPR 31#5) s + 8#64) s
  | .p748, s => put 0 (r (.GPR 19#5) s + 24#64) s
  | .p752, s => put 2 40#64 s
  | .p756, s => put 1 (r (.GPR 8#5) s + 24#64) s
  | .p760, s => put 20 (r (.GPR 4#5) s) s
  | .p764, s => put 21 (r (.GPR 3#5) s) s
  | .p768, s => call 91900#64 s
  | .p772, s | .p812, s => load32 8 31 76#64 s
  | .p776, s => storePair 21 20 19 8#64 s
  | .p780, s => next (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 25#5) s) s)
  | .p784, s => storePair32 26 8 19 64#64 s
  | .p788, s => w .PC (read_pc s - 72#64) s
  | .p796, s => put 0 (r (.GPR 19#5) s + 16#64) s
  | .p800, s => put 2 48#64 s
  | .p804, s => put 1 (r (.GPR 8#5) s + 16#64) s
  | .p808, s => call 91860#64 s
  | .p816, s => storePair 21 22 19 0#64 s
  | .p820, s => storePair32 25 8 19 64#64 s
  | .p824, s => w .PC (read_pc s - 108#64) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureFixed.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched : s.program.find? (base + BitVec.ofNat 64 op.row.1) = some op.row.2 := by
    cases op
    all_goals first
      | exact Linked.MeasureFixed.chunk1_codeAt code _ (by decide)
      | exact Linked.MeasureFixed.chunk2_codeAt code _ (by decide)
      | exact Linked.MeasureFixed.chunk3_codeAt code _ (by decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true}) [Op.effect, next, put, branch,
      loadPair, load32, storePair, storePair32, call, Udivti3.compare, Udivti3.next,
      exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned,
      BitVec.sub_eq_add_neg, BitVec.add_assoc, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
      UintCodec.uint_lsl3_mask, UintCodec.uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, branch, loadPair, load32, storePair, storePair32,
    call, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, branch, loadPair, load32, storePair, storePair32,
    call, Udivti3.compare, Udivti3.next, state_simp_rules]

end SszArm.Codec.Fixed.MeasureFixed.Fields
