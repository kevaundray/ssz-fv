import SszArm.BoolExec

namespace SszArm.BoolCodec

open BitVec

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Distinct nonbranch instructions in the shipped Boolean decoder body. -/
inductive StoreOp where
  -- 628–680
  | movW8_256
  | subSp32
  | strX9Sp
  | strX10Sp8
  | strX11Sp16
  | addX9X0_0
  | addX9X9_16
  | lsrW11W8_8
  | strbW8X9
  | strbW11X9_1
  | ldrX11Sp16
  | ldrX10Sp8
  | ldrX9Sp
  | addSp32
  -- 2084–2240
  | movW8_1
  | movW9_3
  | subSp16
  | addSp16
  | movX10_0
  | strX10X9
  | strX10X9_8
  | addX9X9_56
  | strX8X9
  | addX9X9_32
  | strX3X0_48
  | strW9X0_72
  | stpX8X8X0
  -- 4084–4292
  | movW10_0
  | lsrW11W10_8
  | strbW10X9
  | addX9X9_40
  | strX8X0_32
  | movW8_13
deriving DecidableEq, Repr

/-- Word encoding for each distinct shipped opcode. -/
def StoreOp.word : StoreOp → BitVec 32
  | .movW8_256 => 0x52802008#32
  | .subSp32 => 0xd10083ff#32
  | .strX9Sp => 0xf90003e9#32
  | .strX10Sp8 => 0xf90007ea#32
  | .strX11Sp16 => 0xf9000beb#32
  | .addX9X0_0 => 0x91000009#32
  | .addX9X9_16 => 0x91004129#32
  | .lsrW11W8_8 => 0x53087d0b#32
  | .strbW8X9 => 0x39000128#32
  | .strbW11X9_1 => 0x3900052b#32
  | .ldrX11Sp16 => 0xf9400beb#32
  | .ldrX10Sp8 => 0xf94007ea#32
  | .ldrX9Sp => 0xf94003e9#32
  | .addSp32 => 0x910083ff#32
  | .movW8_1 => 0x52800028#32
  | .movW9_3 => 0x52800069#32
  | .subSp16 => 0xd10043ff#32
  | .addSp16 => 0x910043ff#32
  | .movX10_0 => 0xd280000a#32
  | .strX10X9 => 0xf900012a#32
  | .strX10X9_8 => 0xf900052a#32
  | .addX9X9_56 => 0x9100e129#32
  | .strX8X9 => 0xf9000128#32
  | .addX9X9_32 => 0x91008129#32
  | .strX3X0_48 => 0xf9001803#32
  | .strW9X0_72 => 0xb9004809#32
  | .stpX8X8X0 => 0xa9002008#32
  | .movW10_0 => 0x5280000a#32
  | .lsrW11W10_8 => 0x53087d4b#32
  | .strbW10X9 => 0x3900012a#32
  | .addX9X9_40 => 0x9100a129#32
  | .strX8X0_32 => 0xf9001008#32
  | .movW8_13 => 0x528001a8#32

/-- Exact small-step state effect for each distinct shipped opcode. -/
def StoreOp.effect : StoreOp → ArmState → ArmState
  | .movW8_256 => fun s =>
      w .PC (read_pc s + 4#64) (w (.GPR 8) 256#64 s)
  | .subSp32 => fun s =>
      w (.GPR 31) (r (.GPR 31) s - 32#64) (w .PC (read_pc s + 4#64) s)
  | .strX9Sp => fun s =>
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 8 (r (.GPR 31) s) (r (.GPR 9) s) s)
  | .strX10Sp8 => fun s =>
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 8 (r (.GPR 31) s + 8#64) (r (.GPR 10) s) s)
  | .strX11Sp16 => fun s =>
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 8 (r (.GPR 31) s + 16#64) (r (.GPR 11) s) s)
  | .addX9X0_0 => fun s =>
      w (.GPR 9) (r (.GPR 0) s + 0#64) (w .PC (read_pc s + 4#64) s)
  | .addX9X9_16 => fun s =>
      w (.GPR 9) (r (.GPR 9) s + 16#64) (w .PC (read_pc s + 4#64) s)
  | .lsrW11W8_8 => fun s =>
      w (.GPR 11) ((((r (.GPR 8) s).setWidth 32) >>> 8).setWidth 64)
        (w .PC (read_pc s + 4#64) s)
  | .strbW8X9 => fun s =>
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 1 (r (.GPR 9) s) ((r (.GPR 8) s).setWidth 8) s)
  | .strbW11X9_1 => fun s =>
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 1 (r (.GPR 9) s + 1#64) ((r (.GPR 11) s).setWidth 8) s)
  | .ldrX11Sp16 => fun s =>
      w .PC (read_pc s + 4#64)
        (w (.GPR 11) (read_mem_bytes 8 (r (.GPR 31) s + 16#64) s) s)
  | .ldrX10Sp8 => fun s =>
      w .PC (read_pc s + 4#64)
        (w (.GPR 10) (read_mem_bytes 8 (r (.GPR 31) s + 8#64) s) s)
  | .ldrX9Sp => fun s =>
      w .PC (read_pc s + 4#64)
        (w (.GPR 9) (read_mem_bytes 8 (r (.GPR 31) s) s) s)
  | .addSp32 => fun s =>
      w (.GPR 31) (r (.GPR 31) s + 32#64) (w .PC (read_pc s + 4#64) s)
  | .movW8_1 => fun s =>
      w .PC (read_pc s + 4#64) (w (.GPR 8) 1#64 s)
  | .movW9_3 => fun s =>
      w .PC (read_pc s + 4#64) (w (.GPR 9) 3#64 s)
  | .subSp16 => fun s =>
      w (.GPR 31) (r (.GPR 31) s - 16#64) (w .PC (read_pc s + 4#64) s)
  | .addSp16 => fun s =>
      w (.GPR 31) (r (.GPR 31) s + 16#64) (w .PC (read_pc s + 4#64) s)
  | .movX10_0 => fun s =>
      w .PC (read_pc s + 4#64) (w (.GPR 10) 0#64 s)
  | .strX10X9 => fun s =>
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 8 (r (.GPR 9) s) (r (.GPR 10) s) s)
  | .strX10X9_8 => fun s =>
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 8 (r (.GPR 9) s + 8#64) (r (.GPR 10) s) s)
  | .addX9X9_56 => fun s =>
      w (.GPR 9) (r (.GPR 9) s + 56#64) (w .PC (read_pc s + 4#64) s)
  | .strX8X9 => fun s =>
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 8 (r (.GPR 9) s) (r (.GPR 8) s) s)
  | .addX9X9_32 => fun s =>
      w (.GPR 9) (r (.GPR 9) s + 32#64) (w .PC (read_pc s + 4#64) s)
  | .strX3X0_48 => fun s =>
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 8 (r (.GPR 0) s + 48#64) (r (.GPR 3) s) s)
  | .strW9X0_72 => fun s =>
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 4 (r (.GPR 0) s + 72#64) ((r (.GPR 9) s).setWidth 32) s)
  | .stpX8X8X0 => fun s =>
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 16 (r (.GPR 0) s) ((r (.GPR 8) s) ++ (r (.GPR 8) s)) s)
  | .movW10_0 => fun s =>
      w .PC (read_pc s + 4#64) (w (.GPR 10) 0#64 s)
  | .lsrW11W10_8 => fun s =>
      w (.GPR 11) ((((r (.GPR 10) s).setWidth 32) >>> 8).setWidth 64)
        (w .PC (read_pc s + 4#64) s)
  | .strbW10X9 => fun s =>
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 1 (r (.GPR 9) s) ((r (.GPR 10) s).setWidth 8) s)
  | .addX9X9_40 => fun s =>
      w (.GPR 9) (r (.GPR 9) s + 40#64) (w .PC (read_pc s + 4#64) s)
  | .strX8X0_32 => fun s =>
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 8 (r (.GPR 0) s + 32#64) (r (.GPR 8) s) s)
  | .movW8_13 => fun s =>
      w .PC (read_pc s + 4#64) (w (.GPR 8) 13#64 s)

private theorem lsr_mask (x : BitVec 32) :
    (x.rotateRight 8).setWidth 64 &&& 4294967295#64 &&& 16777215#64 =
      x.setWidth 64 >>> 8 := by
  rw [show 4294967295#64 = (BitVec.allOnes 32).setWidth 64 by decide,
    show 16777215#64 = (BitVec.allOnes 24).setWidth 64 by decide]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 24
  · simp [h, hi, show i < 32 by omega, show 8 + i < 64 by omega]
  · have hx : x.getLsbD (8 + i) = false := BitVec.getLsbD_of_ge x (8 + i) (by omega)
    simp [h, hi, hx]

/-- Decoding and executing each distinct shipped opcode, with alignment checked
for the stack-based loads/stores. -/
theorem step_word (s : ArmState) (op : StoreOp)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some op.word) :
    stepi s = op.effect s := by
  cases op
  all_goals
    simp only [StoreOp.word] at hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true})
      [StoreOp.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha]
  all_goals try rfl
  all_goals
    rw [lsr_mask]
    exact w_of_w_commute (by decide)

end SszArm.BoolCodec
