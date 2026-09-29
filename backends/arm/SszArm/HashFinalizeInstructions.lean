import SszArm.HashContract
import SszArm.BitVectorProgram

namespace SszArm.Hash.Finalize

structure Op where
  offset : Nat
  word : BitVec 32
  instruction : ArmInst
  decoded : decode_raw_inst word = some instruction
  member : (offset, word) ∈ finalizeProgram

def Op.effect (op : Op) (s : ArmState) : ArmState := exec_inst op.instruction s

theorem Op.step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + finalizeOffset + BitVec.ofNat 64 op.offset) :
    stepi s = op.effect s := by
  exact stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans (code.finalize (op.offset, op.word) op.member)) op.decoded

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program :=
  SszArm.BitVector.exec_program op.instruction s

def effect (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun state op => op.effect state) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_err s = .None ∧
      read_pc s = base + finalizeOffset + BitVec.ofNat 64 op.offset ∧
      Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (follows : Follows base ops s) :
    run ops.length s = effect ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
    change run (ops.length + 1) s = effect ops (op.effect s)
    rw [run, op.step s base code follows.1 follows.2.1]
    exact induction _ (code.of_program_eq (op.program s)) follows.2.2

def p0 : Op := ⟨0, 0xd10083ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 32, Rn := 31, Rd := 31 }), rfl, by decide⟩

def p4 : Op := ⟨4, 0xf90003fe#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 30 }), rfl, by decide⟩

def p8 : Op := ⟨8, 0xa9014ff4#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 2, Rt2 := 19, Rn := 31, Rt := 20 }), rfl, by decide⟩

def p12 : Op := ⟨12, 0xf9403028#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 12, Rn := 1, Rt := 8 }), rfl, by decide⟩

def p16 : Op := ⟨16, 0xf100fd1f#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 1, sh := 0, imm12 := 63, Rn := 8, Rd := 31 }), rfl, by decide⟩

def p20 : Op := ⟨20, 0x54001128#32,
  .BR (.Cond_branch_imm { imm19 := 137, o0 := 0, cond := 8 }), rfl, by decide⟩

def p24 : Op := ⟨24, 0x52801009#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 128, Rd := 9 }), rfl, by decide⟩

def p28 : Op := ⟨28, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), rfl, by decide⟩

def p32 : Op := ⟨32, 0xf90003ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 10 }), rfl, by decide⟩

def p36 : Op := ⟨36, 0xaa0803ea#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 8, imm6 := 0, Rn := 31, Rd := 10 }), rfl, by decide⟩

def p40 : Op := ⟨40, 0x8b0a002a#32,
  .DPR (.Add_sub_shifted_reg { sf := 1, op := 0, S := 0, shift := 0, Rm := 10, imm6 := 0, Rn := 1, Rd := 10 }), rfl, by decide⟩

def p44 : Op := ⟨44, 0x39000149#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 0, Rn := 10, Rt := 9 }), rfl, by decide⟩

def p48 : Op := ⟨48, 0xf94003ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 10 }), rfl, by decide⟩

def p52 : Op := ⟨52, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), rfl, by decide⟩

def p56 : Op := ⟨56, 0xaa0003f3#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 0, imm6 := 0, Rn := 31, Rd := 19 }), rfl, by decide⟩

def p60 : Op := ⟨60, 0xf9403028#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 12, Rn := 1, Rt := 8 }), rfl, by decide⟩

def p64 : Op := ⟨64, 0xaa0103f4#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 1, imm6 := 0, Rn := 31, Rd := 20 }), rfl, by decide⟩

def p68 : Op := ⟨68, 0x91000500#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 1, Rn := 8, Rd := 0 }), rfl, by decide⟩

def p72 : Op := ⟨72, 0xf100e01f#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 1, sh := 0, imm12 := 56, Rn := 0, Rd := 31 }), rfl, by decide⟩

def p76 : Op := ⟨76, 0xf9003020#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 12, Rn := 1, Rt := 0 }), rfl, by decide⟩

def p80 : Op := ⟨80, 0x540002c9#32,
  .BR (.Cond_branch_imm { imm19 := 22, o0 := 0, cond := 9 }), rfl, by decide⟩

def p84 : Op := ⟨84, 0xf101001f#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 1, sh := 0, imm12 := 64, Rn := 0, Rd := 31 }), rfl, by decide⟩

def p88 : Op := ⟨88, 0x54000ea8#32,
  .BR (.Cond_branch_imm { imm19 := 117, o0 := 0, cond := 8 }), rfl, by decide⟩

def p92 : Op := ⟨92, 0x528007e9#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 63, Rd := 9 }), rfl, by decide⟩

def p96 : Op := ⟨96, 0x8b000280#32,
  .DPR (.Add_sub_shifted_reg { sf := 1, op := 0, S := 0, shift := 0, Rm := 0, imm6 := 0, Rn := 20, Rd := 0 }), rfl, by decide⟩

def p100 : Op := ⟨100, 0x2a1f03e1#32,
  .DPR (.Logical_shifted_reg { sf := 0, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 1 }), rfl, by decide⟩

def p104 : Op := ⟨104, 0xcb080122#32,
  .DPR (.Add_sub_shifted_reg { sf := 1, op := 1, S := 0, shift := 0, Rm := 8, imm6 := 0, Rn := 9, Rd := 2 }), rfl, by decide⟩

def p108 : Op := ⟨108, 0x94008631#32,
  .BR (.Uncond_branch_imm { op := 1, imm26 := 34353 }), rfl, by decide⟩

def p112 : Op := ⟨112, 0x91010280#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 64, Rn := 20, Rd := 0 }), rfl, by decide⟩

def p116 : Op := ⟨116, 0xaa1403e1#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 20, imm6 := 0, Rn := 31, Rd := 1 }), rfl, by decide⟩

def p120 : Op := ⟨120, 0x97fffeb1#32,
  .BR (.Uncond_branch_imm { op := 1, imm26 := 67108529 }), rfl, by decide⟩

def p124 : Op := ⟨124, 0xaa1f03e0#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 0 }), rfl, by decide⟩

def p128 : Op := ⟨128, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), rfl, by decide⟩

def p132 : Op := ⟨132, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), rfl, by decide⟩

def p136 : Op := ⟨136, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), rfl, by decide⟩

def p140 : Op := ⟨140, 0x91000289#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 20, Rd := 9 }), rfl, by decide⟩

def p144 : Op := ⟨144, 0x91018129#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 96, Rn := 9, Rd := 9 }), rfl, by decide⟩

def p148 : Op := ⟨148, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), rfl, by decide⟩

def p152 : Op := ⟨152, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), rfl, by decide⟩

def p156 : Op := ⟨156, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), rfl, by decide⟩

def p160 : Op := ⟨160, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), rfl, by decide⟩

def p164 : Op := ⟨164, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), rfl, by decide⟩

def p168 : Op := ⟨168, 0x52800708#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 56, Rd := 8 }), rfl, by decide⟩

def p172 : Op := ⟨172, 0x2a1f03e1#32,
  .DPR (.Logical_shifted_reg { sf := 0, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 1 }), rfl, by decide⟩

def p176 : Op := ⟨176, 0xcb000102#32,
  .DPR (.Add_sub_shifted_reg { sf := 1, op := 1, S := 0, shift := 0, Rm := 0, imm6 := 0, Rn := 8, Rd := 2 }), rfl, by decide⟩

def p180 : Op := ⟨180, 0x8b000280#32,
  .DPR (.Add_sub_shifted_reg { sf := 1, op := 0, S := 0, shift := 0, Rm := 0, imm6 := 0, Rn := 20, Rd := 0 }), rfl, by decide⟩

def p184 : Op := ⟨184, 0x9400861e#32,
  .BR (.Uncond_branch_imm { op := 1, imm26 := 34334 }), rfl, by decide⟩

def p188 : Op := ⟨188, 0xf9403688#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 13, Rn := 20, Rt := 8 }), rfl, by decide⟩

def p192 : Op := ⟨192, 0x91010280#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 64, Rn := 20, Rd := 0 }), rfl, by decide⟩

def p196 : Op := ⟨196, 0xaa1403e1#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 20, imm6 := 0, Rn := 31, Rd := 1 }), rfl, by decide⟩

def p200 : Op := ⟨200, 0xd37df108#32,
  .DPI (.Bitfield { sf := 1, opc := 2, N := 1, immr := 61, imms := 60, Rn := 8, Rd := 8 }), rfl, by decide⟩

def p204 : Op := ⟨204, 0xdac00d08#32,
  .DPR (.Data_processing_one_source { sf := 1, S := 0, opcode2 := 0, opcode := 3, Rn := 8, Rd := 8 }), rfl, by decide⟩

def p208 : Op := ⟨208, 0xf9001e88#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 7, Rn := 20, Rt := 8 }), rfl, by decide⟩

def p212 : Op := ⟨212, 0x97fffe9a#32,
  .BR (.Uncond_branch_imm { op := 1, imm26 := 67108506 }), rfl, by decide⟩

def p216 : Op := ⟨216, 0x29482688#32,
  .LDST (.Reg_pair_signed_offset { opc := 0, V := 0, L := 1, imm7 := 16, Rt2 := 9, Rn := 20, Rt := 8 }), rfl, by decide⟩

def p220 : Op := ⟨220, 0xaa1303ea#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 19, imm6 := 0, Rn := 31, Rd := 10 }), rfl, by decide⟩

def p224 : Op := ⟨224, 0x5ac00908#32,
  .DPR (.Data_processing_one_source { sf := 0, S := 0, opcode2 := 0, opcode := 2, Rn := 8, Rd := 8 }), rfl, by decide⟩

def p228 : Op := ⟨228, 0x5ac00929#32,
  .DPR (.Data_processing_one_source { sf := 0, S := 0, opcode2 := 0, opcode := 2, Rn := 9, Rd := 9 }), rfl, by decide⟩

def p232 : Op := ⟨232, 0x39000268#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 0, Rn := 19, Rt := 8 }), rfl, by decide⟩

def p236 : Op := ⟨236, 0x53187d0b#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 24, imms := 31, Rn := 8, Rd := 11 }), rfl, by decide⟩

def p240 : Op := ⟨240, 0x53107d0c#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 16, imms := 31, Rn := 8, Rd := 12 }), rfl, by decide⟩

def p244 : Op := ⟨244, 0x53087d08#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 8, imms := 31, Rn := 8, Rd := 8 }), rfl, by decide⟩

def p248 : Op := ⟨248, 0x9100114a#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 4, Rn := 10, Rd := 10 }), rfl, by decide⟩

def p252 : Op := ⟨252, 0x39000149#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 0, Rn := 10, Rt := 9 }), rfl, by decide⟩

def p256 : Op := ⟨256, 0x39000e6b#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 3, Rn := 19, Rt := 11 }), rfl, by decide⟩

def p260 : Op := ⟨260, 0x53187d2b#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 24, imms := 31, Rn := 9, Rd := 11 }), rfl, by decide⟩

def p264 : Op := ⟨264, 0x53107d2d#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 16, imms := 31, Rn := 9, Rd := 13 }), rfl, by decide⟩

def p268 : Op := ⟨268, 0x39000a6c#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 2, Rn := 19, Rt := 12 }), rfl, by decide⟩

def p272 : Op := ⟨272, 0x39000668#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 1, Rn := 19, Rt := 8 }), rfl, by decide⟩

def p276 : Op := ⟨276, 0x53087d28#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 8, imms := 31, Rn := 9, Rd := 8 }), rfl, by decide⟩

def p280 : Op := ⟨280, 0x2949268c#32,
  .LDST (.Reg_pair_signed_offset { opc := 0, V := 0, L := 1, imm7 := 18, Rt2 := 9, Rn := 20, Rt := 12 }), rfl, by decide⟩

def p284 : Op := ⟨284, 0x39000d4b#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 3, Rn := 10, Rt := 11 }), rfl, by decide⟩

def p288 : Op := ⟨288, 0x3900094d#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 2, Rn := 10, Rt := 13 }), rfl, by decide⟩

def p292 : Op := ⟨292, 0x5ac0098b#32,
  .DPR (.Data_processing_one_source { sf := 0, S := 0, opcode2 := 0, opcode := 2, Rn := 12, Rd := 11 }), rfl, by decide⟩

def p296 : Op := ⟨296, 0x39001668#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 5, Rn := 19, Rt := 8 }), rfl, by decide⟩

def p300 : Op := ⟨300, 0xaa1303e8#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 19, imm6 := 0, Rn := 31, Rd := 8 }), rfl, by decide⟩

def p304 : Op := ⟨304, 0x53187d6a#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 24, imms := 31, Rn := 11, Rd := 10 }), rfl, by decide⟩

def p308 : Op := ⟨308, 0x91002108#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 8, Rn := 8, Rd := 8 }), rfl, by decide⟩

def p312 : Op := ⟨312, 0x3900010b#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 0, Rn := 8, Rt := 11 }), rfl, by decide⟩

def p316 : Op := ⟨316, 0x53107d6c#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 16, imms := 31, Rn := 11, Rd := 12 }), rfl, by decide⟩

def p320 : Op := ⟨320, 0x5ac00929#32,
  .DPR (.Data_processing_one_source { sf := 0, S := 0, opcode2 := 0, opcode := 2, Rn := 9, Rd := 9 }), rfl, by decide⟩

def p324 : Op := ⟨324, 0x39000d0a#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 3, Rn := 8, Rt := 10 }), rfl, by decide⟩

def p328 : Op := ⟨328, 0x53087d6a#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 8, imms := 31, Rn := 11, Rd := 10 }), rfl, by decide⟩

def p332 : Op := ⟨332, 0x3900090c#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 2, Rn := 8, Rt := 12 }), rfl, by decide⟩

def p336 : Op := ⟨336, 0xaa1303e8#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 19, imm6 := 0, Rn := 31, Rd := 8 }), rfl, by decide⟩

def p340 : Op := ⟨340, 0x53107d2c#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 16, imms := 31, Rn := 9, Rd := 12 }), rfl, by decide⟩

def p344 : Op := ⟨344, 0x3900266a#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 9, Rn := 19, Rt := 10 }), rfl, by decide⟩

def p348 : Op := ⟨348, 0x53187d2a#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 24, imms := 31, Rn := 9, Rd := 10 }), rfl, by decide⟩

def p352 : Op := ⟨352, 0x91003108#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 12, Rn := 8, Rd := 8 }), rfl, by decide⟩

def p356 : Op := ⟨356, 0x39000109#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 0, Rn := 8, Rt := 9 }), rfl, by decide⟩

def p360 : Op := ⟨360, 0x53087d29#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 8, imms := 31, Rn := 9, Rd := 9 }), rfl, by decide⟩

def p364 : Op := ⟨364, 0x39000d0a#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 3, Rn := 8, Rt := 10 }), rfl, by decide⟩

def p368 : Op := ⟨368, 0x294a2a8b#32,
  .LDST (.Reg_pair_signed_offset { opc := 0, V := 0, L := 1, imm7 := 20, Rt2 := 10, Rn := 20, Rt := 11 }), rfl, by decide⟩

def p372 : Op := ⟨372, 0x39003669#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 13, Rn := 19, Rt := 9 }), rfl, by decide⟩

def p376 : Op := ⟨376, 0x3900090c#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 2, Rn := 8, Rt := 12 }), rfl, by decide⟩

def p380 : Op := ⟨380, 0xaa1303e8#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 19, imm6 := 0, Rn := 31, Rd := 8 }), rfl, by decide⟩

def p384 : Op := ⟨384, 0x5ac0096b#32,
  .DPR (.Data_processing_one_source { sf := 0, S := 0, opcode2 := 0, opcode := 2, Rn := 11, Rd := 11 }), rfl, by decide⟩

def p388 : Op := ⟨388, 0x5ac0094a#32,
  .DPR (.Data_processing_one_source { sf := 0, S := 0, opcode2 := 0, opcode := 2, Rn := 10, Rd := 10 }), rfl, by decide⟩

def p392 : Op := ⟨392, 0x53187d69#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 24, imms := 31, Rn := 11, Rd := 9 }), rfl, by decide⟩

def p396 : Op := ⟨396, 0x91004108#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 8, Rd := 8 }), rfl, by decide⟩

def p400 : Op := ⟨400, 0x3900010b#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 0, Rn := 8, Rt := 11 }), rfl, by decide⟩

def p404 : Op := ⟨404, 0x53107d6c#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 16, imms := 31, Rn := 11, Rd := 12 }), rfl, by decide⟩

def p408 : Op := ⟨408, 0x39000d09#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 3, Rn := 8, Rt := 9 }), rfl, by decide⟩

def p412 : Op := ⟨412, 0x53087d69#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 8, imms := 31, Rn := 11, Rd := 9 }), rfl, by decide⟩

def p416 : Op := ⟨416, 0x3900090c#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 2, Rn := 8, Rt := 12 }), rfl, by decide⟩

def p420 : Op := ⟨420, 0xaa1303e8#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 19, imm6 := 0, Rn := 31, Rd := 8 }), rfl, by decide⟩

def p424 : Op := ⟨424, 0x53107d4c#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 16, imms := 31, Rn := 10, Rd := 12 }), rfl, by decide⟩

def p428 : Op := ⟨428, 0x39004669#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 17, Rn := 19, Rt := 9 }), rfl, by decide⟩

def p432 : Op := ⟨432, 0x53187d49#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 24, imms := 31, Rn := 10, Rd := 9 }), rfl, by decide⟩

def p436 : Op := ⟨436, 0x91005108#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 20, Rn := 8, Rd := 8 }), rfl, by decide⟩

def p440 : Op := ⟨440, 0x3900010a#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 0, Rn := 8, Rt := 10 }), rfl, by decide⟩

def p444 : Op := ⟨444, 0x39000d09#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 3, Rn := 8, Rt := 9 }), rfl, by decide⟩

def p448 : Op := ⟨448, 0x53087d49#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 8, imms := 31, Rn := 10, Rd := 9 }), rfl, by decide⟩

def p452 : Op := ⟨452, 0x294b2a8b#32,
  .LDST (.Reg_pair_signed_offset { opc := 0, V := 0, L := 1, imm7 := 22, Rt2 := 10, Rn := 20, Rt := 11 }), rfl, by decide⟩

def p456 : Op := ⟨456, 0x39005669#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 21, Rn := 19, Rt := 9 }), rfl, by decide⟩

def p460 : Op := ⟨460, 0x3900090c#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 2, Rn := 8, Rt := 12 }), rfl, by decide⟩

def p464 : Op := ⟨464, 0xaa1303e8#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 19, imm6 := 0, Rn := 31, Rd := 8 }), rfl, by decide⟩

def p468 : Op := ⟨468, 0x5ac0096b#32,
  .DPR (.Data_processing_one_source { sf := 0, S := 0, opcode2 := 0, opcode := 2, Rn := 11, Rd := 11 }), rfl, by decide⟩

def p472 : Op := ⟨472, 0x5ac0094a#32,
  .DPR (.Data_processing_one_source { sf := 0, S := 0, opcode2 := 0, opcode := 2, Rn := 10, Rd := 10 }), rfl, by decide⟩

def p476 : Op := ⟨476, 0x53187d69#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 24, imms := 31, Rn := 11, Rd := 9 }), rfl, by decide⟩

def p480 : Op := ⟨480, 0x91006108#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 24, Rn := 8, Rd := 8 }), rfl, by decide⟩

def p484 : Op := ⟨484, 0x3900010b#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 0, Rn := 8, Rt := 11 }), rfl, by decide⟩

def p488 : Op := ⟨488, 0x53107d6c#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 16, imms := 31, Rn := 11, Rd := 12 }), rfl, by decide⟩

def p492 : Op := ⟨492, 0x39000d09#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 3, Rn := 8, Rt := 9 }), rfl, by decide⟩

def p496 : Op := ⟨496, 0x53087d69#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 8, imms := 31, Rn := 11, Rd := 9 }), rfl, by decide⟩

def p500 : Op := ⟨500, 0x53107d4b#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 16, imms := 31, Rn := 10, Rd := 11 }), rfl, by decide⟩

def p504 : Op := ⟨504, 0x3900090c#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 2, Rn := 8, Rt := 12 }), rfl, by decide⟩

def p508 : Op := ⟨508, 0xaa1303e8#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 19, imm6 := 0, Rn := 31, Rd := 8 }), rfl, by decide⟩

def p512 : Op := ⟨512, 0x39006669#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 25, Rn := 19, Rt := 9 }), rfl, by decide⟩

def p516 : Op := ⟨516, 0x53187d49#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 24, imms := 31, Rn := 10, Rd := 9 }), rfl, by decide⟩

def p520 : Op := ⟨520, 0x91007108#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 28, Rn := 8, Rd := 8 }), rfl, by decide⟩

def p524 : Op := ⟨524, 0x3900010a#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 0, Rn := 8, Rt := 10 }), rfl, by decide⟩

def p528 : Op := ⟨528, 0x39000d09#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 3, Rn := 8, Rt := 9 }), rfl, by decide⟩

def p532 : Op := ⟨532, 0x53087d49#32,
  .DPI (.Bitfield { sf := 0, opc := 2, N := 0, immr := 8, imms := 31, Rn := 10, Rd := 9 }), rfl, by decide⟩

def p536 : Op := ⟨536, 0x3900090b#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 2, Rn := 8, Rt := 11 }), rfl, by decide⟩

def p540 : Op := ⟨540, 0x39007669#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 29, Rn := 19, Rt := 9 }), rfl, by decide⟩

def p544 : Op := ⟨544, 0xa9414ff4#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 2, Rt2 := 19, Rn := 31, Rt := 20 }), rfl, by decide⟩

def p548 : Op := ⟨548, 0xf84207fe#32,
  .LDST (.Reg_imm_post_indexed { size := 3, V := 0, opc := 1, imm9 := 32, Rn := 31, Rt := 30 }), rfl, by decide⟩

def p552 : Op := ⟨552, 0xd65f03c0#32,
  .BR (.Uncond_branch_reg { opc := 2, op2 := 31, op3 := 0, Rn := 30, op4 := 0 }), rfl, by decide⟩

end SszArm.Hash.Finalize
