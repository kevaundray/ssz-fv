import SszArm.MeasureResultBlock

namespace SszArm.Measure.Bits.ListEntry

open Result

def p684 : Op := ⟨684, 0x71000d1f#32,
  .DPI (.Add_sub_imm { sf := 0, op := 1, S := 1, sh := 0, imm12 := 3, Rn := 8, Rd := 31 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p688 : Op := ⟨688, 0x54006521#32,
  .BR (.Cond_branch_imm { imm19 := 809, o0 := 0, cond := 1 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p692 : Op := ⟨692, 0xa94266ba#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 4, Rt2 := 25, Rn := 21, Rt := 26 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p696 : Op := ⟨696, 0xf9400c37#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 3, Rn := 1, Rt := 23 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p700 : Op := ⟨700, 0xa940d828#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 1, Rt2 := 22, Rn := 1, Rt := 8 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p704 : Op := ⟨704, 0xb50018f9#32,
  .BR (.Compare_branch { sf := 1, op := 1, imm19 := 199, Rt := 25 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p708 : Op := ⟨708, 0xaa1f03f5#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 21 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p712 : Op := ⟨712, 0xaa1a03f8#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 26, imm6 := 0, Rn := 31, Rd := 24 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p716 : Op := ⟨716, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p720 : Op := ⟨720, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p724 : Op := ⟨724, 0x12000109#32,
  .DPI (.Logical_imm { sf := 0, opc := 0, N := 0, immr := 0, imms := 0, Rn := 8, Rd := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p728 : Op := ⟨728, 0x35000089#32,
  .BR (.Compare_branch { sf := 0, op := 1, imm19 := 4, Rt := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p732 : Op := ⟨732, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p736 : Op := ⟨736, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p740 : Op := ⟨740, 0x14000004#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 4 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p744 : Op := ⟨744, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p748 : Op := ⟨748, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p752 : Op := ⟨752, 0x140000f0#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 240 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p756 : Op := ⟨756, 0x14000112#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 274 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1248 : Op := ⟨1248, 0x71000d1f#32,
  .DPI (.Add_sub_imm { sf := 0, op := 1, S := 1, sh := 0, imm12 := 3, Rn := 8, Rd := 31 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1252 : Op := ⟨1252, 0x54005381#32,
  .BR (.Cond_branch_imm { imm19 := 668, o0 := 0, cond := 1 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1256 : Op := ⟨1256, 0xa94266ba#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 4, Rt2 := 25, Rn := 21, Rt := 26 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1260 : Op := ⟨1260, 0xa940dc36#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 1, Rt2 := 23, Rn := 1, Rt := 22 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1264 : Op := ⟨1264, 0xb5000b79#32,
  .BR (.Compare_branch { sf := 1, op := 1, imm19 := 91, Rt := 25 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1268 : Op := ⟨1268, 0xaa1f03f5#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 21 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1272 : Op := ⟨1272, 0xaa1a03f8#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 26, imm6 := 0, Rn := 31, Rd := 24 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1276 : Op := ⟨1276, 0x1400006d#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 109 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1584 : Op := ⟨1584, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1588 : Op := ⟨1588, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1592 : Op := ⟨1592, 0x12000109#32,
  .DPI (.Logical_imm { sf := 0, opc := 0, N := 0, immr := 0, imms := 0, Rn := 8, Rd := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1596 : Op := ⟨1596, 0x34000089#32,
  .BR (.Compare_branch { sf := 0, op := 0, imm19 := 4, Rt := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1600 : Op := ⟨1600, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1604 : Op := ⟨1604, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1608 : Op := ⟨1608, 0x14000004#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 4 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1612 : Op := ⟨1612, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1616 : Op := ⟨1616, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1620 : Op := ⟨1620, 0x1400003a#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 58 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1624 : Op := ⟨1624, 0x14000016#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 22 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1712 : Op := ⟨1712, 0xaa1503e0#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 21, imm6 := 0, Rn := 31, Rd := 0 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1716 : Op := ⟨1716, 0xaa1803e1#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 24, imm6 := 0, Rn := 31, Rd := 1 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1720 : Op := ⟨1720, 0xaa1603e2#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 22, imm6 := 0, Rn := 31, Rd := 2 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1724 : Op := ⟨1724, 0xaa1703e3#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 23, imm6 := 0, Rn := 31, Rd := 3 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1732 : Op := ⟨1732, 0x13001c08#32,
  .DPI (.Bitfield { sf := 0, opc := 0, N := 0, immr := 0, imms := 7, Rn := 0, Rd := 8 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1736 : Op := ⟨1736, 0x7100051f#32,
  .DPI (.Add_sub_imm { sf := 0, op := 1, S := 1, sh := 0, imm12 := 1, Rn := 8, Rd := 31 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1740 : Op := ⟨1740, 0x5400038b#32,
  .BR (.Cond_branch_imm { imm19 := 28, o0 := 0, cond := 11 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩

end SszArm.Measure.Bits.ListEntry
