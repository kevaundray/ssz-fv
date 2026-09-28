import SszArm.MeasureResultBlock
import SszArm.NatExactEntry

namespace SszArm.Measure.Scalar.Bytes

open Result

def p776 : Op := ⟨776, 0x7100091f#32,
  .DPI (.Add_sub_imm { sf := 0, op := 1, S := 1, sh := 0, imm12 := 2, Rn := 8, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p780 : Op := ⟨780, 0x54006241#32,
  .BR (.Cond_branch_imm { imm19 := 786, o0 := 0, cond := 1 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p784 : Op := ⟨784, 0xf9400ab4#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 2, Rn := 21, Rt := 20 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p788 : Op := ⟨788, 0xa940a428#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 1, Rt2 := 9, Rn := 1, Rt := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p792 : Op := ⟨792, 0xf100029f#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 1, sh := 0, imm12 := 0, Rn := 20, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p796 : Op := ⟨796, 0x54000061#32,
  .BR (.Cond_branch_imm { imm19 := 3, o0 := 0, cond := 1 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p800 : Op := ⟨800, 0x5280000a#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p804 : Op := ⟨804, 0x14000002#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 2 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p808 : Op := ⟨808, 0x5280002a#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p812 : Op := ⟨812, 0xb40023e8#32,
  .BR (.Compare_branch { sf := 1, op := 0, imm19 := 287, Rt := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p816 : Op := ⟨816, 0xd100052b#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 1, Rn := 9, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p820 : Op := ⟨820, 0xb100057f#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 1, sh := 0, imm12 := 1, Rn := 11, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p824 : Op := ⟨824, 0x54002f00#32,
  .BR (.Cond_branch_imm { imm19 := 376, o0 := 0, cond := 0 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p828 : Op := ⟨828, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p832 : Op := ⟨832, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p836 : Op := ⟨836, 0xaa0b03e9#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 11, imm6 := 0, Rn := 31, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p840 : Op := ⟨840, 0xd37df129#32,
  .DPI (.Bitfield { sf := 1, opc := 2, N := 1, immr := 61, imms := 60, Rn := 9, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p844 : Op := ⟨844, 0x8b090109#32,
  .DPR (.Add_sub_shifted_reg { sf := 1, op := 0, S := 0, shift := 0, Rm := 9, imm6 := 0, Rn := 8, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p848 : Op := ⟨848, 0xf940012c#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 9, Rt := 12 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p852 : Op := ⟨852, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p856 : Op := ⟨856, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p860 : Op := ⟨860, 0xd100056b#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 1, Rn := 11, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p864 : Op := ⟨864, 0xb4fffeac#32,
  .BR (.Compare_branch { sf := 1, op := 0, imm19 := 524277, Rt := 12 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p868 : Op := ⟨868, 0x9100096b#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 2, Rn := 11, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p872 : Op := ⟨872, 0x1400016d#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 365 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1156 : Op := ⟨1156, 0x7100091f#32,
  .DPI (.Add_sub_imm { sf := 0, op := 1, S := 1, sh := 0, imm12 := 2, Rn := 8, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1160 : Op := ⟨1160, 0x54005661#32,
  .BR (.Cond_branch_imm { imm19 := 691, o0 := 0, cond := 1 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1164 : Op := ⟨1164, 0xa940a428#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 1, Rt2 := 9, Rn := 1, Rt := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1168 : Op := ⟨1168, 0xf9400ab4#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 2, Rn := 21, Rt := 20 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1172 : Op := ⟨1172, 0xb40023c8#32,
  .BR (.Compare_branch { sf := 1, op := 0, imm19 := 286, Rt := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1176 : Op := ⟨1176, 0xd100052b#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 1, Rn := 9, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1180 : Op := ⟨1180, 0xb100057f#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 1, sh := 0, imm12 := 1, Rn := 11, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1184 : Op := ⟨1184, 0x54003420#32,
  .BR (.Cond_branch_imm { imm19 := 417, o0 := 0, cond := 0 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1188 : Op := ⟨1188, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1192 : Op := ⟨1192, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1196 : Op := ⟨1196, 0xaa0b03e9#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 11, imm6 := 0, Rn := 31, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1200 : Op := ⟨1200, 0xd37df129#32,
  .DPI (.Bitfield { sf := 1, opc := 2, N := 1, immr := 61, imms := 60, Rn := 9, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1204 : Op := ⟨1204, 0x8b090109#32,
  .DPR (.Add_sub_shifted_reg { sf := 1, op := 0, S := 0, shift := 0, Rm := 9, imm6 := 0, Rn := 8, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1208 : Op := ⟨1208, 0xf940012c#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 9, Rt := 12 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1212 : Op := ⟨1212, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1216 : Op := ⟨1216, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1220 : Op := ⟨1220, 0xaa0b03ea#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 11, imm6 := 0, Rn := 31, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1224 : Op := ⟨1224, 0xd100056b#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 1, Rn := 11, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1228 : Op := ⟨1228, 0xb4fffe8c#32,
  .BR (.Compare_branch { sf := 1, op := 0, imm19 := 524276, Rt := 12 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1232 : Op := ⟨1232, 0x9100054a#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 1, Rn := 10, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1236 : Op := ⟨1236, 0xf1000d5f#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 1, sh := 0, imm12 := 3, Rn := 10, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1240 : Op := ⟨1240, 0x54003283#32,
  .BR (.Cond_branch_imm { imm19 := 404, o0 := 0, cond := 3 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1244 : Op := ⟨1244, 0x14000273#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 627 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1960 : Op := ⟨1960, 0xf100029f#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 1, sh := 0, imm12 := 0, Rn := 20, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1964 : Op := ⟨1964, 0x54000061#32,
  .BR (.Cond_branch_imm { imm19 := 3, o0 := 0, cond := 1 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1968 : Op := ⟨1968, 0x5280000a#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1972 : Op := ⟨1972, 0x14000002#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 2 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1976 : Op := ⟨1976, 0x5280002a#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1980 : Op := ⟨1980, 0xf100013f#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 1, sh := 0, imm12 := 0, Rn := 9, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1984 : Op := ⟨1984, 0x54000061#32,
  .BR (.Cond_branch_imm { imm19 := 3, o0 := 0, cond := 1 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1988 : Op := ⟨1988, 0x5280000b#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 0, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1992 : Op := ⟨1992, 0x14000002#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 2 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1996 : Op := ⟨1996, 0x5280002b#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2000 : Op := ⟨2000, 0x4a0a016b#32,
  .DPR (.Logical_shifted_reg { sf := 0, opc := 2, shift := 0, N := 0, Rm := 10, imm6 := 0, Rn := 11, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2004 : Op :=
  { offset := 2004
    word := 0x1a8a13ea#32
    instruction := (decode_raw_inst 0x1a8a13ea#32).get (by decide)
    decoded := (Option.some_get (by decide)).symm
    member := by simp only [bodyProgram, List.mem_append]; decide }
def p2008 : Op := ⟨2008, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2012 : Op := ⟨2012, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2016 : Op := ⟨2016, 0x12000169#32,
  .DPI (.Logical_imm { sf := 0, opc := 0, N := 0, immr := 0, imms := 0, Rn := 11, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2020 : Op := ⟨2020, 0x35000089#32,
  .BR (.Compare_branch { sf := 0, op := 1, imm19 := 4, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2024 : Op := ⟨2024, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2028 : Op := ⟨2028, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2032 : Op := ⟨2032, 0x14000004#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 4 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2036 : Op := ⟨2036, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2040 : Op := ⟨2040, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2044 : Op := ⟨2044, 0x14000056#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 86 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2048 : Op := ⟨2048, 0xaa1f03f5#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 21 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2052 : Op := ⟨2052, 0xb4004174#32,
  .BR (.Compare_branch { sf := 1, op := 0, imm19 := 523, Rt := 20 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2056 : Op := ⟨2056, 0xeb09029f#32,
  .DPR (.Add_sub_shifted_reg { sf := 1, op := 1, S := 1, shift := 0, Rm := 9, imm6 := 0, Rn := 20, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2060 : Op := ⟨2060, 0xaa0903ea#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 9, imm6 := 0, Rn := 31, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2064 : Op := ⟨2064, 0x540009c1#32,
  .BR (.Cond_branch_imm { imm19 := 78, o0 := 0, cond := 1 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2068 : Op := ⟨2068, 0x14000207#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 519 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2316 : Op := ⟨2316, 0xaa1f03eb#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2320 : Op := ⟨2320, 0xaa0903ea#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 9, imm6 := 0, Rn := 31, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2324 : Op := ⟨2324, 0x14000160#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 352 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2328 : Op := ⟨2328, 0xaa1f03eb#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2332 : Op := ⟨2332, 0xeb0a017f#32,
  .DPR (.Add_sub_shifted_reg { sf := 1, op := 1, S := 1, shift := 0, Rm := 10, imm6 := 0, Rn := 11, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2336 : Op := ⟨2336, 0x54000063#32,
  .BR (.Cond_branch_imm { imm19 := 3, o0 := 0, cond := 3 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2340 : Op := ⟨2340, 0x5280000a#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2344 : Op := ⟨2344, 0x14000002#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 2 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2348 : Op := ⟨2348, 0x5280002a#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2352 : Op := ⟨2352, 0x54000121#32,
  .BR (.Cond_branch_imm { imm19 := 9, o0 := 0, cond := 1 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2356 : Op := ⟨2356, 0xb4002b74#32,
  .BR (.Compare_branch { sf := 1, op := 0, imm19 := 347, Rt := 20 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2360 : Op := ⟨2360, 0xb4000109#32,
  .BR (.Compare_branch { sf := 1, op := 0, imm19 := 8, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2364 : Op := ⟨2364, 0xf940010a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 8, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2368 : Op := ⟨2368, 0xeb0a029f#32,
  .DPR (.Add_sub_shifted_reg { sf := 1, op := 1, S := 1, shift := 0, Rm := 10, imm6 := 0, Rn := 20, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2372 : Op := ⟨2372, 0x54002ae0#32,
  .BR (.Cond_branch_imm { imm19 := 343, o0 := 0, cond := 0 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2376 : Op := ⟨2376, 0xeb0a029f#32,
  .DPR (.Add_sub_shifted_reg { sf := 1, op := 1, S := 1, shift := 0, Rm := 10, imm6 := 0, Rn := 20, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2380 : Op := ⟨2380, 0x54002aa9#32,
  .BR (.Cond_branch_imm { imm19 := 341, o0 := 0, cond := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2384 : Op := ⟨2384, 0x14000002#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 2 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2388 : Op := ⟨2388, 0x34002a6a#32,
  .BR (.Compare_branch { sf := 0, op := 0, imm19 := 339, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2852 : Op := ⟨2852, 0xb4001b49#32,
  .BR (.Compare_branch { sf := 1, op := 0, imm19 := 218, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2856 : Op := ⟨2856, 0xf940010a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 8, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2860 : Op := ⟨2860, 0xf100093f#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 1, sh := 0, imm12 := 2, Rn := 9, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2864 : Op := ⟨2864, 0x54000463#32,
  .BR (.Cond_branch_imm { imm19 := 35, o0 := 0, cond := 3 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2868 : Op := ⟨2868, 0xf940050b#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 8, Rt := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2872 : Op := ⟨2872, 0x140000d7#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 215 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2984 : Op := ⟨2984, 0xaa1f03eb#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2988 : Op := ⟨2988, 0x1400000a#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3724 : Op := ⟨3724, 0xaa1f03eb#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3728 : Op := ⟨3728, 0xaa1f03ea#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3732 : Op := ⟨3732, 0xca14014a#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 2, shift := 0, N := 0, Rm := 20, imm6 := 0, Rn := 10, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3736 : Op := ⟨3736, 0xaa0b014a#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 11, imm6 := 0, Rn := 10, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3740 : Op := ⟨3740, 0xb500006a#32,
  .BR (.Compare_branch { sf := 1, op := 1, imm19 := 3, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3744 : Op := ⟨3744, 0xaa1f03f5#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 21 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3748 : Op := ⟨3748, 0x14000063#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 99 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩

end SszArm.Measure.Scalar.Bytes
