import SszArm.MeasureResultBlock
import SszArm.MeasureBitsWidthMath

namespace SszArm.Measure.Bits.Width

open Result

def p1852 : Op := ⟨1852, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1856 : Op := ⟨1856, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1860 : Op := ⟨1860, 0xd343ff49#32,
  .DPI (.Bitfield { sf := 1, opc := 2, N := 1, immr := 3, imms := 63, Rn := 26, Rd := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1864 : Op := ⟨1864, 0xaa19f528#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 25, imm6 := 61, Rn := 9, Rd := 8 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1868 : Op := ⟨1868, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1872 : Op := ⟨1872, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1876 : Op := ⟨1876, 0xd343ff29#32,
  .DPI (.Bitfield { sf := 1, opc := 2, N := 1, immr := 3, imms := 63, Rn := 25, Rd := 9 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1880 : Op := ⟨1880, 0x9101e3e0#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 120, Rn := 31, Rd := 0 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1884 : Op := ⟨1884, 0xaa1403e4#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 20, imm6 := 0, Rn := 31, Rd := 4 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1888 : Op := ⟨1888, 0x9101e3f7#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 120, Rn := 31, Rd := 23 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1892 : Op := ⟨1892, 0xb1000502#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 1, sh := 0, imm12 := 1, Rn := 8, Rd := 2 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1896 : Op := ⟨1896, 0x54000062#32,
  .BR (.Cond_branch_imm { imm19 := 3, o0 := 0, cond := 2 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1900 : Op := ⟨1900, 0xaa0903e3#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 9, imm6 := 0, Rn := 31, Rd := 3 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1904 : Op := ⟨1904, 0x14000002#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 2 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1908 : Op := ⟨1908, 0x91000523#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 1, Rn := 9, Rd := 3 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩

end SszArm.Measure.Bits.Width
