import SszArm.MeasureResultFields

namespace SszArm.Measure.Bits.Limit

open Result

def p1748 : Op :=
  ⟨1748, Result.p4064.word, Result.p4064.instruction, Result.p4064.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1752 : Op :=
  ⟨1752, Result.p4068.word, Result.p4068.instruction, Result.p4068.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1756 : Op :=
  ⟨1756, Result.p4072.word, Result.p4072.instruction, Result.p4072.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1760 : Op :=
  ⟨1760, Result.p4076.word, Result.p4076.instruction, Result.p4076.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1764 : Op :=
  ⟨1764, Result.p4080.word, Result.p4080.instruction, Result.p4080.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1768 : Op :=
  ⟨1768, Result.p4084.word, Result.p4084.instruction, Result.p4084.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1772 : Op :=
  ⟨1772, Result.p4088.word, Result.p4088.instruction, Result.p4088.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1776 : Op :=
  ⟨1776, Result.p4092.word, Result.p4092.instruction, Result.p4092.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1780 : Op :=
  ⟨1780, Result.p4096.word, Result.p4096.instruction, Result.p4096.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1784 : Op :=
  ⟨1784, Result.p4100.word, Result.p4100.instruction, Result.p4100.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1788 : Op :=
  ⟨1788, Result.p4104.word, Result.p4104.instruction, Result.p4104.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1792 : Op :=
  ⟨1792, Result.p4108.word, Result.p4108.instruction, Result.p4108.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1796 : Op :=
  ⟨1796, Result.p3976.word, Result.p3976.instruction, Result.p3976.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1800 : Op :=
  ⟨1800, Result.p3980.word, Result.p3980.instruction, Result.p3980.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1804 : Op :=
  ⟨1804, Result.p3984.word, Result.p3984.instruction, Result.p3984.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1808 : Op :=
  ⟨1808, Result.p3988.word, Result.p3988.instruction, Result.p3988.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1812 : Op :=
  ⟨1812, Result.p3992.word, Result.p3992.instruction, Result.p3992.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1816 : Op :=
  ⟨1816, Result.p3996.word, Result.p3996.instruction, Result.p3996.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1820 : Op :=
  ⟨1820, Result.p4000.word, Result.p4000.instruction, Result.p4000.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1824 : Op :=
  ⟨1824, Result.p4004.word, Result.p4004.instruction, Result.p4004.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1828 : Op :=
  ⟨1828, Result.p4008.word, Result.p4008.instruction, Result.p4008.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1832 : Op :=
  ⟨1832, Result.p4012.word, Result.p4012.instruction, Result.p4012.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩

def reservedOps : List Op := [p1748, p1752, p1756, p1760, p1764, p1768, p1772, p1776, p1780, p1784, p1788, p1792]
def headerOps : List Op := [p1796, p1800, p1804, p1808, p1812, p1816, p1820, p1824, p1828, p1832]

def p1744 : Op :=
  ⟨1744, Result.p3924.word, Result.p3924.instruction, Result.p3924.decoded,
    by simp only [bodyProgram, List.mem_append]; decide⟩
def p1836 : Op := ⟨1836, 0x52800048#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 2, Rd := 8 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1840 : Op := ⟨1840, 0xa9015e76#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 2, Rt2 := 23, Rn := 19, Rt := 22 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1844 : Op := ⟨1844, 0xa9026275#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 4, Rt2 := 24, Rn := 19, Rt := 21 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩
def p1848 : Op := ⟨1848, 0x14000200#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 512 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩

end SszArm.Measure.Bits.Limit
