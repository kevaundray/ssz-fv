import SszArm.BitVectorBlocks

namespace SszArm.BitVector.Padding

open Block

def p6052 : Op := ⟨6052, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6056 : Op := ⟨6056, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6060 : Op := ⟨6060, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by decide⟩
def p6064 : Op := ⟨6064, 0x910002e9#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 23, Rd := 9 }), by rfl, by decide⟩
def p6068 : Op := ⟨6068, 0x9100e129#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 56, Rn := 9, Rd := 9 }), by rfl, by decide⟩
def p6072 : Op := ⟨6072, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by decide⟩
def p6076 : Op := ⟨6076, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by decide⟩
def p6080 : Op := ⟨6080, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by decide⟩
def p6084 : Op := ⟨6084, 0xf900052a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 9, Rt := 10 }), by rfl, by decide⟩
def p6088 : Op := ⟨6088, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by decide⟩
def p6092 : Op := ⟨6092, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6096 : Op := ⟨6096, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6100 : Op := ⟨6100, 0x528001e8#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 15, Rd := 8 }), by rfl, by decide⟩
def p6104 : Op := ⟨6104, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6108 : Op := ⟨6108, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6112 : Op := ⟨6112, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by decide⟩
def p6116 : Op := ⟨6116, 0x910002e9#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 23, Rd := 9 }), by rfl, by decide⟩
def p6120 : Op := ⟨6120, 0x9100a129#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 40, Rn := 9, Rd := 9 }), by rfl, by decide⟩
def p6124 : Op := ⟨6124, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by decide⟩
def p6128 : Op := ⟨6128, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by decide⟩
def p6132 : Op := ⟨6132, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by decide⟩
def p6136 : Op := ⟨6136, 0xf900052a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 9, Rt := 10 }), by rfl, by decide⟩
def p6140 : Op := ⟨6140, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by decide⟩
def p6144 : Op := ⟨6144, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6148 : Op := ⟨6148, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6152 : Op := ⟨6152, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6156 : Op := ⟨6156, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6160 : Op := ⟨6160, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by decide⟩
def p6164 : Op := ⟨6164, 0x910002e9#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 23, Rd := 9 }), by rfl, by decide⟩
def p6168 : Op := ⟨6168, 0x91006129#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 24, Rn := 9, Rd := 9 }), by rfl, by decide⟩
def p6172 : Op := ⟨6172, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by decide⟩
def p6176 : Op := ⟨6176, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by decide⟩
def p6180 : Op := ⟨6180, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by decide⟩
def p6184 : Op := ⟨6184, 0xf900052a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 9, Rt := 10 }), by rfl, by decide⟩
def p6188 : Op := ⟨6188, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by decide⟩
def p6192 : Op := ⟨6192, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6196 : Op := ⟨6196, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6200 : Op := ⟨6200, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6204 : Op := ⟨6204, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6208 : Op := ⟨6208, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by decide⟩
def p6212 : Op := ⟨6212, 0x910002e9#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 23, Rd := 9 }), by rfl, by decide⟩
def p6216 : Op := ⟨6216, 0x91004129#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 9, Rd := 9 }), by rfl, by decide⟩
def p6220 : Op := ⟨6220, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by decide⟩
def p6224 : Op := ⟨6224, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by decide⟩
def p6228 : Op := ⟨6228, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by decide⟩
def p6232 : Op := ⟨6232, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6236 : Op := ⟨6236, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6240 : Op := ⟨6240, 0x140001f0#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 496 }), by rfl, by decide⟩

inductive Store where
  | third | second | first | text
  deriving DecidableEq

def Store.start : Store → Nat
  | .third => 6052 | .second => 6104 | .first => 6152 | .text => 6200

def Store.displacement : Store → BitVec 64
  | .third => 56 | .second => 40 | .first => 24 | .text => 16

def Store.bodyStart (store : Store) : Nat := store.start + 12

def Store.restoreStart : Store → Nat
  | .third => 6088 | .second => 6140 | .first => 6188 | .text => 6228

def Store.stop : Store → Nat
  | .third => 6100 | .second => 6152 | .first => 6200 | .text => 6240

def Store.saveOps : Store → List Op
  | .third => [p6052, p6056, p6060]
  | .second => [p6104, p6108, p6112]
  | .first => [p6152, p6156, p6160]
  | .text => [p6200, p6204, p6208]

def Store.bodyOps : Store → List Op
  | .third => [p6064, p6068, p6072, p6076, p6080, p6084]
  | .second => [p6116, p6120, p6124, p6128, p6132, p6136]
  | .first => [p6164, p6168, p6172, p6176, p6180, p6184]
  | .text => [p6212, p6216, p6220, p6224]

def Store.restoreOps : Store → List Op
  | .third => [p6088, p6092, p6096]
  | .second => [p6140, p6144, p6148]
  | .first => [p6188, p6192, p6196]
  | .text => [p6228, p6232, p6236]

end SszArm.BitVector.Padding
