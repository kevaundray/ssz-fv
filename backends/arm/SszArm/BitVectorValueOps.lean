import SszArm.BitVectorBlocks
import SszArm.BoolAlignment

namespace SszArm.BitVector.ValueTail

open Block

def p6592 : Op := ⟨6592, 0xb94093e8#32,
  .LDST (.Reg_unsigned_imm { size := 2, V := 0, opc := 1, imm12 := 36, Rn := 31, Rt := 8 }), by rfl, by decide⟩
def p6596 : Op := ⟨6596, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6600 : Op := ⟨6600, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6604 : Op := ⟨6604, 0x12000109#32,
  .DPI (.Logical_imm { sf := 0, opc := 0, N := 0, immr := 0, imms := 0, Rn := 8, Rd := 9 }), by rfl, by decide⟩
def p6608 : Op := ⟨6608, 0x34000089#32,
  .BR (.Compare_branch { sf := 0, op := 0, imm19 := 4, Rt := 9 }), by rfl, by decide⟩
def p6612 : Op := ⟨6612, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6616 : Op := ⟨6616, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6620 : Op := ⟨6620, 0x14000004#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 4 }), by rfl, by decide⟩
def p6624 : Op := ⟨6624, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6628 : Op := ⟨6628, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6632 : Op := ⟨6632, 0x1400010d#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 269 }), by rfl, by decide⟩
def p6636 : Op := ⟨6636, 0xa94a23e9#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 20, Rt2 := 8, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6640 : Op := ⟨6640, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6644 : Op := ⟨6644, 0xf90003eb#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 11 }), by rfl, by decide⟩
def p6648 : Op := ⟨6648, 0xd343fd2b#32,
  .DPI (.Bitfield { sf := 1, opc := 2, N := 1, immr := 3, imms := 63, Rn := 9, Rd := 11 }), by rfl, by decide⟩
def p6652 : Op := ⟨6652, 0xaa08f56a#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 8, imm6 := 61, Rn := 11, Rd := 10 }), by rfl, by decide⟩
def p6656 : Op := ⟨6656, 0xf94003eb#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 11 }), by rfl, by decide⟩
def p6660 : Op := ⟨6660, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6664 : Op := ⟨6664, 0xf240093f#32,
  .DPI (.Logical_imm { sf := 1, opc := 3, N := 1, immr := 0, imms := 2, Rn := 9, Rd := 31 }), by rfl, by decide⟩
def p6668 : Op := ⟨6668, 0xd343fd0b#32,
  .DPI (.Bitfield { sf := 1, opc := 2, N := 1, immr := 3, imms := 63, Rn := 8, Rd := 11 }), by rfl, by decide⟩
def p6672 : Op := ⟨6672, 0x54000061#32,
  .BR (.Cond_branch_imm { imm19 := 3, o0 := 0, cond := 1 }), by rfl, by decide⟩
def p6676 : Op := ⟨6676, 0x5280000c#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 0, Rd := 12 }), by rfl, by decide⟩
def p6680 : Op := ⟨6680, 0x14000002#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 2 }), by rfl, by decide⟩
def p6684 : Op := ⟨6684, 0x5280002c#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 12 }), by rfl, by decide⟩
def p6688 : Op := ⟨6688, 0xab0c014a#32,
  .DPR (.Add_sub_shifted_reg { sf := 1, op := 0, S := 1, shift := 0, Rm := 12, imm6 := 0, Rn := 10, Rd := 10 }), by rfl, by decide⟩
def p6692 : Op := ⟨6692, 0x54000062#32,
  .BR (.Cond_branch_imm { imm19 := 3, o0 := 0, cond := 2 }), by rfl, by decide⟩
def p6696 : Op := ⟨6696, 0xaa0b03eb#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 11, imm6 := 0, Rn := 31, Rd := 11 }), by rfl, by decide⟩
def p6700 : Op := ⟨6700, 0x14000002#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 2 }), by rfl, by decide⟩
def p6704 : Op := ⟨6704, 0x9100056b#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 1, Rn := 11, Rd := 11 }), by rfl, by decide⟩
def p6708 : Op := ⟨6708, 0xca14014a#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 2, shift := 0, N := 0, Rm := 20, imm6 := 0, Rn := 10, Rd := 10 }), by rfl, by decide⟩
def p6712 : Op := ⟨6712, 0xaa0b014a#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 11, imm6 := 0, Rn := 10, Rd := 10 }), by rfl, by decide⟩
def p6716 : Op := ⟨6716, 0xb500260a#32,
  .BR (.Compare_branch { sf := 1, op := 1, imm19 := 304, Rt := 10 }), by rfl, by decide⟩
def p6720 : Op := ⟨6720, 0x5280006a#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 3, Rd := 10 }), by rfl, by decide⟩
def p6724 : Op := ⟨6724, 0xa90252f8#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 4, Rt2 := 20, Rn := 23, Rt := 24 }), by rfl, by decide⟩
def p6728 : Op := ⟨6728, 0x390042ea#32,
  .LDST (.Reg_unsigned_imm { size := 0, V := 0, opc := 0, imm12 := 16, Rn := 23, Rt := 10 }), by rfl, by decide⟩
def p6732 : Op := ⟨6732, 0xa90322e9#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 6, Rt2 := 8, Rn := 23, Rt := 9 }), by rfl, by decide⟩
def p6736 : Op := ⟨6736, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6740 : Op := ⟨6740, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6744 : Op := ⟨6744, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by decide⟩
def p6748 : Op := ⟨6748, 0x910002e9#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 23, Rd := 9 }), by rfl, by decide⟩
def p6752 : Op := ⟨6752, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by decide⟩
def p6756 : Op := ⟨6756, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by decide⟩
def p6760 : Op := ⟨6760, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by decide⟩
def p6764 : Op := ⟨6764, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p6768 : Op := ⟨6768, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by decide⟩
def p6772 : Op := ⟨6772, 0x17fffe02#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 0x3fffe02 }), by rfl, by decide⟩

end SszArm.BitVector.ValueTail
