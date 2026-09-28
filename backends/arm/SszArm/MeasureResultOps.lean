import SszArm.MeasureResultBlock

namespace SszArm.Measure.Result

def p2392 : Op := ⟨2392, 0x5280002a#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2396 : Op := ⟨2396, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2400 : Op := ⟨2400, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2404 : Op := ⟨2404, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2408 : Op := ⟨2408, 0x91000269#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 19, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2412 : Op := ⟨2412, 0x9100c129#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 48, Rn := 9, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2416 : Op := ⟨2416, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2420 : Op := ⟨2420, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2424 : Op := ⟨2424, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2428 : Op := ⟨2428, 0xf900052a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2432 : Op := ⟨2432, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2436 : Op := ⟨2436, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2440 : Op := ⟨2440, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2444 : Op := ⟨2444, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2448 : Op := ⟨2448, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2452 : Op := ⟨2452, 0xf90007eb#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2456 : Op := ⟨2456, 0x91000269#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 19, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2460 : Op := ⟨2460, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2464 : Op := ⟨2464, 0xd280000b#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2468 : Op := ⟨2468, 0xf900052b#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 9, Rt := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2472 : Op := ⟨2472, 0xf94007eb#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2476 : Op := ⟨2476, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2480 : Op := ⟨2480, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2484 : Op := ⟨2484, 0xa9012668#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 2, Rt2 := 9, Rn := 19, Rt := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2488 : Op := ⟨2488, 0x52800048#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 2, Rd := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p2492 : Op := ⟨2492, 0x14000154#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 340 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3752 : Op := ⟨3752, 0x5280002a#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3756 : Op := ⟨3756, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3760 : Op := ⟨3760, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3764 : Op := ⟨3764, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3768 : Op := ⟨3768, 0x91000269#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 19, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3772 : Op := ⟨3772, 0x9100c129#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 48, Rn := 9, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3776 : Op := ⟨3776, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3780 : Op := ⟨3780, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3784 : Op := ⟨3784, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3788 : Op := ⟨3788, 0xf900052a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3792 : Op := ⟨3792, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3796 : Op := ⟨3796, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3800 : Op := ⟨3800, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3804 : Op := ⟨3804, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3808 : Op := ⟨3808, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3812 : Op := ⟨3812, 0xf90007eb#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3816 : Op := ⟨3816, 0x91000269#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 19, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3820 : Op := ⟨3820, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3824 : Op := ⟨3824, 0xd280000b#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3828 : Op := ⟨3828, 0xf900052b#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 9, Rt := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3832 : Op := ⟨3832, 0xf94007eb#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3836 : Op := ⟨3836, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3840 : Op := ⟨3840, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3844 : Op := ⟨3844, 0xa9012668#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 2, Rt2 := 9, Rn := 19, Rt := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3848 : Op := ⟨3848, 0x52800068#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 3, Rd := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3852 : Op := ⟨3852, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3856 : Op := ⟨3856, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3860 : Op := ⟨3860, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3864 : Op := ⟨3864, 0x91000269#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 19, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3868 : Op := ⟨3868, 0x91008129#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 32, Rn := 9, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3872 : Op := ⟨3872, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3876 : Op := ⟨3876, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3880 : Op := ⟨3880, 0xf9000534#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 9, Rt := 20 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3884 : Op := ⟨3884, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3888 : Op := ⟨3888, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3892 : Op := ⟨3892, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3896 : Op := ⟨3896, 0xb9004268#32,
  .LDST (.Reg_unsigned_imm { size := 2, V := 0, opc := 0, imm12 := 16, Rn := 19, Rt := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3900 : Op := ⟨3900, 0x14000036#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 54 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3924 : Op := ⟨3924, 0x52800028#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3928 : Op := ⟨3928, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3932 : Op := ⟨3932, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3936 : Op := ⟨3936, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3940 : Op := ⟨3940, 0x91000269#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 19, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3944 : Op := ⟨3944, 0x91004129#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 9, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3948 : Op := ⟨3948, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3952 : Op := ⟨3952, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3956 : Op := ⟨3956, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3960 : Op := ⟨3960, 0xf900052a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3964 : Op := ⟨3964, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3968 : Op := ⟨3968, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3972 : Op := ⟨3972, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3976 : Op := ⟨3976, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3980 : Op := ⟨3980, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3984 : Op := ⟨3984, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3988 : Op := ⟨3988, 0x91000269#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 19, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3992 : Op := ⟨3992, 0xf9000128#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3996 : Op := ⟨3996, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4000 : Op := ⟨4000, 0xf900052a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4004 : Op := ⟨4004, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4008 : Op := ⟨4008, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4012 : Op := ⟨4012, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4016 : Op := ⟨4016, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4020 : Op := ⟨4020, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4024 : Op := ⟨4024, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4028 : Op := ⟨4028, 0x91000269#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 19, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4032 : Op := ⟨4032, 0x91008129#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 32, Rn := 9, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4036 : Op := ⟨4036, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4040 : Op := ⟨4040, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4044 : Op := ⟨4044, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4048 : Op := ⟨4048, 0xf900052a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4052 : Op := ⟨4052, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4056 : Op := ⟨4056, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4060 : Op := ⟨4060, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4064 : Op := ⟨4064, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4068 : Op := ⟨4068, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4072 : Op := ⟨4072, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4076 : Op := ⟨4076, 0x91000269#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 19, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4080 : Op := ⟨4080, 0x9100c129#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 48, Rn := 9, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4084 : Op := ⟨4084, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4088 : Op := ⟨4088, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4092 : Op := ⟨4092, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4096 : Op := ⟨4096, 0xf900052a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4100 : Op := ⟨4100, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4104 : Op := ⟨4104, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4108 : Op := ⟨4108, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4112 : Op := ⟨4112, 0xb9004268#32,
  .LDST (.Reg_unsigned_imm { size := 2, V := 0, opc := 0, imm12 := 16, Rn := 19, Rt := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4144 : Op := ⟨4144, 0x52800108#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 8, Rd := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4148 : Op := ⟨4148, 0xa9015275#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 2, Rt2 := 20, Rn := 19, Rt := 21 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4152 : Op := ⟨4152, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4156 : Op := ⟨4156, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4160 : Op := ⟨4160, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4164 : Op := ⟨4164, 0x91000269#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 19, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4168 : Op := ⟨4168, 0xf9000128#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4172 : Op := ⟨4172, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4176 : Op := ⟨4176, 0xf900052a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4180 : Op := ⟨4180, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4184 : Op := ⟨4184, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4188 : Op := ⟨4188, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4192 : Op := ⟨4192, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4196 : Op := ⟨4196, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4200 : Op := ⟨4200, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4204 : Op := ⟨4204, 0x91000269#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 19, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4208 : Op := ⟨4208, 0x91008129#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 32, Rn := 9, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4212 : Op := ⟨4212, 0xd280000a#32,
  .DPI (.Move_wide_imm { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4216 : Op := ⟨4216, 0xf900012a#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4220 : Op := ⟨4220, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4224 : Op := ⟨4224, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4228 : Op := ⟨4228, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4232 : Op := ⟨4232, 0xd10043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4236 : Op := ⟨4236, 0xf90003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4240 : Op := ⟨4240, 0xf90007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4244 : Op := ⟨4244, 0x91000269#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 19, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4248 : Op := ⟨4248, 0x91010129#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 64, Rn := 9, Rd := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4252 : Op := ⟨4252, 0x5280000a#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 0, Rd := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4256 : Op := ⟨4256, 0xb900012a#32,
  .LDST (.Reg_unsigned_imm { size := 2, V := 0, opc := 0, imm12 := 0, Rn := 9, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4260 : Op := ⟨4260, 0xf94007ea#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 10 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4264 : Op := ⟨4264, 0xf94003e9#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4268 : Op := ⟨4268, 0x910043ff#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p4272 : Op := ⟨4272, 0x17ffffd9#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 67108825 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩

end SszArm.Measure.Result
