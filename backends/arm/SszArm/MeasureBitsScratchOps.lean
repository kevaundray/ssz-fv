import SszArm.MeasureResultFields

namespace SszArm.Measure.Bits.Scratch

open Result

def p3532 : Op := { p4064 with offset := 3532, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3536 : Op := { p4068 with offset := 3536, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3540 : Op := { p4072 with offset := 3540, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3544 : Op := { p4076 with offset := 3544, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3548 : Op := { p4080 with offset := 3548, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3552 : Op := { p4084 with offset := 3552, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3556 : Op := { p4088 with offset := 3556, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3560 : Op := { p4092 with offset := 3560, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3564 : Op := { p4096 with offset := 3564, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3568 : Op := { p4100 with offset := 3568, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3572 : Op := { p4104 with offset := 3572, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3576 : Op := { p4108 with offset := 3576, member := by simp only [bodyProgram, List.mem_append]; decide }

def reservedOps : List Op := [p3532, p3536, p3540, p3544, p3548, p3552, p3556, p3560, p3564, p3568, p3572, p3576]

def p3580 : Op := { p3976 with offset := 3580, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3584 : Op := { p3980 with offset := 3584, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3588 : Op := { p3984 with offset := 3588, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3592 : Op := { p3988 with offset := 3592, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3596 : Op := { p3992 with offset := 3596, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3600 : Op := { p3996 with offset := 3600, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3604 : Op := { p4000 with offset := 3604, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3608 : Op := { p4004 with offset := 3608, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3612 : Op := { p4008 with offset := 3612, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3616 : Op := { p4012 with offset := 3616, member := by simp only [bodyProgram, List.mem_append]; decide }

def headerOps : List Op := [p3580, p3584, p3588, p3592, p3596, p3600, p3604, p3608, p3612, p3616]

def p3624 : Op := { p4016 with offset := 3624, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3628 : Op := { p4020 with offset := 3628, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3632 : Op := { p4024 with offset := 3632, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3636 : Op := { p4028 with offset := 3636, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3640 : Op := { p4032 with offset := 3640, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3644 : Op := { p4036 with offset := 3644, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3648 : Op := { p4040 with offset := 3648, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3652 : Op := { p4044 with offset := 3652, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3656 : Op := { p4048 with offset := 3656, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3660 : Op := { p4052 with offset := 3660, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3664 : Op := { p4056 with offset := 3664, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3668 : Op := { p4060 with offset := 3668, member := by simp only [bodyProgram, List.mem_append]; decide }

def actualOps : List Op := [p3624, p3628, p3632, p3636, p3640, p3644, p3648, p3652, p3656, p3660, p3664, p3668]

def p3672 : Op := { p3928 with offset := 3672, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3676 : Op := { p3932 with offset := 3676, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3680 : Op := { p3936 with offset := 3680, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3684 : Op := { p3940 with offset := 3684, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3688 : Op := { p3944 with offset := 3688, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3692 : Op := { p3948 with offset := 3692, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3696 : Op := { p3952 with offset := 3696, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3700 : Op := { p3956 with offset := 3700, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3704 : Op := { p3960 with offset := 3704, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3708 : Op := { p3964 with offset := 3708, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3712 : Op := { p3968 with offset := 3712, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3716 : Op := { p3972 with offset := 3716, member := by simp only [bodyProgram, List.mem_append]; decide }

def expectedOps : List Op := [p3672, p3676, p3680, p3684, p3688, p3692, p3696, p3700, p3704, p3708, p3712, p3716]

def p3528 : Op := { Result.p3924 with offset := 3528, member := by simp only [bodyProgram, List.mem_append]; decide }
def p3620 : Op := ⟨3620, 0x52900008#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 32768, Rd := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3720 : Op := ⟨3720, 0x1400002c#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 44 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩

end SszArm.Measure.Bits.Scratch
