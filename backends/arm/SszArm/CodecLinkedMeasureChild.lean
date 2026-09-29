import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.MeasureChild

/-- Actual ELF entry address of _ZN13ssz_fv_native5codec13measure_parts28_$u7b$$u7b$closure$u7d$$u7d$17hbcad779f9c302ea9E. -/
def address : Nat := 2300248

def byteSize : Nat := 596

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd103c3ff#32), -- sub sp, sp, #0xf0
  (4, 0xf90053fe#32), -- str x30, [sp, #0xa0]
  (8, 0xa90b67fa#32), -- stp x26, x25, [sp, #0xb0]
  (12, 0xa90c5ff8#32), -- stp x24, x23, [sp, #0xc0]
  (16, 0xa90d57f6#32), -- stp x22, x21, [sp, #0xd0]
  (20, 0xa90e4ff4#32), -- stp x20, x19, [sp, #0xe0]
  (24, 0xf940003a#32), -- ldr x26, [x1]
  (28, 0xaa0303f4#32), -- mov x20, x3
  (32, 0xaa0103f7#32), -- mov x23, x1
  (36, 0xaa0003f3#32), -- mov x19, x0
  (40, 0xa9406348#32), -- ldp x8, x24, [x26]
  (44, 0xb40000c8#32), -- cbz x8, 0x23199c <.LBB89_3>
  (48, 0xeb18005f#32), -- cmp x2, x24
  (52, 0x540010a2#32), -- b.hs 0x231ba0 <.LBB89_18>
  (56, 0x52800309#32), -- mov w9, #0x18               // =24
  (60, 0x9b092048#32), -- madd x8, x2, x9, x8
  (64, 0xf9400918#32), -- ldr x24, [x8, #0x10]
  (68, 0xf9400ae1#32), -- ldr x1, [x23, #0x10]
  (72, 0xeb01005f#32), -- cmp x2, x1
  (76, 0x54000fa2#32), -- b.hs 0x231b98 <.LBB89_17>
  (80, 0x52800608#32), -- mov w8, #0x30               // =48
  (84, 0xf94006e9#32), -- ldr x9, [x23, #0x8]
  (88, 0x910163e0#32), -- add x0, sp, #0x58
  (92, 0x9b082442#32), -- madd x2, x2, x8, x9
  (96, 0xf9400ee8#32), -- ldr x8, [x23, #0x18]
  (100, 0xaa1803e1#32), -- mov x1, x24
  (104, 0xaa1403e3#32), -- mov x3, x20
  (108, 0x39400104#32), -- ldrb w4, [x8]
  (112, 0x97fff64d#32), -- bl 0x22f2fc <_ZN13ssz_fv_native5codec7measure17h6f170d30c3984362E>
  (116, 0xa945abe9#32), -- ldp x9, x10, [sp, #0x58]
  (120, 0xb9409be8#32), -- ldr w8, [sp, #0x98]
  (124, 0xa946d7f6#32), -- ldp x22, x21, [sp, #0x68]
  (128, 0xf9403ff9#32), -- ldr x25, [sp, #0x78]
  (132, 0xa901abe9#32), -- stp x9, x10, [sp, #0x18]
  (136, 0x34000188#32), -- cbz w8, 0x231a10 <.LBB89_6>
  (140, 0xa9482be9#32), -- ldp x9, x10, [sp, #0x80]
  (144, 0xf9404beb#32), -- ldr x11, [sp, #0x90]
  (148, 0xa9015676#32), -- stp x22, x21, [x19, #0x10]
  (152, 0xf9001e6b#32), -- str x11, [x19, #0x38]
  (156, 0xa902aa69#32), -- stp x9, x10, [x19, #0x28]
  (160, 0xa941abe9#32), -- ldp x9, x10, [sp, #0x18]
  (164, 0xf9001279#32), -- str x25, [x19, #0x20]
  (168, 0xa9002a69#32), -- stp x9, x10, [x19]
  (172, 0xb9409fe9#32), -- ldr w9, [sp, #0x9c]
  (176, 0x29082668#32), -- stp w8, w9, [x19, #0x40]
  (180, 0x1400005c#32), -- b 0x231b7c <.LBB89_16>
  (184, 0xa941a7e8#32), -- ldp x8, x9, [sp, #0x18]
  (188, 0xf940034a#32), -- ldr x10, [x26]
  (192, 0xa900a7e8#32), -- stp x8, x9, [sp, #0x8]
  (196, 0xb400020a#32), -- cbz x10, 0x231a5c <.LBB89_9>
  (200, 0xaa1803e0#32), -- mov x0, x24
  (204, 0x97fffd93#32), -- bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>
  (208, 0xd10043ff#32), -- sub sp, sp, #0x10
  (212, 0xf90003e9#32), -- str x9, [sp]
  (216, 0x12000009#32), -- and w9, w0, #0x1
  (220, 0x34000089#32), -- cbz w9, 0x231a44 <.Llower_arm_643>
  (224, 0xf94003e9#32), -- ldr x9, [sp]
  (228, 0x910043ff#32), -- add sp, sp, #0x10
  (232, 0x14000004#32), -- b 0x231a50 <.Llower_arm_644>
  (236, 0xf94003e9#32), -- ldr x9, [sp]
  (240, 0x910043ff#32), -- add sp, sp, #0x10
  (244, 0x14000010#32), -- b 0x231a8c <.Llower_arm_646>
  (248, 0xf94016f7#32), -- ldr x23, [x23, #0x28]
  (252, 0xa9400ae1#32) -- ldp x1, x2, [x23]
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0x14000026#32), -- b 0x231af0 <.LBB89_13>
  (260, 0xf94012e8#32), -- ldr x8, [x23, #0x20]
  (264, 0x39400108#32), -- ldrb w8, [x8]
  (268, 0xd10043ff#32), -- sub sp, sp, #0x10
  (272, 0xf90003e9#32), -- str x9, [sp]
  (276, 0x12000109#32), -- and w9, w8, #0x1
  (280, 0x35000089#32), -- cbnz w9, 0x231a80 <.Llower_arm_645>
  (284, 0xf94003e9#32), -- ldr x9, [sp]
  (288, 0x910043ff#32), -- add sp, sp, #0x10
  (292, 0x14000004#32), -- b 0x231a8c <.Llower_arm_646>
  (296, 0xf94003e9#32), -- ldr x9, [sp]
  (300, 0x910043ff#32), -- add sp, sp, #0x10
  (304, 0x17fffff2#32), -- b 0x231a50 <.Llower_arm_644>
  (308, 0xf94016f8#32), -- ldr x24, [x23, #0x28]
  (312, 0x910163e0#32), -- add x0, sp, #0x58
  (316, 0xaa1f03e3#32), -- mov x3, xzr
  (320, 0x52800084#32), -- mov w4, #0x4                // =4
  (324, 0xaa1403e5#32), -- mov x5, x20
  (328, 0xa9400b01#32), -- ldp x1, x2, [x24]
  (332, 0x97ffc762#32), -- bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>
  (336, 0xb9409bfa#32), -- ldr w26, [sp, #0x98]
  (340, 0x3400019a#32), -- cbz w26, 0x231adc <.LBB89_12>
  (344, 0x910063e0#32), -- add x0, sp, #0x18
  (348, 0x910163e1#32), -- add x1, sp, #0x58
  (352, 0x52800802#32), -- mov w2, #0x40               // =64
  (356, 0x94006e85#32), -- bl 0x24d4d0 <memcpy>
  (360, 0xb9409ff4#32), -- ldr w20, [sp, #0x9c]
  (364, 0x910063e1#32), -- add x1, sp, #0x18
  (368, 0xaa1303e0#32), -- mov x0, x19
  (372, 0x52800802#32), -- mov w2, #0x40               // =64
  (376, 0x94006e80#32), -- bl 0x24d4d0 <memcpy>
  (380, 0x2908527a#32), -- stp w26, w20, [x19, #0x40]
  (384, 0x14000029#32), -- b 0x231b7c <.LBB89_16>
  (388, 0xa945a7e8#32), -- ldp x8, x9, [sp, #0x58]
  (392, 0xf9401af7#32), -- ldr x23, [x23, #0x30]
  (396, 0xa9002708#32), -- stp x8, x9, [x24]
  (400, 0xa9400ae1#32), -- ldp x1, x2, [x23]
  (404, 0xa901a7e8#32), -- stp x8, x9, [sp, #0x18]
  (408, 0x910163e0#32), -- add x0, sp, #0x58
  (412, 0xaa1603e3#32), -- mov x3, x22
  (416, 0xaa1503e4#32), -- mov x4, x21
  (420, 0xaa1403e5#32), -- mov x5, x20
  (424, 0x97ffc74b#32), -- bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>
  (428, 0xb9409bf4#32), -- ldr w20, [sp, #0x98]
  (432, 0x34000194#32), -- cbz w20, 0x231b38 <.LBB89_15>
  (436, 0x910063e0#32), -- add x0, sp, #0x18
  (440, 0x910163e1#32), -- add x1, sp, #0x58
  (444, 0x52800802#32), -- mov w2, #0x40               // =64
  (448, 0x94006e6e#32), -- bl 0x24d4d0 <memcpy>
  (452, 0xb9409ff5#32), -- ldr w21, [sp, #0x9c]
  (456, 0x910063e1#32), -- add x1, sp, #0x18
  (460, 0xaa1303e0#32), -- mov x0, x19
  (464, 0x52800802#32), -- mov w2, #0x40               // =64
  (468, 0x94006e69#32), -- bl 0x24d4d0 <memcpy>
  (472, 0x29085674#32), -- stp w20, w21, [x19, #0x40]
  (476, 0x14000012#32), -- b 0x231b7c <.LBB89_16>
  (480, 0xa945a7e8#32), -- ldp x8, x9, [sp, #0x58]
  (484, 0xa9015676#32), -- stp x22, x21, [x19, #0x10]
  (488, 0xf9001279#32), -- str x25, [x19, #0x20]
  (492, 0xd10043ff#32), -- sub sp, sp, #0x10
  (496, 0xf90003e9#32), -- str x9, [sp]
  (500, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (504, 0x91000269#32), -- add x9, x19, #0x0
  (508, 0x91010129#32) -- add x9, x9, #0x40
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0x5280000a#32), -- mov w10, #0x0               // =0
  (516, 0xb900012a#32), -- str w10, [x9]
  (520, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (524, 0xf94003e9#32), -- ldr x9, [sp]
  (528, 0x910043ff#32), -- add sp, sp, #0x10
  (532, 0xa901a7e8#32), -- stp x8, x9, [sp, #0x18]
  (536, 0xa90026e8#32), -- stp x8, x9, [x23]
  (540, 0xa940a7e8#32), -- ldp x8, x9, [sp, #0x8]
  (544, 0xa9002668#32), -- stp x8, x9, [x19]
  (548, 0xa94e4ff4#32), -- ldp x20, x19, [sp, #0xe0]
  (552, 0xf94053fe#32), -- ldr x30, [sp, #0xa0]
  (556, 0xa94d57f6#32), -- ldp x22, x21, [sp, #0xd0]
  (560, 0xa94c5ff8#32), -- ldp x24, x23, [sp, #0xc0]
  (564, 0xa94b67fa#32), -- ldp x26, x25, [sp, #0xb0]
  (568, 0x9103c3ff#32), -- add sp, sp, #0xf0
  (572, 0xd65f03c0#32), -- ret
  (576, 0xaa0203e0#32), -- mov x0, x2
  (580, 0x97ffb175#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (584, 0xaa0203e0#32), -- mov x0, x2
  (588, 0xaa1803e1#32), -- mov x1, x24
  (592, 0x97ffb172#32) -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2

def CodeAt (s : ArmState) (base : BitVec 64) : Prop :=
  WordsAt program s base

theorem chunk0_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk0 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append, member, true_or, or_true]

theorem chunk1_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk1 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append, member, true_or, or_true]

theorem chunk2_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk2 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append, member, true_or, or_true]

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, Bool.and_self]

end SszArm.Codec.Linked.MeasureChild
