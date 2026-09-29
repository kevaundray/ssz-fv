import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.MeasureFixed

/-- Actual ELF entry address of _ZN13ssz_fv_native6schema13measure_fixed17hd34cfd77f8373849E. -/
def address : Nat := 2321108

def byteSize : Nat := 828

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10283ff#32), -- sub sp, sp, #0xa0
  (4, 0xf9002bfe#32), -- str x30, [sp, #0x50]
  (8, 0xa90667fa#32), -- stp x26, x25, [sp, #0x60]
  (12, 0xa9075ff8#32), -- stp x24, x23, [sp, #0x70]
  (16, 0xa90857f6#32), -- stp x22, x21, [sp, #0x80]
  (20, 0xa9094ff4#32), -- stp x20, x19, [sp, #0x90]
  (24, 0xf9400028#32), -- ldr x8, [x1]
  (28, 0xaa0003f3#32), -- mov x19, x0
  (32, 0xf1000d1f#32), -- cmp x8, #0x3
  (36, 0x5400036d#32), -- b.le 0x236b64 <.LBB98_6>
  (40, 0xaa0203f4#32), -- mov x20, x2
  (44, 0xf100251f#32), -- cmp x8, #0x9
  (48, 0x540003ec#32), -- b.gt 0x236b80 <.LBB98_10>
  (52, 0xf100111f#32), -- cmp x8, #0x4
  (56, 0x54000560#32), -- b.eq 0x236bb8 <.LBB98_15>
  (60, 0xf1001d1f#32), -- cmp x8, #0x7
  (64, 0x54001201#32), -- b.ne 0x236d54 <.LBB98_29>
  (68, 0xaa0103f9#32), -- mov x25, x1
  (72, 0xf9400c21#32), -- ldr x1, [x1, #0x18]
  (76, 0x910023e0#32), -- add x0, sp, #0x8
  (80, 0xaa1403e2#32), -- mov x2, x20
  (84, 0x910023fa#32), -- add x26, sp, #0x8
  (88, 0x97ffffea#32), -- bl 0x236ad4 <_ZN13ssz_fv_native6schema13measure_fixed17hd34cfd77f8373849E>
  (92, 0xa940dbf7#32), -- ldp x23, x22, [sp, #0x8]
  (96, 0xb9404bf8#32), -- ldr w24, [sp, #0x48]
  (100, 0xf9400ff5#32), -- ldr x21, [sp, #0x18]
  (104, 0x34000dd8#32), -- cbz w24, 0x236cf4 <.LBB98_26>
  (108, 0x91006260#32), -- add x0, x19, #0x18
  (112, 0x91006341#32), -- add x1, x26, #0x18
  (116, 0x52800502#32), -- mov w2, #0x28               // =40
  (120, 0x94005a61#32), -- bl 0x24d4d0 <memcpy>
  (124, 0xb9404fe8#32), -- ldr w8, [sp, #0x4c]
  (128, 0xa900d676#32), -- stp x22, x21, [x19, #0x8]
  (132, 0xf9000277#32), -- str x23, [x19]
  (136, 0x29082278#32), -- stp w24, w8, [x19, #0x40]
  (140, 0x14000090#32), -- b 0x236da0 <.LBB98_31>
  (144, 0xb4000248#32), -- cbz x8, 0x236bac <.LBB98_14>
  (148, 0xf100051f#32), -- cmp x8, #0x1
  (152, 0x54000060#32), -- b.eq 0x236b78 <.LBB98_9>
  (156, 0xf100091f#32), -- cmp x8, #0x2
  (160, 0x54000f01#32), -- b.ne 0x236d54 <.LBB98_29>
  (164, 0xa940d835#32), -- ldp x21, x22, [x1, #0x8]
  (168, 0x14000072#32), -- b 0x236d44 <.LBB98_28>
  (172, 0xf100291f#32), -- cmp x8, #0xa
  (176, 0x54000420#32), -- b.eq 0x236c08 <.LBB98_17>
  (180, 0xf1002d1f#32), -- cmp x8, #0xb
  (184, 0x54000e41#32), -- b.ne 0x236d54 <.LBB98_29>
  (188, 0x52800308#32), -- mov w8, #0x18               // =24
  (192, 0x8b080028#32), -- add x8, x1, x8
  (196, 0xf9400509#32), -- ldr x9, [x8, #0x8]
  (200, 0xb50003e9#32), -- cbnz x9, 0x236c18 <.LBB98_18>
  (204, 0xaa1f03f5#32), -- mov x21, xzr
  (208, 0xaa1f03f6#32), -- mov x22, xzr
  (212, 0x14000067#32), -- b 0x236d44 <.LBB98_28>
  (216, 0xaa1f03f5#32), -- mov x21, xzr
  (220, 0x52800036#32), -- mov w22, #0x1               // =1
  (224, 0x14000064#32), -- b 0x236d44 <.LBB98_28>
  (228, 0xa9408828#32), -- ldp x8, x2, [x1, #0x8]
  (232, 0x910023e0#32), -- add x0, sp, #0x8
  (236, 0x52800103#32), -- mov w3, #0x8                // =8
  (240, 0xaa1403e4#32), -- mov x4, x20
  (244, 0x910023f9#32), -- add x25, sp, #0x8
  (248, 0xaa0803e1#32), -- mov x1, x8
  (252, 0x97ffa832#32) -- bl 0x220c98 <_ZN13ssz_fv_native3nat3Nat13div_rem_small17he8c5c3bc7904fc5eE>
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0xa940dbf5#32), -- ldp x21, x22, [sp, #0x8]
  (260, 0xb9404bf7#32), -- ldr w23, [sp, #0x48]
  (264, 0xf9400ff8#32), -- ldr x24, [sp, #0x18]
  (268, 0x34000637#32), -- cbz w23, 0x236ca4 <.LBB98_23>
  (272, 0x91006260#32), -- add x0, x19, #0x18
  (276, 0x91006321#32), -- add x1, x25, #0x18
  (280, 0x52800502#32), -- mov w2, #0x28               // =40
  (284, 0x94005a38#32), -- bl 0x24d4d0 <memcpy>
  (288, 0xb9404fe8#32), -- ldr w8, [sp, #0x4c]
  (292, 0xa9005a75#32), -- stp x21, x22, [x19]
  (296, 0xf9000a78#32), -- str x24, [x19, #0x10]
  (300, 0x29082277#32), -- stp w23, w8, [x19, #0x40]
  (304, 0x14000067#32), -- b 0x236da0 <.LBB98_31>
  (308, 0x52800108#32), -- mov w8, #0x8                // =8
  (312, 0x8b080028#32), -- add x8, x1, x8
  (316, 0xf9400509#32), -- ldr x9, [x8, #0x8]
  (320, 0xb4fffc69#32), -- cbz x9, 0x236ba0 <.LBB98_13>
  (324, 0x8b090529#32), -- add x9, x9, x9, lsl #1
  (328, 0xf9400108#32), -- ldr x8, [x8]
  (332, 0xaa1f03f5#32), -- mov x21, xzr
  (336, 0xaa1f03f6#32), -- mov x22, xzr
  (340, 0xd37df137#32), -- lsl x23, x9, #3
  (344, 0x91004118#32), -- add x24, x8, #0x10
  (348, 0xf8418701#32), -- ldr x1, [x24], #0x18
  (352, 0x910023e0#32), -- add x0, sp, #0x8
  (356, 0xaa1403e2#32), -- mov x2, x20
  (360, 0x97ffffa6#32), -- bl 0x236ad4 <_ZN13ssz_fv_native6schema13measure_fixed17hd34cfd77f8373849E>
  (364, 0xa9408ff9#32), -- ldp x25, x3, [sp, #0x8]
  (368, 0xb9404bfa#32), -- ldr w26, [sp, #0x48]
  (372, 0xf9400fe4#32), -- ldr x4, [sp, #0x18]
  (376, 0x35000b9a#32), -- cbnz w26, 0x236dbc <.LBB98_32>
  (380, 0xd10043ff#32), -- sub sp, sp, #0x10
  (384, 0xf90003e9#32), -- str x9, [sp]
  (388, 0x12000329#32), -- and w9, w25, #0x1
  (392, 0x34000089#32), -- cbz w9, 0x236c6c <.Llower_arm_717>
  (396, 0xf94003e9#32), -- ldr x9, [sp]
  (400, 0x910043ff#32), -- add sp, sp, #0x10
  (404, 0x14000004#32), -- b 0x236c78 <.Llower_arm_718>
  (408, 0xf94003e9#32), -- ldr x9, [sp]
  (412, 0x910043ff#32), -- add sp, sp, #0x10
  (416, 0x14000038#32), -- b 0x236d54 <.LBB98_29>
  (420, 0x910023e0#32), -- add x0, sp, #0x8
  (424, 0xaa1503e1#32), -- mov x1, x21
  (428, 0xaa1603e2#32), -- mov x2, x22
  (432, 0xaa1403e5#32), -- mov x5, x20
  (436, 0x97ffb2e9#32), -- bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>
  (440, 0xa940dbf5#32), -- ldp x21, x22, [sp, #0x8]
  (444, 0xb9404bf9#32), -- ldr w25, [sp, #0x48]
  (448, 0x35000ad9#32), -- cbnz w25, 0x236dec <.LBB98_33>
  (452, 0xf10062f7#32), -- subs x23, x23, #0x18
  (456, 0x54fffca1#32), -- b.ne 0x236c30 <.LBB98_19>
  (460, 0x14000029#32), -- b 0x236d44 <.LBB98_28>
  (464, 0xb4000518#32), -- cbz x24, 0x236d44 <.LBB98_28>
  (468, 0x910023e0#32), -- add x0, sp, #0x8
  (472, 0xaa1503e1#32), -- mov x1, x21
  (476, 0xaa1603e2#32), -- mov x2, x22
  (480, 0xaa1f03e3#32), -- mov x3, xzr
  (484, 0x52800024#32), -- mov w4, #0x1                // =1
  (488, 0xaa1403e5#32), -- mov x5, x20
  (492, 0x910023f7#32), -- add x23, sp, #0x8
  (496, 0x97ffb2da#32), -- bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>
  (500, 0xa940dbf5#32), -- ldp x21, x22, [sp, #0x8]
  (504, 0xb9404bf4#32), -- ldr w20, [sp, #0x48]
  (508, 0x340003b4#32) -- cbz w20, 0x236d44 <.LBB98_28>
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0x91004260#32), -- add x0, x19, #0x10
  (516, 0x910042e1#32), -- add x1, x23, #0x10
  (520, 0x52800602#32), -- mov w2, #0x30               // =48
  (524, 0x940059fc#32), -- bl 0x24d4d0 <memcpy>
  (528, 0xb9404fe8#32), -- ldr w8, [sp, #0x4c]
  (532, 0xa9005a75#32), -- stp x21, x22, [x19]
  (536, 0x29082274#32), -- stp w20, w8, [x19, #0x40]
  (540, 0x1400002c#32), -- b 0x236da0 <.LBB98_31>
  (544, 0xd10043ff#32), -- sub sp, sp, #0x10
  (548, 0xf90003e9#32), -- str x9, [sp]
  (552, 0x120002e9#32), -- and w9, w23, #0x1
  (556, 0x34000089#32), -- cbz w9, 0x236d10 <.Llower_arm_719>
  (560, 0xf94003e9#32), -- ldr x9, [sp]
  (564, 0x910043ff#32), -- add sp, sp, #0x10
  (568, 0x14000004#32), -- b 0x236d1c <.Llower_arm_720>
  (572, 0xf94003e9#32), -- ldr x9, [sp]
  (576, 0x910043ff#32), -- add sp, sp, #0x10
  (580, 0x1400000f#32), -- b 0x236d54 <.LBB98_29>
  (584, 0xa9409323#32), -- ldp x3, x4, [x25, #0x8]
  (588, 0x910023e0#32), -- add x0, sp, #0x8
  (592, 0xaa1603e1#32), -- mov x1, x22
  (596, 0xaa1503e2#32), -- mov x2, x21
  (600, 0xaa1403e5#32), -- mov x5, x20
  (604, 0x910023f7#32), -- add x23, sp, #0x8
  (608, 0x97ffb6d2#32), -- bl 0x22487c <_ZN13ssz_fv_native3nat3Nat3mul17h5dc2c96f405496c8E>
  (612, 0xa940dbf5#32), -- ldp x21, x22, [sp, #0x8]
  (616, 0xb9404bf4#32), -- ldr w20, [sp, #0x48]
  (620, 0x35fffcb4#32), -- cbnz w20, 0x236cd4 <.LBB98_25>
  (624, 0x52800028#32), -- mov w8, #0x1                // =1
  (628, 0xa900da75#32), -- stp x21, x22, [x19, #0x8]
  (632, 0xf9000268#32), -- str x8, [x19]
  (636, 0x1400000a#32), -- b 0x236d78 <.LBB98_30>
  (640, 0xd10043ff#32), -- sub sp, sp, #0x10
  (644, 0xf90003e9#32), -- str x9, [sp]
  (648, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (652, 0x91000269#32), -- add x9, x19, #0x0
  (656, 0xd280000a#32), -- mov x10, #0x0               // =0
  (660, 0xf900012a#32), -- str x10, [x9]
  (664, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (668, 0xf94003e9#32), -- ldr x9, [sp]
  (672, 0x910043ff#32), -- add sp, sp, #0x10
  (676, 0xd10043ff#32), -- sub sp, sp, #0x10
  (680, 0xf90003e9#32), -- str x9, [sp]
  (684, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (688, 0x91000269#32), -- add x9, x19, #0x0
  (692, 0x91010129#32), -- add x9, x9, #0x40
  (696, 0x5280000a#32), -- mov w10, #0x0               // =0
  (700, 0xb900012a#32), -- str w10, [x9]
  (704, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (708, 0xf94003e9#32), -- ldr x9, [sp]
  (712, 0x910043ff#32), -- add sp, sp, #0x10
  (716, 0xa9494ff4#32), -- ldp x20, x19, [sp, #0x90]
  (720, 0xf9402bfe#32), -- ldr x30, [sp, #0x50]
  (724, 0xa94857f6#32), -- ldp x22, x21, [sp, #0x80]
  (728, 0xa9475ff8#32), -- ldp x24, x23, [sp, #0x70]
  (732, 0xa94667fa#32), -- ldp x26, x25, [sp, #0x60]
  (736, 0x910283ff#32), -- add sp, sp, #0xa0
  (740, 0xd65f03c0#32), -- ret
  (744, 0x910023e8#32), -- add x8, sp, #0x8
  (748, 0x91006260#32), -- add x0, x19, #0x18
  (752, 0x52800502#32), -- mov w2, #0x28               // =40
  (756, 0x91006101#32), -- add x1, x8, #0x18
  (760, 0xaa0403f4#32), -- mov x20, x4
  (764, 0xaa0303f5#32) -- mov x21, x3
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0x940059bf#32), -- bl 0x24d4d0 <memcpy>
  (772, 0xb9404fe8#32), -- ldr w8, [sp, #0x4c]
  (776, 0xa900d275#32), -- stp x21, x20, [x19, #0x8]
  (780, 0xf9000279#32), -- str x25, [x19]
  (784, 0x2908227a#32), -- stp w26, w8, [x19, #0x40]
  (788, 0x17ffffee#32), -- b 0x236da0 <.LBB98_31>
  (792, 0x910023e8#32), -- add x8, sp, #0x8
  (796, 0x91004260#32), -- add x0, x19, #0x10
  (800, 0x52800602#32), -- mov w2, #0x30               // =48
  (804, 0x91004101#32), -- add x1, x8, #0x10
  (808, 0x940059b5#32), -- bl 0x24d4d0 <memcpy>
  (812, 0xb9404fe8#32), -- ldr w8, [sp, #0x4c]
  (816, 0xa9005a75#32), -- stp x21, x22, [x19]
  (820, 0x29082279#32), -- stp w25, w8, [x19, #0x40]
  (824, 0x17ffffe5#32) -- b 0x236da0 <.LBB98_31>
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3

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

theorem chunk3_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk3 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append, member, true_or, or_true]

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, chunk3_decodes, Bool.and_self]

end SszArm.Codec.Linked.MeasureFixed
