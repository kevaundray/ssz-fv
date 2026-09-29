import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.ShiftXor

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN13ssz_fv_native7indices9shift_xor17h45a956e38b065bb1E. -/
def address : Nat := 2365816

def byteSize : Nat := 1796

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xb40002a1#32), -- cbz x1, 0x2419cc <.LBB123_5>
  (4, 0xd1002028#32), -- sub x8, x1, #0x8
  (8, 0xaa0203eb#32), -- mov x11, x2
  (12, 0xb40005ab#32), -- cbz x11, 0x241a38 <.LBB123_7>
  (16, 0xd10043ff#32), -- sub sp, sp, #0x10
  (20, 0xf90003ea#32), -- str x10, [sp]
  (24, 0xaa0b03ea#32), -- mov x10, x11
  (28, 0xd37df14a#32), -- lsl x10, x10, #3
  (32, 0x8b0a010a#32), -- add x10, x8, x10
  (36, 0xf9400149#32), -- ldr x9, [x10]
  (40, 0xf94003ea#32), -- ldr x10, [sp]
  (44, 0x910043ff#32), -- add sp, sp, #0x10
  (48, 0xaa0b03ea#32), -- mov x10, x11
  (52, 0xd100056b#32), -- sub x11, x11, #0x1
  (56, 0xb4fffea9#32), -- cbz x9, 0x241984 <.LBB123_2>
  (60, 0xd37ae548#32), -- lsl x8, x10, #6
  (64, 0xd37afd4a#32), -- lsr x10, x10, #58
  (68, 0x9280000b#32), -- mov x11, #-0x1 // =-1
  (72, 0xf1010108#32), -- subs x8, x8, #0x40
  (76, 0x9a0b014a#32), -- adc x10, x10, x11
  (80, 0x14000007#32), -- b 0x2419e4 <.LBB123_6>
  (84, 0xaa1f03e8#32), -- mov x8, xzr
  (88, 0xaa1f03ea#32), -- mov x10, xzr
  (92, 0xaa1f03eb#32), -- mov x11, xzr
  (96, 0xaa1f03ec#32), -- mov x12, xzr
  (100, 0xaa0203e9#32), -- mov x9, x2
  (104, 0xb40002e2#32), -- cbz x2, 0x241a3c <.LBB123_8>
  (108, 0xd10043ff#32), -- sub sp, sp, #0x10
  (112, 0xf90003ea#32), -- str x10, [sp]
  (116, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (120, 0xaa0903ea#32), -- mov x10, x9
  (124, 0xd280080b#32), -- mov x11, #0x40 // =64
  (128, 0xb400008a#32), -- cbz x10, 0x241a08 <.Llower_arm_1016>
  (132, 0xd100056b#32), -- sub x11, x11, #0x1
  (136, 0xd341fd4a#32), -- lsr x10, x10, #1
  (140, 0xb5ffffca#32), -- cbnz x10, 0x2419fc <.Llower_arm_1015>
  (144, 0xaa0b03e9#32), -- mov x9, x11
  (148, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (152, 0xf94003ea#32), -- ldr x10, [sp]
  (156, 0x910043ff#32), -- add sp, sp, #0x10
  (160, 0x5280080b#32), -- mov w11, #0x40 // =64
  (164, 0x4b090169#32), -- sub w9, w11, w9
  (168, 0xab09010b#32), -- adds x11, x8, x9
  (172, 0x54000062#32), -- b.hs 0x241a30 <.Llower_arm_1017>
  (176, 0xaa0a03ec#32), -- mov x12, x10
  (180, 0x14000002#32), -- b 0x241a34 <.Llower_arm_1018>
  (184, 0x9100054c#32), -- add x12, x10, #0x1
  (188, 0x14000002#32), -- b 0x241a3c <.LBB123_8>
  (192, 0xaa1f03ec#32), -- mov x12, xzr
  (196, 0xeb040168#32), -- subs x8, x11, x4
  (200, 0xfa050189#32), -- sbcs x9, x12, x5
  (204, 0x9a8833e8#32), -- csel x8, xzr, x8, lo
  (208, 0x9a8933e9#32), -- csel x9, xzr, x9, lo
  (212, 0xb100fd08#32), -- adds x8, x8, #0x3f
  (216, 0x54000062#32), -- b.hs 0x241a5c <.Llower_arm_1019>
  (220, 0xaa0903e9#32), -- mov x9, x9
  (224, 0x14000002#32), -- b 0x241a60 <.Llower_arm_1020>
  (228, 0x91000529#32), -- add x9, x9, #0x1
  (232, 0xd10043ff#32), -- sub sp, sp, #0x10
  (236, 0xf90003ea#32), -- str x10, [sp]
  (240, 0xd346fd0a#32), -- lsr x10, x8, #6
  (244, 0xaa09e949#32), -- orr x9, x10, x9, lsl #58
  (248, 0xf94003ea#32), -- ldr x10, [sp]
  (252, 0x910043ff#32) -- add sp, sp, #0x10
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0xf100053f#32), -- cmp x9, #0x1
  (260, 0x54000068#32), -- b.hi 0x241a88 <.Llower_arm_1021>
  (264, 0xd2800028#32), -- mov x8, #0x1 // =1
  (268, 0x14000002#32), -- b 0x241a8c <.Llower_arm_1022>
  (272, 0xaa0903e8#32), -- mov x8, x9
  (276, 0xf100093f#32), -- cmp x9, #0x2
  (280, 0x54000322#32), -- b.hs 0x241af4 <.LBB123_11>
  (284, 0xf100fcbf#32), -- cmp x5, #0x3f
  (288, 0x54001109#32), -- b.ls 0x241cb8 <.LBB123_23>
  (292, 0xd24003e8#32), -- eor x8, xzr, #0x1
  (296, 0xd10043ff#32), -- sub sp, sp, #0x10
  (300, 0xf90003e9#32), -- str x9, [sp]
  (304, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (308, 0x91000009#32), -- add x9, x0, #0x0
  (312, 0xd280000a#32), -- mov x10, #0x0 // =0
  (316, 0xf900012a#32), -- str x10, [x9]
  (320, 0xf9000528#32), -- str x8, [x9, #0x8]
  (324, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (328, 0xf94003e9#32), -- ldr x9, [sp]
  (332, 0x910043ff#32), -- add sp, sp, #0x10
  (336, 0xd10043ff#32), -- sub sp, sp, #0x10
  (340, 0xf90003e9#32), -- str x9, [sp]
  (344, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (348, 0x91000009#32), -- add x9, x0, #0x0
  (352, 0x91010129#32), -- add x9, x9, #0x40
  (356, 0x5280000a#32), -- mov w10, #0x0 // =0
  (360, 0xb900012a#32), -- str w10, [x9]
  (364, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (368, 0xf94003e9#32), -- ldr x9, [sp]
  (372, 0x910043ff#32), -- add sp, sp, #0x10
  (376, 0xd65f03c0#32), -- ret
  (380, 0xd37dfd29#32), -- lsr x9, x9, #61
  (384, 0xb50007c9#32), -- cbnz x9, 0x241bf0 <.LBB123_22>
  (388, 0xd37df10a#32), -- lsl x10, x8, #3
  (392, 0xd10043ff#32), -- sub sp, sp, #0x10
  (396, 0xf90003e9#32), -- str x9, [sp]
  (400, 0x92410149#32), -- and x9, x10, #0x8000000000000000
  (404, 0xb5000089#32), -- cbnz x9, 0x241b1c <.Llower_arm_1023>
  (408, 0xf94003e9#32), -- ldr x9, [sp]
  (412, 0x910043ff#32), -- add sp, sp, #0x10
  (416, 0x14000004#32), -- b 0x241b28 <.Llower_arm_1024>
  (420, 0xf94003e9#32), -- ldr x9, [sp]
  (424, 0x910043ff#32), -- add sp, sp, #0x10
  (428, 0x14000033#32), -- b 0x241bf0 <.LBB123_22>
  (432, 0xf94000c9#32), -- ldr x9, [x6]
  (436, 0xf94008cb#32), -- ldr x11, [x6, #0x10]
  (440, 0xab09016c#32), -- adds x12, x11, x9
  (444, 0x540005e2#32), -- b.hs 0x241bf0 <.LBB123_22>
  (448, 0xb100219f#32), -- cmn x12, #0x8
  (452, 0x540005a8#32), -- b.hi 0x241bf0 <.LBB123_22>
  (456, 0x91001d8d#32), -- add x13, x12, #0x7
  (460, 0x927df1ad#32), -- and x13, x13, #0xfffffffffffffff8
  (464, 0xcb0c01ac#32), -- sub x12, x13, x12
  (468, 0xab0b018b#32), -- adds x11, x12, x11
  (472, 0x54000502#32), -- b.hs 0x241bf0 <.LBB123_22>
  (476, 0xab0a016a#32), -- adds x10, x11, x10
  (480, 0x540004c2#32), -- b.hs 0x241bf0 <.LBB123_22>
  (484, 0xf94004cc#32), -- ldr x12, [x6, #0x8]
  (488, 0xeb0c015f#32), -- cmp x10, x12
  (492, 0x54000468#32), -- b.hi 0x241bf0 <.LBB123_22>
  (496, 0xf10100bf#32), -- cmp x5, #0x40
  (500, 0x8b0b0129#32), -- add x9, x9, x11
  (504, 0xf90008ca#32), -- str x10, [x6, #0x10]
  (508, 0x54001563#32) -- b.lo 0x241e20 <.LBB123_33>
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xaa1f03ea#32), -- mov x10, xzr
  (516, 0xf100015f#32), -- cmp x10, #0x0
  (520, 0x9100054b#32), -- add x11, x10, #0x1
  (524, 0x54000060#32), -- b.eq 0x241b90 <.Llower_arm_1025>
  (528, 0x5280000c#32), -- mov w12, #0x0 // =0
  (532, 0x14000002#32), -- b 0x241b94 <.Llower_arm_1026>
  (536, 0x5280002c#32), -- mov w12, #0x1 // =1
  (540, 0xeb0b011f#32), -- cmp x8, x11
  (544, 0xd10043ff#32), -- sub sp, sp, #0x10
  (548, 0xf90003eb#32), -- str x11, [sp]
  (552, 0xaa0a03eb#32), -- mov x11, x10
  (556, 0xd37df16b#32), -- lsl x11, x11, #3
  (560, 0x8b0b012b#32), -- add x11, x9, x11
  (564, 0xf900016c#32), -- str x12, [x11]
  (568, 0xf94003eb#32), -- ldr x11, [sp]
  (572, 0x910043ff#32), -- add sp, sp, #0x10
  (576, 0xaa0b03ea#32), -- mov x10, x11
  (580, 0x54fffe01#32), -- b.ne 0x241b7c <.LBB123_20>
  (584, 0xa9002009#32), -- stp x9, x8, [x0]
  (588, 0xd10043ff#32), -- sub sp, sp, #0x10
  (592, 0xf90003e9#32), -- str x9, [sp]
  (596, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (600, 0x91000009#32), -- add x9, x0, #0x0
  (604, 0x91010129#32), -- add x9, x9, #0x40
  (608, 0x5280000a#32), -- mov w10, #0x0 // =0
  (612, 0xb900012a#32), -- str w10, [x9]
  (616, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (620, 0xf94003e9#32), -- ldr x9, [sp]
  (624, 0x910043ff#32), -- add sp, sp, #0x10
  (628, 0xd65f03c0#32), -- ret
  (632, 0x5290000a#32), -- mov w10, #0x8000 // =32768
  (636, 0x52800029#32), -- mov w9, #0x1 // =1
  (640, 0xd10043ff#32), -- sub sp, sp, #0x10
  (644, 0xf90003e9#32), -- str x9, [sp]
  (648, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (652, 0x91000009#32), -- add x9, x0, #0x0
  (656, 0x9100c129#32), -- add x9, x9, #0x30
  (660, 0xd280000a#32), -- mov x10, #0x0 // =0
  (664, 0xf900012a#32), -- str x10, [x9]
  (668, 0xd280000a#32), -- mov x10, #0x0 // =0
  (672, 0xf900052a#32), -- str x10, [x9, #0x8]
  (676, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (680, 0xf94003e9#32), -- ldr x9, [sp]
  (684, 0x910043ff#32), -- add sp, sp, #0x10
  (688, 0xd10043ff#32), -- sub sp, sp, #0x10
  (692, 0xf90003e9#32), -- str x9, [sp]
  (696, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (700, 0x91000009#32), -- add x9, x0, #0x0
  (704, 0x91008129#32), -- add x9, x9, #0x20
  (708, 0xd280000a#32), -- mov x10, #0x0 // =0
  (712, 0xf900012a#32), -- str x10, [x9]
  (716, 0xd280000a#32), -- mov x10, #0x0 // =0
  (720, 0xf900052a#32), -- str x10, [x9, #0x8]
  (724, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (728, 0xf94003e9#32), -- ldr x9, [sp]
  (732, 0x910043ff#32), -- add sp, sp, #0x10
  (736, 0xd10043ff#32), -- sub sp, sp, #0x10
  (740, 0xf90003e9#32), -- str x9, [sp]
  (744, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (748, 0x91000009#32), -- add x9, x0, #0x0
  (752, 0x91004129#32), -- add x9, x9, #0x10
  (756, 0xd280000a#32), -- mov x10, #0x0 // =0
  (760, 0xf900012a#32), -- str x10, [x9]
  (764, 0xd280000a#32) -- mov x10, #0x0 // =0
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0xf900052a#32), -- str x10, [x9, #0x8]
  (772, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (776, 0xf94003e9#32), -- ldr x9, [sp]
  (780, 0x910043ff#32), -- add sp, sp, #0x10
  (784, 0xd10043ff#32), -- sub sp, sp, #0x10
  (788, 0xf90003ea#32), -- str x10, [sp]
  (792, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (796, 0x9100000a#32), -- add x10, x0, #0x0
  (800, 0xf9000149#32), -- str x9, [x10]
  (804, 0xd280000b#32), -- mov x11, #0x0 // =0
  (808, 0xf900054b#32), -- str x11, [x10, #0x8]
  (812, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (816, 0xf94003ea#32), -- ldr x10, [sp]
  (820, 0x910043ff#32), -- add sp, sp, #0x10
  (824, 0xb900400a#32), -- str w10, [x0, #0x40]
  (828, 0xd65f03c0#32), -- ret
  (832, 0xd10043ff#32), -- sub sp, sp, #0x10
  (836, 0xf90003ea#32), -- str x10, [sp]
  (840, 0xd346fc8a#32), -- lsr x10, x4, #6
  (844, 0xaa05e949#32), -- orr x9, x10, x5, lsl #58
  (848, 0xf94003ea#32), -- ldr x10, [sp]
  (852, 0x910043ff#32), -- add sp, sp, #0x10
  (856, 0x1200148a#32), -- and w10, w4, #0x3f
  (860, 0xb40001c1#32), -- cbz x1, 0x241d0c <.LBB123_26>
  (864, 0xeb09005f#32), -- cmp x2, x9
  (868, 0x54000249#32), -- b.ls 0x241d24 <.LBB123_27>
  (872, 0xd10043ff#32), -- sub sp, sp, #0x10
  (876, 0xf90003ea#32), -- str x10, [sp]
  (880, 0xaa0903ea#32), -- mov x10, x9
  (884, 0xd37df14a#32), -- lsl x10, x10, #3
  (888, 0x8b0a002a#32), -- add x10, x1, x10
  (892, 0xf9400148#32), -- ldr x8, [x10]
  (896, 0xf94003ea#32), -- ldr x10, [sp]
  (900, 0x910043ff#32), -- add sp, sp, #0x10
  (904, 0x9aca2508#32), -- lsr x8, x8, x10
  (908, 0x3500014a#32), -- cbnz w10, 0x241d2c <.LBB123_28>
  (912, 0x14000030#32), -- b 0x241dc8 <.LBB123_32>
  (916, 0xf100013f#32), -- cmp x9, #0x0
  (920, 0xaa1f03eb#32), -- mov x11, xzr
  (924, 0x9a9f0048#32), -- csel x8, x2, xzr, eq
  (928, 0x9aca2508#32), -- lsr x8, x8, x10
  (932, 0x3500024a#32), -- cbnz w10, 0x241d64 <.LBB123_31>
  (936, 0x1400002a#32), -- b 0x241dc8 <.LBB123_32>
  (940, 0x9aca27e8#32), -- lsr x8, xzr, x10
  (944, 0x3400050a#32), -- cbz w10, 0x241dc8 <.LBB123_32>
  (948, 0xb100053f#32), -- cmn x9, #0x1
  (952, 0xaa1f03eb#32), -- mov x11, xzr
  (956, 0x54000180#32), -- b.eq 0x241d64 <.LBB123_31>
  (960, 0x91000529#32), -- add x9, x9, #0x1
  (964, 0xeb02013f#32), -- cmp x9, x2
  (968, 0x54000122#32), -- b.hs 0x241d64 <.LBB123_31>
  (972, 0xd10043ff#32), -- sub sp, sp, #0x10
  (976, 0xf90003ea#32), -- str x10, [sp]
  (980, 0xaa0903ea#32), -- mov x10, x9
  (984, 0xd37df14a#32), -- lsl x10, x10, #3
  (988, 0x8b0a002a#32), -- add x10, x1, x10
  (992, 0xf940014b#32), -- ldr x11, [x10]
  (996, 0xf94003ea#32), -- ldr x10, [sp]
  (1000, 0x910043ff#32), -- add sp, sp, #0x10
  (1004, 0x4b0403e9#32), -- neg w9, w4
  (1008, 0x9ac92169#32), -- lsl x9, x11, x9
  (1012, 0xaa090108#32), -- orr x8, x8, x9
  (1016, 0xd2400108#32), -- eor x8, x8, #0x1
  (1020, 0xd10043ff#32) -- sub sp, sp, #0x10
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk4 : List (Nat × BitVec 32) := [
  (1024, 0xf90003e9#32), -- str x9, [sp]
  (1028, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1032, 0x91000009#32), -- add x9, x0, #0x0
  (1036, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1040, 0xf900012a#32), -- str x10, [x9]
  (1044, 0xf9000528#32), -- str x8, [x9, #0x8]
  (1048, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1052, 0xf94003e9#32), -- ldr x9, [sp]
  (1056, 0x910043ff#32), -- add sp, sp, #0x10
  (1060, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1064, 0xf90003e9#32), -- str x9, [sp]
  (1068, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1072, 0x91000009#32), -- add x9, x0, #0x0
  (1076, 0x91010129#32), -- add x9, x9, #0x40
  (1080, 0x5280000a#32), -- mov w10, #0x0 // =0
  (1084, 0xb900012a#32), -- str w10, [x9]
  (1088, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1092, 0xf94003e9#32), -- ldr x9, [sp]
  (1096, 0x910043ff#32), -- add sp, sp, #0x10
  (1100, 0xd65f03c0#32), -- ret
  (1104, 0xd2400108#32), -- eor x8, x8, #0x1
  (1108, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1112, 0xf90003e9#32), -- str x9, [sp]
  (1116, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1120, 0x91000009#32), -- add x9, x0, #0x0
  (1124, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1128, 0xf900012a#32), -- str x10, [x9]
  (1132, 0xf9000528#32), -- str x8, [x9, #0x8]
  (1136, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1140, 0xf94003e9#32), -- ldr x9, [sp]
  (1144, 0x910043ff#32), -- add sp, sp, #0x10
  (1148, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1152, 0xf90003e9#32), -- str x9, [sp]
  (1156, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1160, 0x91000009#32), -- add x9, x0, #0x0
  (1164, 0x91010129#32), -- add x9, x9, #0x40
  (1168, 0x5280000a#32), -- mov w10, #0x0 // =0
  (1172, 0xb900012a#32), -- str w10, [x9]
  (1176, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1180, 0xf94003e9#32), -- ldr x9, [sp]
  (1184, 0x910043ff#32), -- add sp, sp, #0x10
  (1188, 0xd65f03c0#32), -- ret
  (1192, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1196, 0xf90003e9#32), -- str x9, [sp]
  (1200, 0xd346fc89#32), -- lsr x9, x4, #6
  (1204, 0xaa05e92a#32), -- orr x10, x9, x5, lsl #58
  (1208, 0xf94003e9#32), -- ldr x9, [sp]
  (1212, 0x910043ff#32), -- add sp, sp, #0x10
  (1216, 0x1200148b#32), -- and w11, w4, #0x3f
  (1220, 0xb4000701#32), -- cbz x1, 0x241f1c <.LBB123_45>
  (1224, 0x34000a4b#32), -- cbz w11, 0x241f88 <.LBB123_48>
  (1228, 0x8b0a0c2e#32), -- add x14, x1, x10, lsl #3
  (1232, 0x4b0403ed#32), -- neg w13, w4
  (1236, 0xaa1f03ec#32), -- mov x12, xzr
  (1240, 0x120015ad#32), -- and w13, w13, #0x3f
  (1244, 0x910021ce#32), -- add x14, x14, #0x8
  (1248, 0xab0c0150#32), -- adds x16, x10, x12
  (1252, 0x540005c2#32), -- b.hs 0x241f14 <.LBB123_44>
  (1256, 0xeb02021f#32), -- cmp x16, x2
  (1260, 0x54000182#32), -- b.hs 0x241e94 <.LBB123_39>
  (1264, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1268, 0xf90003e9#32), -- str x9, [sp]
  (1272, 0x910001c9#32), -- add x9, x14, #0x0
  (1276, 0xd1002129#32) -- sub x9, x9, #0x8
]

theorem chunk4_decodes :
    chunk4.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk5 : List (Nat × BitVec 32) := [
  (1280, 0xf940012f#32), -- ldr x15, [x9]
  (1284, 0xf94003e9#32), -- ldr x9, [sp]
  (1288, 0x910043ff#32), -- add sp, sp, #0x10
  (1292, 0x91000611#32), -- add x17, x16, #0x1
  (1296, 0xaa1f03f0#32), -- mov x16, xzr
  (1300, 0xb50000d1#32), -- cbnz x17, 0x241ea4 <.LBB123_40>
  (1304, 0x1400000a#32), -- b 0x241eb8 <.LBB123_42>
  (1308, 0xaa1f03ef#32), -- mov x15, xzr
  (1312, 0x91000611#32), -- add x17, x16, #0x1
  (1316, 0xaa1f03f0#32), -- mov x16, xzr
  (1320, 0xb40000d1#32), -- cbz x17, 0x241eb8 <.LBB123_42>
  (1324, 0x8b0c0151#32), -- add x17, x10, x12
  (1328, 0x91000631#32), -- add x17, x17, #0x1
  (1332, 0xeb02023f#32), -- cmp x17, x2
  (1336, 0x54000042#32), -- b.hs 0x241eb8 <.LBB123_42>
  (1340, 0xf94001d0#32), -- ldr x16, [x14]
  (1344, 0x9acb25ef#32), -- lsr x15, x15, x11
  (1348, 0x9acd2210#32), -- lsl x16, x16, x13
  (1352, 0xaa1001ef#32), -- orr x15, x15, x16
  (1356, 0xf100019f#32), -- cmp x12, #0x0
  (1360, 0x91000591#32), -- add x17, x12, #0x1
  (1364, 0x910021ce#32), -- add x14, x14, #0x8
  (1368, 0x54000060#32), -- b.eq 0x241edc <.Llower_arm_1027>
  (1372, 0x52800010#32), -- mov w16, #0x0 // =0
  (1376, 0x14000002#32), -- b 0x241ee0 <.Llower_arm_1028>
  (1380, 0x52800030#32), -- mov w16, #0x1 // =1
  (1384, 0xeb11011f#32), -- cmp x8, x17
  (1388, 0xca1001ef#32), -- eor x15, x15, x16
  (1392, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1396, 0xf90003ea#32), -- str x10, [sp]
  (1400, 0xaa0c03ea#32), -- mov x10, x12
  (1404, 0xd37df14a#32), -- lsl x10, x10, #3
  (1408, 0x8b0a012a#32), -- add x10, x9, x10
  (1412, 0xf900014f#32), -- str x15, [x10]
  (1416, 0xf94003ea#32), -- ldr x10, [sp]
  (1420, 0x910043ff#32), -- add sp, sp, #0x10
  (1424, 0xaa1103ec#32), -- mov x12, x17
  (1428, 0x54fffa61#32), -- b.ne 0x241e58 <.LBB123_36>
  (1432, 0x17ffff2c#32), -- b 0x241bc0 <.LBB123_21>
  (1436, 0xaa1f03ef#32), -- mov x15, xzr
  (1440, 0x17ffffeb#32), -- b 0x241ec4 <.LBB123_43>
  (1444, 0x340007eb#32), -- cbz w11, 0x242018 <.LBB123_53>
  (1448, 0xaa1f03ec#32), -- mov x12, xzr
  (1452, 0xcb0803ed#32), -- neg x13, x8
  (1456, 0xaa0a03ee#32), -- mov x14, x10
  (1460, 0xf10001df#32), -- cmp x14, #0x0
  (1464, 0x9a9f004f#32), -- csel x15, x2, xzr, eq
  (1468, 0xeb0a01df#32), -- cmp x14, x10
  (1472, 0x910005ce#32), -- add x14, x14, #0x1
  (1476, 0x9acb25ef#32), -- lsr x15, x15, x11
  (1480, 0x9a8f33ef#32), -- csel x15, xzr, x15, lo
  (1484, 0xf100019f#32), -- cmp x12, #0x0
  (1488, 0x54000060#32), -- b.eq 0x241f54 <.Llower_arm_1029>
  (1492, 0x52800010#32), -- mov w16, #0x0 // =0
  (1496, 0x14000002#32), -- b 0x241f58 <.Llower_arm_1030>
  (1500, 0x52800030#32), -- mov w16, #0x1 // =1
  (1504, 0xb10005ad#32), -- adds x13, x13, #0x1
  (1508, 0xca1001ef#32), -- eor x15, x15, x16
  (1512, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1516, 0xf90003ea#32), -- str x10, [sp]
  (1520, 0xaa0c03ea#32), -- mov x10, x12
  (1524, 0x8b0a012a#32), -- add x10, x9, x10
  (1528, 0xf900014f#32), -- str x15, [x10]
  (1532, 0xf94003ea#32) -- ldr x10, [sp]
]

theorem chunk5_decodes :
    chunk5.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk6 : List (Nat × BitVec 32) := [
  (1536, 0x910043ff#32), -- add sp, sp, #0x10
  (1540, 0x9100218c#32), -- add x12, x12, #0x8
  (1544, 0x54fffd63#32), -- b.lo 0x241f2c <.LBB123_47>
  (1548, 0x17ffff0f#32), -- b 0x241bc0 <.LBB123_21>
  (1552, 0x8b0a0c2b#32), -- add x11, x1, x10, lsl #3
  (1556, 0xaa1f03ec#32), -- mov x12, xzr
  (1560, 0x14000013#32), -- b 0x241fdc <.LBB123_50>
  (1564, 0xf100019f#32), -- cmp x12, #0x0
  (1568, 0x9100058e#32), -- add x14, x12, #0x1
  (1572, 0x54000060#32), -- b.eq 0x241fa8 <.Llower_arm_1031>
  (1576, 0x5280000f#32), -- mov w15, #0x0 // =0
  (1580, 0x14000002#32), -- b 0x241fac <.Llower_arm_1032>
  (1584, 0x5280002f#32), -- mov w15, #0x1 // =1
  (1588, 0xeb0e011f#32), -- cmp x8, x14
  (1592, 0xca0f01ad#32), -- eor x13, x13, x15
  (1596, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1600, 0xf90003ea#32), -- str x10, [sp]
  (1604, 0xaa0c03ea#32), -- mov x10, x12
  (1608, 0xd37df14a#32), -- lsl x10, x10, #3
  (1612, 0x8b0a012a#32), -- add x10, x9, x10
  (1616, 0xf900014d#32), -- str x13, [x10]
  (1620, 0xf94003ea#32), -- ldr x10, [sp]
  (1624, 0x910043ff#32), -- add sp, sp, #0x10
  (1628, 0xaa0e03ec#32), -- mov x12, x14
  (1632, 0x54ffdf40#32), -- b.eq 0x241bc0 <.LBB123_21>
  (1636, 0x8b0c014e#32), -- add x14, x10, x12
  (1640, 0xaa1f03ed#32), -- mov x13, xzr
  (1644, 0xeb0a01df#32), -- cmp x14, x10
  (1648, 0x54fffd63#32), -- b.lo 0x241f94 <.LBB123_49>
  (1652, 0xeb0201df#32), -- cmp x14, x2
  (1656, 0x54fffd22#32), -- b.hs 0x241f94 <.LBB123_49>
  (1660, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1664, 0xf90003e9#32), -- str x9, [sp]
  (1668, 0xaa0c03e9#32), -- mov x9, x12
  (1672, 0xd37df129#32), -- lsl x9, x9, #3
  (1676, 0x8b090169#32), -- add x9, x11, x9
  (1680, 0xf940012d#32), -- ldr x13, [x9]
  (1684, 0xf94003e9#32), -- ldr x9, [sp]
  (1688, 0x910043ff#32), -- add sp, sp, #0x10
  (1692, 0x17ffffe0#32), -- b 0x241f94 <.LBB123_49>
  (1696, 0xaa1f03eb#32), -- mov x11, xzr
  (1700, 0xcb0803ec#32), -- neg x12, x8
  (1704, 0xaa0a03ed#32), -- mov x13, x10
  (1708, 0xf10001bf#32), -- cmp x13, #0x0
  (1712, 0x9a9f004e#32), -- csel x14, x2, xzr, eq
  (1716, 0xeb0a01bf#32), -- cmp x13, x10
  (1720, 0x910005ad#32), -- add x13, x13, #0x1
  (1724, 0x9a8e33ee#32), -- csel x14, xzr, x14, lo
  (1728, 0xf100017f#32), -- cmp x11, #0x0
  (1732, 0x54000060#32), -- b.eq 0x242048 <.Llower_arm_1033>
  (1736, 0x5280000f#32), -- mov w15, #0x0 // =0
  (1740, 0x14000002#32), -- b 0x24204c <.Llower_arm_1034>
  (1744, 0x5280002f#32), -- mov w15, #0x1 // =1
  (1748, 0xb100058c#32), -- adds x12, x12, #0x1
  (1752, 0xca0f01ce#32), -- eor x14, x14, x15
  (1756, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1760, 0xf90003ea#32), -- str x10, [sp]
  (1764, 0xaa0b03ea#32), -- mov x10, x11
  (1768, 0x8b0a012a#32), -- add x10, x9, x10
  (1772, 0xf900014e#32), -- str x14, [x10]
  (1776, 0xf94003ea#32), -- ldr x10, [sp]
  (1780, 0x910043ff#32), -- add sp, sp, #0x10
  (1784, 0x9100216b#32), -- add x11, x11, #0x8
  (1788, 0x54fffd83#32) -- b.lo 0x242024 <.LBB123_54>
]

theorem chunk6_decodes :
    chunk6.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk7 : List (Nat × BitVec 32) := [
  (1792, 0x17fffed2#32) -- b 0x241bc0 <.LBB123_21>
]

theorem chunk7_decodes :
    chunk7.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete linked function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7

def CodeAt (s : ArmState) (base : BitVec 64) : Prop :=
  WordsAt program s base

theorem chunk0_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk0 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk1_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk1 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk2_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk2 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk3_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk3 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk4_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk4 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk5_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk5 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk6_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk6 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk7_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk7 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, chunk3_decodes, chunk4_decodes, chunk5_decodes, chunk6_decodes, chunk7_decodes, Bool.and_self]

theorem step_at (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (row : Nat × BitVec 32) (member : row ∈ program)
    (entry : read_pc s = base + BitVec.ofNat 64 row.1)
    (error : read_err s = .None) :
    stepi s = exec_inst (SszArm.Codec.Linked.decoded program all_decode row member) s :=
  SszArm.Codec.Linked.step_at program all_decode s base code row member entry error

end SszArm.Indices.Linked.ShiftXor
