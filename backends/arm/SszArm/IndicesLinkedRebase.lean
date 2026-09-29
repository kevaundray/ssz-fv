import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.Rebase

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN13ssz_fv_native7indices6rebase17h0203817c13357eb1E. -/
def address : Nat := 2262480

def byteSize : Nat := 1508

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0x8a050088#32), -- and x8, x4, x5
  (4, 0xb100051f#32), -- cmn x8, #0x1
  (8, 0x54000300#32), -- b.eq 0x228638 <.LBB61_2>
  (12, 0xb1000489#32), -- adds x9, x4, #0x1
  (16, 0x54000062#32), -- b.hs 0x2285ec <.Llower_arm_497>
  (20, 0xaa0503e8#32), -- mov x8, x5
  (24, 0x14000002#32), -- b 0x2285f0 <.Llower_arm_498>
  (28, 0x910004a8#32), -- add x8, x5, #0x1
  (32, 0xf240153f#32), -- tst x9, #0x3f
  (36, 0xd10043ff#32), -- sub sp, sp, #0x10
  (40, 0xf90003eb#32), -- str x11, [sp]
  (44, 0xd346fd2b#32), -- lsr x11, x9, #6
  (48, 0xaa08e96a#32), -- orr x10, x11, x8, lsl #58
  (52, 0xf94003eb#32), -- ldr x11, [sp]
  (56, 0x910043ff#32), -- add sp, sp, #0x10
  (60, 0xd346fd0b#32), -- lsr x11, x8, #6
  (64, 0x54000061#32), -- b.ne 0x22861c <.Llower_arm_499>
  (68, 0x5280000c#32), -- mov w12, #0x0 // =0
  (72, 0x14000002#32), -- b 0x228620 <.Llower_arm_500>
  (76, 0x5280002c#32), -- mov w12, #0x1 // =1
  (80, 0xab0c014a#32), -- adds x10, x10, x12
  (84, 0x54000062#32), -- b.hs 0x228630 <.Llower_arm_501>
  (88, 0xaa0b03eb#32), -- mov x11, x11
  (92, 0x14000002#32), -- b 0x228634 <.Llower_arm_502>
  (96, 0x9100056b#32), -- add x11, x11, #0x1
  (100, 0xb400066b#32), -- cbz x11, 0x228700 <.LBB61_3>
  (104, 0x52800028#32), -- mov w8, #0x1 // =1
  (108, 0xd10043ff#32), -- sub sp, sp, #0x10
  (112, 0xf90003e9#32), -- str x9, [sp]
  (116, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (120, 0x91000009#32), -- add x9, x0, #0x0
  (124, 0x91004129#32), -- add x9, x9, #0x10
  (128, 0xd280000a#32), -- mov x10, #0x0 // =0
  (132, 0xf900012a#32), -- str x10, [x9]
  (136, 0xd280000a#32), -- mov x10, #0x0 // =0
  (140, 0xf900052a#32), -- str x10, [x9, #0x8]
  (144, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (148, 0xf94003e9#32), -- ldr x9, [sp]
  (152, 0x910043ff#32), -- add sp, sp, #0x10
  (156, 0xd10043ff#32), -- sub sp, sp, #0x10
  (160, 0xf90003e9#32), -- str x9, [sp]
  (164, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (168, 0x91000009#32), -- add x9, x0, #0x0
  (172, 0xf9000128#32), -- str x8, [x9]
  (176, 0xd280000a#32), -- mov x10, #0x0 // =0
  (180, 0xf900052a#32), -- str x10, [x9, #0x8]
  (184, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (188, 0xf94003e9#32), -- ldr x9, [sp]
  (192, 0x910043ff#32), -- add sp, sp, #0x10
  (196, 0xd10043ff#32), -- sub sp, sp, #0x10
  (200, 0xf90003e9#32), -- str x9, [sp]
  (204, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (208, 0x91000009#32), -- add x9, x0, #0x0
  (212, 0x91008129#32), -- add x9, x9, #0x20
  (216, 0xd280000a#32), -- mov x10, #0x0 // =0
  (220, 0xf900012a#32), -- str x10, [x9]
  (224, 0xd280000a#32), -- mov x10, #0x0 // =0
  (228, 0xf900052a#32), -- str x10, [x9, #0x8]
  (232, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (236, 0xf94003e9#32), -- ldr x9, [sp]
  (240, 0x910043ff#32), -- add sp, sp, #0x10
  (244, 0xd10043ff#32), -- sub sp, sp, #0x10
  (248, 0xf90003e9#32), -- str x9, [sp]
  (252, 0xf90007ea#32) -- str x10, [sp, #0x8]
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0x91000009#32), -- add x9, x0, #0x0
  (260, 0x9100c129#32), -- add x9, x9, #0x30
  (264, 0xd280000a#32), -- mov x10, #0x0 // =0
  (268, 0xf900012a#32), -- str x10, [x9]
  (272, 0xd280000a#32), -- mov x10, #0x0 // =0
  (276, 0xf900052a#32), -- str x10, [x9, #0x8]
  (280, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (284, 0xf94003e9#32), -- ldr x9, [sp]
  (288, 0x910043ff#32), -- add sp, sp, #0x10
  (292, 0x52900008#32), -- mov w8, #0x8000 // =32768
  (296, 0xb9004008#32), -- str w8, [x0, #0x40]
  (300, 0xd65f03c0#32), -- ret
  (304, 0xb40006aa#32), -- cbz x10, 0x2287d4 <.LBB61_9>
  (308, 0xf100055f#32), -- cmp x10, #0x1
  (312, 0x54000921#32), -- b.ne 0x22882c <.LBB61_10>
  (316, 0xb4000061#32), -- cbz x1, 0x228718 <.LBB61_8>
  (320, 0xb4000042#32), -- cbz x2, 0x228718 <.LBB61_8>
  (324, 0xf9400022#32), -- ldr x2, [x1]
  (328, 0xf101009f#32), -- cmp x4, #0x40
  (332, 0x5280080a#32), -- mov w10, #0x40 // =64
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
  (376, 0x9a8a308b#32), -- csel x11, x4, x10, lo
  (380, 0xf10000bf#32), -- cmp x5, #0x0
  (384, 0x1a8a016b#32), -- csel w11, w11, w10, eq
  (388, 0xf101013f#32), -- cmp x9, #0x40
  (392, 0x9a8a3129#32), -- csel x9, x9, x10, lo
  (396, 0xf100011f#32), -- cmp x8, #0x0
  (400, 0x92800008#32), -- mov x8, #-0x1 // =-1
  (404, 0x1a8a0129#32), -- csel w9, w9, w10, eq
  (408, 0x9acb210c#32), -- lsl x12, x8, x11
  (412, 0x9ac9210a#32), -- lsl x10, x8, x9
  (416, 0x7101013f#32), -- cmp w9, #0x40
  (420, 0x54000060#32), -- b.eq 0x228780 <.Llower_arm_503>
  (424, 0xaa2a03e9#32), -- mvn x9, x10
  (428, 0x14000002#32), -- b 0x228784 <.Llower_arm_504>
  (432, 0xaa0803e9#32), -- mov x9, x8
  (436, 0x7101017f#32), -- cmp w11, #0x40
  (440, 0x54000060#32), -- b.eq 0x228794 <.Llower_arm_505>
  (444, 0xaa2c03e8#32), -- mvn x8, x12
  (448, 0x14000002#32), -- b 0x228798 <.Llower_arm_506>
  (452, 0xaa0803e8#32), -- mov x8, x8
  (456, 0x9a8c03ea#32), -- csel x10, xzr, x12, eq
  (460, 0x8a080048#32), -- and x8, x2, x8
  (464, 0x8a0a0129#32), -- and x9, x9, x10
  (468, 0xaa090108#32), -- orr x8, x8, x9
  (472, 0xd10043ff#32), -- sub sp, sp, #0x10
  (476, 0xf90003e9#32), -- str x9, [sp]
  (480, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (484, 0x91000009#32), -- add x9, x0, #0x0
  (488, 0xd280000a#32), -- mov x10, #0x0 // =0
  (492, 0xf900012a#32), -- str x10, [x9]
  (496, 0xf9000528#32), -- str x8, [x9, #0x8]
  (500, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (504, 0xf94003e9#32), -- ldr x9, [sp]
  (508, 0x910043ff#32) -- add sp, sp, #0x10
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xd65f03c0#32), -- ret
  (516, 0xd10043ff#32), -- sub sp, sp, #0x10
  (520, 0xf90003e9#32), -- str x9, [sp]
  (524, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (528, 0x91000009#32), -- add x9, x0, #0x0
  (532, 0xd280000a#32), -- mov x10, #0x0 // =0
  (536, 0xf900012a#32), -- str x10, [x9]
  (540, 0xd280000a#32), -- mov x10, #0x0 // =0
  (544, 0xf900052a#32), -- str x10, [x9, #0x8]
  (548, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (552, 0xf94003e9#32), -- ldr x9, [sp]
  (556, 0x910043ff#32), -- add sp, sp, #0x10
  (560, 0xd10043ff#32), -- sub sp, sp, #0x10
  (564, 0xf90003e9#32), -- str x9, [sp]
  (568, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (572, 0x91000009#32), -- add x9, x0, #0x0
  (576, 0x91010129#32), -- add x9, x9, #0x40
  (580, 0x5280000a#32), -- mov w10, #0x0 // =0
  (584, 0xb900012a#32), -- str w10, [x9]
  (588, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (592, 0xf94003e9#32), -- ldr x9, [sp]
  (596, 0x910043ff#32), -- add sp, sp, #0x10
  (600, 0xd65f03c0#32), -- ret
  (604, 0xd37dfd4b#32), -- lsr x11, x10, #61
  (608, 0xb500046b#32), -- cbnz x11, 0x2288bc <.LBB61_20>
  (612, 0xd37df14c#32), -- lsl x12, x10, #3
  (616, 0xd10043ff#32), -- sub sp, sp, #0x10
  (620, 0xf90003e9#32), -- str x9, [sp]
  (624, 0x92410189#32), -- and x9, x12, #0x8000000000000000
  (628, 0xb5000089#32), -- cbnz x9, 0x228854 <.Llower_arm_507>
  (632, 0xf94003e9#32), -- ldr x9, [sp]
  (636, 0x910043ff#32), -- add sp, sp, #0x10
  (640, 0x14000004#32), -- b 0x228860 <.Llower_arm_508>
  (644, 0xf94003e9#32), -- ldr x9, [sp]
  (648, 0x910043ff#32), -- add sp, sp, #0x10
  (652, 0x14000018#32), -- b 0x2288bc <.LBB61_20>
  (656, 0xf94000cb#32), -- ldr x11, [x6]
  (660, 0xf94008cd#32), -- ldr x13, [x6, #0x10]
  (664, 0xab0b01ae#32), -- adds x14, x13, x11
  (668, 0x54000282#32), -- b.hs 0x2288bc <.LBB61_20>
  (672, 0xb10021df#32), -- cmn x14, #0x8
  (676, 0x54000248#32), -- b.hi 0x2288bc <.LBB61_20>
  (680, 0x91001dcf#32), -- add x15, x14, #0x7
  (684, 0x927df1ef#32), -- and x15, x15, #0xfffffffffffffff8
  (688, 0xcb0e01ee#32), -- sub x14, x15, x14
  (692, 0xab0d01cd#32), -- adds x13, x14, x13
  (696, 0x540001a2#32), -- b.hs 0x2288bc <.LBB61_20>
  (700, 0xab0c01ac#32), -- adds x12, x13, x12
  (704, 0x54000162#32), -- b.hs 0x2288bc <.LBB61_20>
  (708, 0xf94004ce#32), -- ldr x14, [x6, #0x8]
  (712, 0xeb0e019f#32), -- cmp x12, x14
  (716, 0x54000108#32), -- b.hi 0x2288bc <.LBB61_20>
  (720, 0x8b0d016b#32), -- add x11, x11, x13
  (724, 0xaa0203ee#32), -- mov x14, x2
  (728, 0xf90008cc#32), -- str x12, [x6, #0x10]
  (732, 0xb40006e1#32), -- cbz x1, 0x228988 <.LBB61_22>
  (736, 0xb40006a2#32), -- cbz x2, 0x228984 <.LBB61_21>
  (740, 0xf940002e#32), -- ldr x14, [x1]
  (744, 0x14000034#32), -- b 0x228988 <.LBB61_22>
  (748, 0x52800028#32), -- mov w8, #0x1 // =1
  (752, 0xd10043ff#32), -- sub sp, sp, #0x10
  (756, 0xf90003e9#32), -- str x9, [sp]
  (760, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (764, 0x91000009#32) -- add x9, x0, #0x0
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0x9100c129#32), -- add x9, x9, #0x30
  (772, 0xd280000a#32), -- mov x10, #0x0 // =0
  (776, 0xf900012a#32), -- str x10, [x9]
  (780, 0xd280000a#32), -- mov x10, #0x0 // =0
  (784, 0xf900052a#32), -- str x10, [x9, #0x8]
  (788, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (792, 0xf94003e9#32), -- ldr x9, [sp]
  (796, 0x910043ff#32), -- add sp, sp, #0x10
  (800, 0xd10043ff#32), -- sub sp, sp, #0x10
  (804, 0xf90003e9#32), -- str x9, [sp]
  (808, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (812, 0x91000009#32), -- add x9, x0, #0x0
  (816, 0x91008129#32), -- add x9, x9, #0x20
  (820, 0xd280000a#32), -- mov x10, #0x0 // =0
  (824, 0xf900012a#32), -- str x10, [x9]
  (828, 0xd280000a#32), -- mov x10, #0x0 // =0
  (832, 0xf900052a#32), -- str x10, [x9, #0x8]
  (836, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (840, 0xf94003e9#32), -- ldr x9, [sp]
  (844, 0x910043ff#32), -- add sp, sp, #0x10
  (848, 0xd10043ff#32), -- sub sp, sp, #0x10
  (852, 0xf90003e9#32), -- str x9, [sp]
  (856, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (860, 0x91000009#32), -- add x9, x0, #0x0
  (864, 0x91004129#32), -- add x9, x9, #0x10
  (868, 0xd280000a#32), -- mov x10, #0x0 // =0
  (872, 0xf900012a#32), -- str x10, [x9]
  (876, 0xd280000a#32), -- mov x10, #0x0 // =0
  (880, 0xf900052a#32), -- str x10, [x9, #0x8]
  (884, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (888, 0xf94003e9#32), -- ldr x9, [sp]
  (892, 0x910043ff#32), -- add sp, sp, #0x10
  (896, 0xd10043ff#32), -- sub sp, sp, #0x10
  (900, 0xf90003e9#32), -- str x9, [sp]
  (904, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (908, 0x91000009#32), -- add x9, x0, #0x0
  (912, 0xf9000128#32), -- str x8, [x9]
  (916, 0xd280000a#32), -- mov x10, #0x0 // =0
  (920, 0xf900052a#32), -- str x10, [x9, #0x8]
  (924, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (928, 0xf94003e9#32), -- ldr x9, [sp]
  (932, 0x910043ff#32), -- add sp, sp, #0x10
  (936, 0x52900008#32), -- mov w8, #0x8000 // =32768
  (940, 0xb9004008#32), -- str w8, [x0, #0x40]
  (944, 0xd65f03c0#32), -- ret
  (948, 0xaa1f03ee#32), -- mov x14, xzr
  (952, 0xf101009f#32), -- cmp x4, #0x40
  (956, 0x5280080c#32), -- mov w12, #0x40 // =64
  (960, 0x9a8c308d#32), -- csel x13, x4, x12, lo
  (964, 0xf10000bf#32), -- cmp x5, #0x0
  (968, 0x1a8c01af#32), -- csel w15, w13, w12, eq
  (972, 0xf101013f#32), -- cmp x9, #0x40
  (976, 0x9280000d#32), -- mov x13, #-0x1 // =-1
  (980, 0x9a8c3130#32), -- csel x16, x9, x12, lo
  (984, 0xf100011f#32), -- cmp x8, #0x0
  (988, 0x9acf21b2#32), -- lsl x18, x13, x15
  (992, 0x1a8c0210#32), -- csel w16, w16, w12, eq
  (996, 0x9ad021b1#32), -- lsl x17, x13, x16
  (1000, 0x7101021f#32), -- cmp w16, #0x40
  (1004, 0x54000060#32), -- b.eq 0x2289c8 <.Llower_arm_509>
  (1008, 0xaa3103f0#32), -- mvn x16, x17
  (1012, 0x14000002#32), -- b 0x2289cc <.Llower_arm_510>
  (1016, 0xaa0d03f0#32), -- mov x16, x13
  (1020, 0x710101ff#32) -- cmp w15, #0x40
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk4 : List (Nat × BitVec 32) := [
  (1024, 0x54000060#32), -- b.eq 0x2289dc <.Llower_arm_511>
  (1028, 0xaa3203ef#32), -- mvn x15, x18
  (1032, 0x14000002#32), -- b 0x2289e0 <.Llower_arm_512>
  (1036, 0xaa0d03ef#32), -- mov x15, x13
  (1040, 0x9a9203f1#32), -- csel x17, xzr, x18, eq
  (1044, 0x8a0f01ce#32), -- and x14, x14, x15
  (1048, 0x8a11020f#32), -- and x15, x16, x17
  (1052, 0xaa0f01ce#32), -- orr x14, x14, x15
  (1056, 0xf900016e#32), -- str x14, [x11]
  (1060, 0x5280002e#32), -- mov w14, #0x1 // =1
  (1064, 0xb5000d61#32), -- cbnz x1, 0x228ba4 <.LBB61_27>
  (1068, 0xd37ae5cf#32), -- lsl x15, x14, #6
  (1072, 0xd37afdd0#32), -- lsr x16, x14, #58
  (1076, 0xeb0f0091#32), -- subs x17, x4, x15
  (1080, 0xfa1000b2#32), -- sbcs x18, x5, x16
  (1084, 0x9a9133f1#32), -- csel x17, xzr, x17, lo
  (1088, 0x9a9233f2#32), -- csel x18, xzr, x18, lo
  (1092, 0xf101023f#32), -- cmp x17, #0x40
  (1096, 0x9a8c3231#32), -- csel x17, x17, x12, lo
  (1100, 0xf100025f#32), -- cmp x18, #0x0
  (1104, 0x1a8c0231#32), -- csel w17, w17, w12, eq
  (1108, 0xeb0f012f#32), -- subs x15, x9, x15
  (1112, 0xfa100110#32), -- sbcs x16, x8, x16
  (1116, 0x9ad121b2#32), -- lsl x18, x13, x17
  (1120, 0x9a8f33ef#32), -- csel x15, xzr, x15, lo
  (1124, 0x9a9033f0#32), -- csel x16, xzr, x16, lo
  (1128, 0xf10101ff#32), -- cmp x15, #0x40
  (1132, 0x9a8c31ef#32), -- csel x15, x15, x12, lo
  (1136, 0xf100021f#32), -- cmp x16, #0x0
  (1140, 0x1a8c01ef#32), -- csel w15, w15, w12, eq
  (1144, 0x9acf21b0#32), -- lsl x16, x13, x15
  (1148, 0x710101ff#32), -- cmp w15, #0x40
  (1152, 0x54000060#32), -- b.eq 0x228a5c <.Llower_arm_513>
  (1156, 0xaa3003ef#32), -- mvn x15, x16
  (1160, 0x14000002#32), -- b 0x228a60 <.Llower_arm_514>
  (1164, 0xaa0d03ef#32), -- mov x15, x13
  (1168, 0x7101023f#32), -- cmp w17, #0x40
  (1172, 0x910005d0#32), -- add x16, x14, #0x1
  (1176, 0x9a9203f1#32), -- csel x17, xzr, x18, eq
  (1180, 0xeb10015f#32), -- cmp x10, x16
  (1184, 0x8a1101ef#32), -- and x15, x15, x17
  (1188, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1192, 0xf90003e9#32), -- str x9, [sp]
  (1196, 0xaa0e03e9#32), -- mov x9, x14
  (1200, 0xd37df129#32), -- lsl x9, x9, #3
  (1204, 0x8b090169#32), -- add x9, x11, x9
  (1208, 0xf900012f#32), -- str x15, [x9]
  (1212, 0xf94003e9#32), -- ldr x9, [sp]
  (1216, 0x910043ff#32), -- add sp, sp, #0x10
  (1220, 0xaa1003ee#32), -- mov x14, x16
  (1224, 0x54fffb21#32), -- b.ne 0x2289fc <.LBB61_23>
  (1228, 0xa900280b#32), -- stp x11, x10, [x0]
  (1232, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1236, 0xf90003e9#32), -- str x9, [sp]
  (1240, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1244, 0x91000009#32), -- add x9, x0, #0x0
  (1248, 0x91010129#32), -- add x9, x9, #0x40
  (1252, 0x5280000a#32), -- mov w10, #0x0 // =0
  (1256, 0xb900012a#32), -- str w10, [x9]
  (1260, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1264, 0xf94003e9#32), -- ldr x9, [sp]
  (1268, 0x910043ff#32), -- add sp, sp, #0x10
  (1272, 0xd65f03c0#32), -- ret
  (1276, 0xd10043ff#32) -- sub sp, sp, #0x10
]

theorem chunk4_decodes :
    chunk4.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk5 : List (Nat × BitVec 32) := [
  (1280, 0xf90003e9#32), -- str x9, [sp]
  (1284, 0xaa0e03e9#32), -- mov x9, x14
  (1288, 0xd37df129#32), -- lsl x9, x9, #3
  (1292, 0x8b090029#32), -- add x9, x1, x9
  (1296, 0xf940012f#32), -- ldr x15, [x9]
  (1300, 0xf94003e9#32), -- ldr x9, [sp]
  (1304, 0x910043ff#32), -- add sp, sp, #0x10
  (1308, 0xd37ae5d0#32), -- lsl x16, x14, #6
  (1312, 0xd37afdd1#32), -- lsr x17, x14, #58
  (1316, 0xeb100092#32), -- subs x18, x4, x16
  (1320, 0xfa1100a3#32), -- sbcs x3, x5, x17
  (1324, 0x9a9233f2#32), -- csel x18, xzr, x18, lo
  (1328, 0x9a8333e3#32), -- csel x3, xzr, x3, lo
  (1332, 0xf101025f#32), -- cmp x18, #0x40
  (1336, 0x9a8c3252#32), -- csel x18, x18, x12, lo
  (1340, 0xf100007f#32), -- cmp x3, #0x0
  (1344, 0x1a8c0252#32), -- csel w18, w18, w12, eq
  (1348, 0xeb100130#32), -- subs x16, x9, x16
  (1352, 0xfa110111#32), -- sbcs x17, x8, x17
  (1356, 0x9ad221a3#32), -- lsl x3, x13, x18
  (1360, 0x9a9033f0#32), -- csel x16, xzr, x16, lo
  (1364, 0x9a9133f1#32), -- csel x17, xzr, x17, lo
  (1368, 0xf101021f#32), -- cmp x16, #0x40
  (1372, 0x9a8c3210#32), -- csel x16, x16, x12, lo
  (1376, 0xf100023f#32), -- cmp x17, #0x0
  (1380, 0x1a8c0210#32), -- csel w16, w16, w12, eq
  (1384, 0x9ad021b1#32), -- lsl x17, x13, x16
  (1388, 0x7101021f#32), -- cmp w16, #0x40
  (1392, 0x54000060#32), -- b.eq 0x228b4c <.Llower_arm_515>
  (1396, 0xaa3103f0#32), -- mvn x16, x17
  (1400, 0x14000002#32), -- b 0x228b50 <.Llower_arm_516>
  (1404, 0xaa0d03f0#32), -- mov x16, x13
  (1408, 0x7101025f#32), -- cmp w18, #0x40
  (1412, 0x54000060#32), -- b.eq 0x228b60 <.Llower_arm_517>
  (1416, 0xaa2303f1#32), -- mvn x17, x3
  (1420, 0x14000002#32), -- b 0x228b64 <.Llower_arm_518>
  (1424, 0xaa0d03f1#32), -- mov x17, x13
  (1428, 0x9a8303f2#32), -- csel x18, xzr, x3, eq
  (1432, 0x910005c3#32), -- add x3, x14, #0x1
  (1436, 0x8a1101ef#32), -- and x15, x15, x17
  (1440, 0x8a120210#32), -- and x16, x16, x18
  (1444, 0xeb03015f#32), -- cmp x10, x3
  (1448, 0xaa1001ef#32), -- orr x15, x15, x16
  (1452, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1456, 0xf90003e9#32), -- str x9, [sp]
  (1460, 0xaa0e03e9#32), -- mov x9, x14
  (1464, 0xd37df129#32), -- lsl x9, x9, #3
  (1468, 0x8b090169#32), -- add x9, x11, x9
  (1472, 0xf900012f#32), -- str x15, [x9]
  (1476, 0xf94003e9#32), -- ldr x9, [sp]
  (1480, 0x910043ff#32), -- add sp, sp, #0x10
  (1484, 0xaa0303ee#32), -- mov x14, x3
  (1488, 0x54fff7e0#32), -- b.eq 0x228a9c <.LBB61_24>
  (1492, 0xeb0201df#32), -- cmp x14, x2
  (1496, 0x54fff923#32), -- b.lo 0x228acc <.LBB61_25>
  (1500, 0xaa1f03ef#32), -- mov x15, xzr
  (1504, 0x17ffffcf#32) -- b 0x228aec <.LBB61_26>
]

theorem chunk5_decodes :
    chunk5.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete linked function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5

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

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, chunk3_decodes, chunk4_decodes, chunk5_decodes, Bool.and_self]

theorem step_at (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (row : Nat × BitVec 32) (member : row ∈ program)
    (entry : read_pc s = base + BitVec.ofNat 64 row.1)
    (error : read_err s = .None) :
    stepi s = exec_inst (SszArm.Codec.Linked.decoded program all_decode row member) s :=
  SszArm.Codec.Linked.step_at program all_decode s base code row member entry error

end SszArm.Indices.Linked.Rebase
