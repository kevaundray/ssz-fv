import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.PrefixEqual

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN13ssz_fv_native7indices12prefix_equal17h455af9025a76ffe0E. -/
def address : Nat := 2372468

def byteSize : Nat := 1564

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xb40002a0#32), -- cbz x0, 0x2433c8 <.LBB126_5>
  (4, 0xd1002008#32), -- sub x8, x0, #0x8
  (8, 0xaa0103eb#32), -- mov x11, x1
  (12, 0xb40005ab#32), -- cbz x11, 0x243434 <.LBB126_7>
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
  (56, 0xb4fffea9#32), -- cbz x9, 0x243380 <.LBB126_2>
  (60, 0xd37ae548#32), -- lsl x8, x10, #6
  (64, 0xd37afd4a#32), -- lsr x10, x10, #58
  (68, 0x9280000b#32), -- mov x11, #-0x1 // =-1
  (72, 0xf1010108#32), -- subs x8, x8, #0x40
  (76, 0x9a0b014a#32), -- adc x10, x10, x11
  (80, 0x14000007#32), -- b 0x2433e0 <.LBB126_6>
  (84, 0xaa1f03e8#32), -- mov x8, xzr
  (88, 0xaa1f03ea#32), -- mov x10, xzr
  (92, 0xaa1f03eb#32), -- mov x11, xzr
  (96, 0xaa1f03ec#32), -- mov x12, xzr
  (100, 0xaa0103e9#32), -- mov x9, x1
  (104, 0xb40002e1#32), -- cbz x1, 0x243438 <.LBB126_8>
  (108, 0xd10043ff#32), -- sub sp, sp, #0x10
  (112, 0xf90003ea#32), -- str x10, [sp]
  (116, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (120, 0xaa0903ea#32), -- mov x10, x9
  (124, 0xd280080b#32), -- mov x11, #0x40 // =64
  (128, 0xb400008a#32), -- cbz x10, 0x243404 <.Llower_arm_1090>
  (132, 0xd100056b#32), -- sub x11, x11, #0x1
  (136, 0xd341fd4a#32), -- lsr x10, x10, #1
  (140, 0xb5ffffca#32), -- cbnz x10, 0x2433f8 <.Llower_arm_1089>
  (144, 0xaa0b03e9#32), -- mov x9, x11
  (148, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (152, 0xf94003ea#32), -- ldr x10, [sp]
  (156, 0x910043ff#32), -- add sp, sp, #0x10
  (160, 0x5280080b#32), -- mov w11, #0x40 // =64
  (164, 0x4b090169#32), -- sub w9, w11, w9
  (168, 0xab09010b#32), -- adds x11, x8, x9
  (172, 0x54000062#32), -- b.hs 0x24342c <.Llower_arm_1091>
  (176, 0xaa0a03ec#32), -- mov x12, x10
  (180, 0x14000002#32), -- b 0x243430 <.Llower_arm_1092>
  (184, 0x9100054c#32), -- add x12, x10, #0x1
  (188, 0x14000002#32), -- b 0x243438 <.LBB126_8>
  (192, 0xaa1f03ec#32), -- mov x12, xzr
  (196, 0xa9bf4ff4#32), -- stp x20, x19, [sp, #-0x10]!
  (200, 0xeb020169#32), -- subs x9, x11, x2
  (204, 0xa9412fea#32), -- ldp x10, x11, [sp, #0x10]
  (208, 0xfa030188#32), -- sbcs x8, x12, x3
  (212, 0x9a8833e8#32), -- csel x8, xzr, x8, lo
  (216, 0x9a8933e9#32), -- csel x9, xzr, x9, lo
  (220, 0xb40002a5#32), -- cbz x5, 0x2434a4 <.LBB126_13>
  (224, 0xd10020ac#32), -- sub x12, x5, #0x8
  (228, 0xaa0603ef#32), -- mov x15, x6
  (232, 0xb40005af#32), -- cbz x15, 0x243510 <.LBB126_15>
  (236, 0xd10043ff#32), -- sub sp, sp, #0x10
  (240, 0xf90003e9#32), -- str x9, [sp]
  (244, 0xaa0f03e9#32), -- mov x9, x15
  (248, 0xd37df129#32), -- lsl x9, x9, #3
  (252, 0x8b090189#32) -- add x9, x12, x9
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0xf940012d#32), -- ldr x13, [x9]
  (260, 0xf94003e9#32), -- ldr x9, [sp]
  (264, 0x910043ff#32), -- add sp, sp, #0x10
  (268, 0xaa0f03ee#32), -- mov x14, x15
  (272, 0xd10005ef#32), -- sub x15, x15, #0x1
  (276, 0xb4fffead#32), -- cbz x13, 0x24345c <.LBB126_10>
  (280, 0xd37ae5cc#32), -- lsl x12, x14, #6
  (284, 0xd37afdce#32), -- lsr x14, x14, #58
  (288, 0x9280000f#32), -- mov x15, #-0x1 // =-1
  (292, 0xf101018c#32), -- subs x12, x12, #0x40
  (296, 0x9a0f01ce#32), -- adc x14, x14, x15
  (300, 0x14000007#32), -- b 0x2434bc <.LBB126_14>
  (304, 0xaa1f03ec#32), -- mov x12, xzr
  (308, 0xaa1f03ee#32), -- mov x14, xzr
  (312, 0xaa1f03ef#32), -- mov x15, xzr
  (316, 0xaa1f03f0#32), -- mov x16, xzr
  (320, 0xaa0603ed#32), -- mov x13, x6
  (324, 0xb40002e6#32), -- cbz x6, 0x243514 <.LBB126_16>
  (328, 0xd10043ff#32), -- sub sp, sp, #0x10
  (332, 0xf90003e9#32), -- str x9, [sp]
  (336, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (340, 0xaa0d03e9#32), -- mov x9, x13
  (344, 0xd280080a#32), -- mov x10, #0x40 // =64
  (348, 0xb4000089#32), -- cbz x9, 0x2434e0 <.Llower_arm_1094>
  (352, 0xd100054a#32), -- sub x10, x10, #0x1
  (356, 0xd341fd29#32), -- lsr x9, x9, #1
  (360, 0xb5ffffc9#32), -- cbnz x9, 0x2434d4 <.Llower_arm_1093>
  (364, 0xaa0a03ed#32), -- mov x13, x10
  (368, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (372, 0xf94003e9#32), -- ldr x9, [sp]
  (376, 0x910043ff#32), -- add sp, sp, #0x10
  (380, 0x5280080f#32), -- mov w15, #0x40 // =64
  (384, 0x4b0d01ed#32), -- sub w13, w15, w13
  (388, 0xab0d018f#32), -- adds x15, x12, x13
  (392, 0x54000062#32), -- b.hs 0x243508 <.Llower_arm_1095>
  (396, 0xaa0e03f0#32), -- mov x16, x14
  (400, 0x14000002#32), -- b 0x24350c <.Llower_arm_1096>
  (404, 0x910005d0#32), -- add x16, x14, #0x1
  (408, 0x14000002#32), -- b 0x243514 <.LBB126_16>
  (412, 0xaa1f03f0#32), -- mov x16, xzr
  (416, 0xeb0a01ec#32), -- subs x12, x15, x10
  (420, 0xfa0b020d#32), -- sbcs x13, x16, x11
  (424, 0x9a8d33ed#32), -- csel x13, xzr, x13, lo
  (428, 0x9a8c33ec#32), -- csel x12, xzr, x12, lo
  (432, 0xeb0d011f#32), -- cmp x8, x13
  (436, 0xd10043ff#32), -- sub sp, sp, #0x10
  (440, 0xf90003ea#32), -- str x10, [sp]
  (444, 0x54000080#32), -- b.eq 0x243540 <.Llower_arm_1097>
  (448, 0x5280002a#32), -- mov w10, #0x1 // =1
  (452, 0x2b1f015f#32), -- cmn w10, wzr
  (456, 0x14000002#32), -- b 0x243544 <.Llower_arm_1098>
  (460, 0xeb0c013f#32), -- cmp x9, x12
  (464, 0xf94003ea#32), -- ldr x10, [sp]
  (468, 0x910043ff#32), -- add sp, sp, #0x10
  (472, 0x54000501#32), -- b.ne 0x2435ec <.LBB126_25>
  (476, 0xb100fd29#32), -- adds x9, x9, #0x3f
  (480, 0x4b0a03ec#32), -- neg w12, w10
  (484, 0x54000062#32), -- b.hs 0x243564 <.Llower_arm_1099>
  (488, 0xaa0803e8#32), -- mov x8, x8
  (492, 0x14000002#32), -- b 0x243568 <.Llower_arm_1100>
  (496, 0x91000508#32), -- add x8, x8, #0x1
  (500, 0xf100fc7f#32), -- cmp x3, #0x3f
  (504, 0x1200158c#32), -- and w12, w12, #0x3f
  (508, 0xd10043ff#32) -- sub sp, sp, #0x10
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xf90003ea#32), -- str x10, [sp]
  (516, 0xd346fd2a#32), -- lsr x10, x9, #6
  (520, 0xaa08e948#32), -- orr x8, x10, x8, lsl #58
  (524, 0xf94003ea#32), -- ldr x10, [sp]
  (528, 0x910043ff#32), -- add sp, sp, #0x10
  (532, 0xd10043ff#32), -- sub sp, sp, #0x10
  (536, 0xf90003ec#32), -- str x12, [sp]
  (540, 0xd346fd4c#32), -- lsr x12, x10, #6
  (544, 0xaa0be989#32), -- orr x9, x12, x11, lsl #58
  (548, 0xf94003ec#32), -- ldr x12, [sp]
  (552, 0x910043ff#32), -- add sp, sp, #0x10
  (556, 0x1200154a#32), -- and w10, w10, #0x3f
  (560, 0x540002a9#32), -- b.ls 0x2435f8 <.LBB126_26>
  (564, 0xf101017f#32), -- cmp x11, #0x40
  (568, 0x54000f63#32), -- b.lo 0x243798 <.LBB126_52>
  (572, 0xaa1f03ea#32), -- mov x10, xzr
  (576, 0xeb0a011f#32), -- cmp x8, x10
  (580, 0x54001de0#32), -- b.eq 0x243974 <.LBB126_79>
  (584, 0xaa0a03e9#32), -- mov x9, x10
  (588, 0x9100054a#32), -- add x10, x10, #0x1
  (592, 0x34ffff84#32), -- cbz w4, 0x2435b4 <.LBB126_20>
  (596, 0xb5ffff69#32), -- cbnz x9, 0x2435b4 <.LBB126_20>
  (600, 0xaa1f03ed#32), -- mov x13, xzr
  (604, 0xeb0801bf#32), -- cmp x13, x8
  (608, 0x54000062#32), -- b.hs 0x2435e0 <.Llower_arm_1101>
  (612, 0x52800000#32), -- mov w0, #0x0 // =0
  (616, 0x14000002#32), -- b 0x2435e4 <.Llower_arm_1102>
  (620, 0x52800020#32), -- mov w0, #0x1 // =1
  (624, 0xa8c14ff4#32), -- ldp x20, x19, [sp], #0x10
  (628, 0xd65f03c0#32), -- ret
  (632, 0x2a1f03e0#32), -- mov w0, wzr
  (636, 0xa8c14ff4#32), -- ldp x20, x19, [sp], #0x10
  (640, 0xd65f03c0#32), -- ret
  (644, 0xd10043ff#32), -- sub sp, sp, #0x10
  (648, 0xf90003e9#32), -- str x9, [sp]
  (652, 0xd346fc49#32), -- lsr x9, x2, #6
  (656, 0xaa03e92e#32), -- orr x14, x9, x3, lsl #58
  (660, 0xf94003e9#32), -- ldr x9, [sp]
  (664, 0x910043ff#32), -- add sp, sp, #0x10
  (668, 0x8b090cb2#32), -- add x18, x5, x9, lsl #3
  (672, 0x4b0203ed#32), -- neg w13, w2
  (676, 0x1200144f#32), -- and w15, w2, #0x3f
  (680, 0x120015b0#32), -- and w16, w13, #0x3f
  (684, 0xcb0803f1#32), -- neg x17, x8
  (688, 0x8b0e0c03#32), -- add x3, x0, x14, lsl #3
  (692, 0x91002252#32), -- add x18, x18, #0x8
  (696, 0x9280000d#32), -- mov x13, #-0x1 // =-1
  (700, 0x91002062#32), -- add x2, x3, #0x8
  (704, 0x14000009#32), -- b 0x243658 <.LBB126_29>
  (708, 0xaa1f03e7#32), -- mov x7, xzr
  (712, 0xb10005ad#32), -- adds x13, x13, #0x1
  (716, 0x91002252#32), -- add x18, x18, #0x8
  (720, 0x91002042#32), -- add x2, x2, #0x8
  (724, 0x1a8433f3#32), -- csel w19, wzr, w4, lo
  (728, 0xca130063#32), -- eor x3, x3, x19
  (732, 0xeb07007f#32), -- cmp x3, x7
  (736, 0x54fffbe1#32), -- b.ne 0x2435d0 <.LBB126_24>
  (740, 0x8b0d0223#32), -- add x3, x17, x13
  (744, 0xb100047f#32), -- cmn x3, #0x1
  (748, 0x540018a0#32), -- b.eq 0x243974 <.LBB126_79>
  (752, 0x8b0d01c3#32), -- add x3, x14, x13
  (756, 0x91000467#32), -- add x7, x3, #0x1
  (760, 0xeb0e00ff#32), -- cmp x7, x14
  (764, 0x540008c3#32) -- b.lo 0x243788 <.LBB126_51>
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0xb40001a0#32), -- cbz x0, 0x2436a8 <.LBB126_34>
  (772, 0xeb0100ff#32), -- cmp x7, x1
  (776, 0x54000222#32), -- b.hs 0x2436c0 <.LBB126_35>
  (780, 0xd10043ff#32), -- sub sp, sp, #0x10
  (784, 0xf90003e9#32), -- str x9, [sp]
  (788, 0x91000049#32), -- add x9, x2, #0x0
  (792, 0xd1002129#32), -- sub x9, x9, #0x8
  (796, 0xf9400123#32), -- ldr x3, [x9]
  (800, 0xf94003e9#32), -- ldr x9, [sp]
  (804, 0x910043ff#32), -- add sp, sp, #0x10
  (808, 0x9acf2463#32), -- lsr x3, x3, x15
  (812, 0x3500014f#32), -- cbnz w15, 0x2436c8 <.LBB126_36>
  (816, 0x14000013#32), -- b 0x2436f0 <.LBB126_40>
  (820, 0xb100047f#32), -- cmn x3, #0x1
  (824, 0xaa1f03e7#32), -- mov x7, xzr
  (828, 0x9a9f0023#32), -- csel x3, x1, xzr, eq
  (832, 0x9acf2463#32), -- lsr x3, x3, x15
  (836, 0x3500018f#32), -- cbnz w15, 0x2436e8 <.LBB126_39>
  (840, 0x1400000d#32), -- b 0x2436f0 <.LBB126_40>
  (844, 0x9acf27e3#32), -- lsr x3, xzr, x15
  (848, 0x3400016f#32), -- cbz w15, 0x2436f0 <.LBB126_40>
  (852, 0xb10004ff#32), -- cmn x7, #0x1
  (856, 0xaa1f03e7#32), -- mov x7, xzr
  (860, 0x540000c0#32), -- b.eq 0x2436e8 <.LBB126_39>
  (864, 0x8b0d01d3#32), -- add x19, x14, x13
  (868, 0x91000a73#32), -- add x19, x19, #0x2
  (872, 0xeb01027f#32), -- cmp x19, x1
  (876, 0x54000042#32), -- b.hs 0x2436e8 <.LBB126_39>
  (880, 0xf9400047#32), -- ldr x7, [x2]
  (884, 0x9ad020e7#32), -- lsl x7, x7, x16
  (888, 0xaa070063#32), -- orr x3, x3, x7
  (892, 0xf100fd7f#32), -- cmp x11, #0x3f
  (896, 0x54fffa28#32), -- b.hi 0x243638 <.LBB126_27>
  (900, 0x8b0d0127#32), -- add x7, x9, x13
  (904, 0x910004f3#32), -- add x19, x7, #0x1
  (908, 0xeb09027f#32), -- cmp x19, x9
  (912, 0x54fff9a3#32), -- b.lo 0x243638 <.LBB126_27>
  (916, 0xb40001a5#32), -- cbz x5, 0x24373c <.LBB126_45>
  (920, 0xeb06027f#32), -- cmp x19, x6
  (924, 0x54000222#32), -- b.hs 0x243754 <.LBB126_46>
  (928, 0xd10043ff#32), -- sub sp, sp, #0x10
  (932, 0xf90003e9#32), -- str x9, [sp]
  (936, 0x91000249#32), -- add x9, x18, #0x0
  (940, 0xd1002129#32), -- sub x9, x9, #0x8
  (944, 0xf9400127#32), -- ldr x7, [x9]
  (948, 0xf94003e9#32), -- ldr x9, [sp]
  (952, 0x910043ff#32), -- add sp, sp, #0x10
  (956, 0x9aca24e7#32), -- lsr x7, x7, x10
  (960, 0x3500014a#32), -- cbnz w10, 0x24375c <.LBB126_47>
  (964, 0x17ffffc1#32), -- b 0x24363c <.LBB126_28>
  (968, 0xb10004ff#32), -- cmn x7, #0x1
  (972, 0xaa1f03f3#32), -- mov x19, xzr
  (976, 0x9a9f00c7#32), -- csel x7, x6, xzr, eq
  (980, 0x9aca24e7#32), -- lsr x7, x7, x10
  (984, 0x3500018a#32), -- cbnz w10, 0x24377c <.LBB126_50>
  (988, 0x17ffffbb#32), -- b 0x24363c <.LBB126_28>
  (992, 0x9aca27e7#32), -- lsr x7, xzr, x10
  (996, 0x34fff72a#32), -- cbz w10, 0x24363c <.LBB126_28>
  (1000, 0xb100067f#32), -- cmn x19, #0x1
  (1004, 0xaa1f03f3#32), -- mov x19, xzr
  (1008, 0x540000c0#32), -- b.eq 0x24377c <.LBB126_50>
  (1012, 0x8b0d0134#32), -- add x20, x9, x13
  (1016, 0x91000a94#32), -- add x20, x20, #0x2
  (1020, 0xeb06029f#32) -- cmp x20, x6
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk4 : List (Nat × BitVec 32) := [
  (1024, 0x54000042#32), -- b.hs 0x24377c <.LBB126_50>
  (1028, 0xf9400253#32), -- ldr x19, [x18]
  (1032, 0x9acc2273#32), -- lsl x19, x19, x12
  (1036, 0xaa1300e7#32), -- orr x7, x7, x19
  (1040, 0x17ffffae#32), -- b 0x24363c <.LBB126_28>
  (1044, 0xaa1f03e3#32), -- mov x3, xzr
  (1048, 0xf100fd7f#32), -- cmp x11, #0x3f
  (1052, 0x54fffb49#32), -- b.ls 0x2436f8 <.LBB126_41>
  (1056, 0x17ffffa9#32), -- b 0x243638 <.LBB126_27>
  (1060, 0xb4000625#32), -- cbz x5, 0x24385c <.LBB126_64>
  (1064, 0x340008ea#32), -- cbz w10, 0x2438b8 <.LBB126_69>
  (1068, 0x8b090cad#32), -- add x13, x5, x9, lsl #3
  (1072, 0xaa1f03eb#32), -- mov x11, xzr
  (1076, 0x910021ad#32), -- add x13, x13, #0x8
  (1080, 0x1400000a#32), -- b 0x2437d4 <.LBB126_56>
  (1084, 0x9aca25ce#32), -- lsr x14, x14, x10
  (1088, 0x9acc21ef#32), -- lsl x15, x15, x12
  (1092, 0xaa0f01ce#32), -- orr x14, x14, x15
  (1096, 0xf100017f#32), -- cmp x11, #0x0
  (1100, 0x910021ad#32), -- add x13, x13, #0x8
  (1104, 0x9100056b#32), -- add x11, x11, #0x1
  (1108, 0x1a8413ef#32), -- csel w15, wzr, w4, ne
  (1112, 0xeb0f01df#32), -- cmp x14, x15
  (1116, 0x54000c21#32), -- b.ne 0x243954 <.LBB126_78>
  (1120, 0xeb0b011f#32), -- cmp x8, x11
  (1124, 0x54000ce0#32), -- b.eq 0x243974 <.LBB126_79>
  (1128, 0xab0b012f#32), -- adds x15, x9, x11
  (1132, 0x54000302#32), -- b.hs 0x243840 <.LBB126_63>
  (1136, 0xeb0601ff#32), -- cmp x15, x6
  (1140, 0x54000182#32), -- b.hs 0x243818 <.LBB126_60>
  (1144, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1148, 0xf90003e9#32), -- str x9, [sp]
  (1152, 0x910001a9#32), -- add x9, x13, #0x0
  (1156, 0xd1002129#32), -- sub x9, x9, #0x8
  (1160, 0xf940012e#32), -- ldr x14, [x9]
  (1164, 0xf94003e9#32), -- ldr x9, [sp]
  (1168, 0x910043ff#32), -- add sp, sp, #0x10
  (1172, 0x910005f0#32), -- add x16, x15, #0x1
  (1176, 0xaa1f03ef#32), -- mov x15, xzr
  (1180, 0xb50000d0#32), -- cbnz x16, 0x243828 <.LBB126_61>
  (1184, 0x17ffffe7#32), -- b 0x2437b0 <.LBB126_55>
  (1188, 0xaa1f03ee#32), -- mov x14, xzr
  (1192, 0x910005f0#32), -- add x16, x15, #0x1
  (1196, 0xaa1f03ef#32), -- mov x15, xzr
  (1200, 0xb4fffc70#32), -- cbz x16, 0x2437b0 <.LBB126_55>
  (1204, 0x8b0b0130#32), -- add x16, x9, x11
  (1208, 0x91000610#32), -- add x16, x16, #0x1
  (1212, 0xeb06021f#32), -- cmp x16, x6
  (1216, 0x54fffbe2#32), -- b.hs 0x2437b0 <.LBB126_55>
  (1220, 0xf94001af#32), -- ldr x15, [x13]
  (1224, 0x17ffffdd#32), -- b 0x2437b0 <.LBB126_55>
  (1228, 0xf100017f#32), -- cmp x11, #0x0
  (1232, 0x910021ad#32), -- add x13, x13, #0x8
  (1236, 0x9100056b#32), -- add x11, x11, #0x1
  (1240, 0x1a8413ef#32), -- csel w15, wzr, w4, ne
  (1244, 0xeb0f03ff#32), -- cmp xzr, x15
  (1248, 0x54fffc00#32), -- b.eq 0x2437d4 <.LBB126_56>
  (1252, 0x1400003f#32), -- b 0x243954 <.LBB126_78>
  (1256, 0x3400062a#32), -- cbz w10, 0x243920 <.LBB126_75>
  (1260, 0xaa1f03eb#32), -- mov x11, xzr
  (1264, 0xeb0b011f#32), -- cmp x8, x11
  (1268, 0x54000860#32), -- b.eq 0x243974 <.LBB126_79>
  (1272, 0xab0b013f#32), -- cmn x9, x11
  (1276, 0x9a9f00cc#32) -- csel x12, x6, xzr, eq
]

theorem chunk4_decodes :
    chunk4.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk5 : List (Nat × BitVec 32) := [
  (1280, 0xab0b013f#32), -- cmn x9, x11
  (1284, 0x9aca258c#32), -- lsr x12, x12, x10
  (1288, 0x9a8c23ed#32), -- csel x13, xzr, x12, hs
  (1292, 0xf100017f#32), -- cmp x11, #0x0
  (1296, 0x9100056c#32), -- add x12, x11, #0x1
  (1300, 0x1a8413ee#32), -- csel w14, wzr, w4, ne
  (1304, 0xaa0c03eb#32), -- mov x11, x12
  (1308, 0xeb0e01bf#32), -- cmp x13, x14
  (1312, 0x54fffe80#32), -- b.eq 0x243864 <.LBB126_66>
  (1316, 0xd100058d#32), -- sub x13, x12, #0x1
  (1320, 0xeb0801bf#32), -- cmp x13, x8
  (1324, 0x54000062#32), -- b.hs 0x2438ac <.Llower_arm_1103>
  (1328, 0x52800000#32), -- mov w0, #0x0 // =0
  (1332, 0x14000002#32), -- b 0x2438b0 <.Llower_arm_1104>
  (1336, 0x52800020#32), -- mov w0, #0x1 // =1
  (1340, 0xa8c14ff4#32), -- ldp x20, x19, [sp], #0x10
  (1344, 0xd65f03c0#32), -- ret
  (1348, 0xcb0803ea#32), -- neg x10, x8
  (1352, 0x9280000d#32), -- mov x13, #-0x1 // =-1
  (1356, 0xaa0903eb#32), -- mov x11, x9
  (1360, 0x14000006#32), -- b 0x2438dc <.LBB126_71>
  (1364, 0xb10005ad#32), -- adds x13, x13, #0x1
  (1368, 0x9100056b#32), -- add x11, x11, #0x1
  (1372, 0x1a8433ee#32), -- csel w14, wzr, w4, lo
  (1376, 0xeb0e019f#32), -- cmp x12, x14
  (1380, 0x54ffe7c1#32), -- b.ne 0x2435d0 <.LBB126_24>
  (1384, 0x8b0d014c#32), -- add x12, x10, x13
  (1388, 0xb100059f#32), -- cmn x12, #0x1
  (1392, 0x54000480#32), -- b.eq 0x243974 <.LBB126_79>
  (1396, 0xeb09017f#32), -- cmp x11, x9
  (1400, 0xaa1f03ec#32), -- mov x12, xzr
  (1404, 0x54fffec3#32), -- b.lo 0x2438c8 <.LBB126_70>
  (1408, 0xeb06017f#32), -- cmp x11, x6
  (1412, 0x54fffe82#32), -- b.hs 0x2438c8 <.LBB126_70>
  (1416, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1420, 0xf90003e9#32), -- str x9, [sp]
  (1424, 0xaa0b03e9#32), -- mov x9, x11
  (1428, 0xd37df129#32), -- lsl x9, x9, #3
  (1432, 0x8b0900a9#32), -- add x9, x5, x9
  (1436, 0xf940012c#32), -- ldr x12, [x9]
  (1440, 0xf94003e9#32), -- ldr x9, [sp]
  (1444, 0x910043ff#32), -- add sp, sp, #0x10
  (1448, 0x17ffffeb#32), -- b 0x2438c8 <.LBB126_70>
  (1452, 0xaa1f03ea#32), -- mov x10, xzr
  (1456, 0xeb0a011f#32), -- cmp x8, x10
  (1460, 0x54000260#32), -- b.eq 0x243974 <.LBB126_79>
  (1464, 0xab0a013f#32), -- cmn x9, x10
  (1468, 0x9a9f00cb#32), -- csel x11, x6, xzr, eq
  (1472, 0xab0a013f#32), -- cmn x9, x10
  (1476, 0x9a8b23ec#32), -- csel x12, xzr, x11, hs
  (1480, 0xf100015f#32), -- cmp x10, #0x0
  (1484, 0x9100054b#32), -- add x11, x10, #0x1
  (1488, 0x1a8413ed#32), -- csel w13, wzr, w4, ne
  (1492, 0xaa0b03ea#32), -- mov x10, x11
  (1496, 0xeb0d019f#32), -- cmp x12, x13
  (1500, 0x54fffea0#32), -- b.eq 0x243924 <.LBB126_76>
  (1504, 0xd100056d#32), -- sub x13, x11, #0x1
  (1508, 0xeb0801bf#32), -- cmp x13, x8
  (1512, 0x54000062#32), -- b.hs 0x243968 <.Llower_arm_1105>
  (1516, 0x52800000#32), -- mov w0, #0x0 // =0
  (1520, 0x14000002#32), -- b 0x24396c <.Llower_arm_1106>
  (1524, 0x52800020#32), -- mov w0, #0x1 // =1
  (1528, 0xa8c14ff4#32), -- ldp x20, x19, [sp], #0x10
  (1532, 0xd65f03c0#32) -- ret
]

theorem chunk5_decodes :
    chunk5.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk6 : List (Nat × BitVec 32) := [
  (1536, 0xeb08011f#32), -- cmp x8, x8
  (1540, 0x54000062#32), -- b.hs 0x243984 <.Llower_arm_1107>
  (1544, 0x52800000#32), -- mov w0, #0x0 // =0
  (1548, 0x14000002#32), -- b 0x243988 <.Llower_arm_1108>
  (1552, 0x52800020#32), -- mov w0, #0x1 // =1
  (1556, 0xa8c14ff4#32), -- ldp x20, x19, [sp], #0x10
  (1560, 0xd65f03c0#32) -- ret
]

theorem chunk6_decodes :
    chunk6.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete linked function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6

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

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, chunk3_decodes, chunk4_decodes, chunk5_decodes, chunk6_decodes, Bool.and_self]

theorem step_at (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (row : Nat × BitVec 32) (member : row ∈ program)
    (entry : read_pc s = base + BitVec.ofNat 64 row.1)
    (error : read_err s = .None) :
    stepi s = exec_inst (SszArm.Codec.Linked.decoded program all_decode row member) s :=
  SszArm.Codec.Linked.step_at program all_decode s base code row member entry error

end SszArm.Indices.Linked.PrefixEqual
