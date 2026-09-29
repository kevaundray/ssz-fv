import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.NatShr

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN13ssz_fv_native3nat3Nat3shr17he988a53a952ee485E. -/
def address : Nat := 2265780

def byteSize : Nat := 1500

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xb40002a1#32), -- cbz x1, 0x229308 <.LBB63_5>
  (4, 0xd1002029#32), -- sub x9, x1, #0x8
  (8, 0xaa0203eb#32), -- mov x11, x2
  (12, 0xb4000a6b#32), -- cbz x11, 0x22940c <.LBB63_14>
  (16, 0xd10043ff#32), -- sub sp, sp, #0x10
  (20, 0xf90003ea#32), -- str x10, [sp]
  (24, 0xaa0b03ea#32), -- mov x10, x11
  (28, 0xd37df14a#32), -- lsl x10, x10, #3
  (32, 0x8b0a012a#32), -- add x10, x9, x10
  (36, 0xf9400148#32), -- ldr x8, [x10]
  (40, 0xf94003ea#32), -- ldr x10, [sp]
  (44, 0x910043ff#32), -- add sp, sp, #0x10
  (48, 0xaa0b03ea#32), -- mov x10, x11
  (52, 0xd100056b#32), -- sub x11, x11, #0x1
  (56, 0xb4fffea8#32), -- cbz x8, 0x2292c0 <.LBB63_2>
  (60, 0xd37ae549#32), -- lsl x9, x10, #6
  (64, 0xd37afd4a#32), -- lsr x10, x10, #58
  (68, 0x9280000b#32), -- mov x11, #-0x1 // =-1
  (72, 0xf1010129#32), -- subs x9, x9, #0x40
  (76, 0x9a0b014a#32), -- adc x10, x10, x11
  (80, 0x14000005#32), -- b 0x229318 <.LBB63_7>
  (84, 0xb4000822#32), -- cbz x2, 0x22940c <.LBB63_14>
  (88, 0xaa1f03e9#32), -- mov x9, xzr
  (92, 0xaa1f03ea#32), -- mov x10, xzr
  (96, 0xaa0203e8#32), -- mov x8, x2
  (100, 0xd10043ff#32), -- sub sp, sp, #0x10
  (104, 0xf90003e9#32), -- str x9, [sp]
  (108, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (112, 0xaa0803e9#32), -- mov x9, x8
  (116, 0xd280080a#32), -- mov x10, #0x40 // =64
  (120, 0xb4000089#32), -- cbz x9, 0x22933c <.Llower_arm_532>
  (124, 0xd100054a#32), -- sub x10, x10, #0x1
  (128, 0xd341fd29#32), -- lsr x9, x9, #1
  (132, 0xb5ffffc9#32), -- cbnz x9, 0x229330 <.Llower_arm_531>
  (136, 0xaa0a03e8#32), -- mov x8, x10
  (140, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (144, 0xf94003e9#32), -- ldr x9, [sp]
  (148, 0x910043ff#32), -- add sp, sp, #0x10
  (152, 0x5280080b#32), -- mov w11, #0x40 // =64
  (156, 0x4b080168#32), -- sub w8, w11, w8
  (160, 0xab080128#32), -- adds x8, x9, x8
  (164, 0x54000062#32), -- b.hs 0x229364 <.Llower_arm_533>
  (168, 0xaa0a03e9#32), -- mov x9, x10
  (172, 0x14000002#32), -- b 0x229368 <.Llower_arm_534>
  (176, 0x91000549#32), -- add x9, x10, #0x1
  (180, 0xeb08009f#32), -- cmp x4, x8
  (184, 0xfa0900bf#32), -- sbcs xzr, x5, x9
  (188, 0x540004e2#32), -- b.hs 0x22940c <.LBB63_14>
  (192, 0xaa05008a#32), -- orr x10, x4, x5
  (196, 0xb400076a#32), -- cbz x10, 0x229464 <.LBB63_15>
  (200, 0xeb04010a#32), -- subs x10, x8, x4
  (204, 0xda050128#32), -- sbc x8, x9, x5
  (208, 0xf101055f#32), -- cmp x10, #0x41
  (212, 0xfa1f011f#32), -- sbcs xzr, x8, xzr
  (216, 0x54000bc2#32), -- b.hs 0x229504 <.LBB63_21>
  (220, 0xb4001fc1#32), -- cbz x1, 0x229788 <.LBB63_42>
  (224, 0xb40022c2#32), -- cbz x2, 0x2297ec <.LBB63_44>
  (228, 0xf9400028#32), -- ldr x8, [x1]
  (232, 0xf100045f#32), -- cmp x2, #0x1
  (236, 0x9ac42508#32), -- lsr x8, x8, x4
  (240, 0x54001f40#32), -- b.eq 0x22978c <.LBB63_43>
  (244, 0xf940042a#32), -- ldr x10, [x1, #0x8]
  (248, 0x4b0403eb#32), -- neg w11, w4
  (252, 0xd10043ff#32) -- sub sp, sp, #0x10
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0xf90003e9#32), -- str x9, [sp]
  (260, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (264, 0x91000009#32), -- add x9, x0, #0x0
  (268, 0x91010129#32), -- add x9, x9, #0x40
  (272, 0x5280000a#32), -- mov w10, #0x0 // =0
  (276, 0xb900012a#32), -- str w10, [x9]
  (280, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (284, 0xf94003e9#32), -- ldr x9, [sp]
  (288, 0x910043ff#32), -- add sp, sp, #0x10
  (292, 0x9acb214a#32), -- lsl x10, x10, x11
  (296, 0xaa080148#32), -- orr x8, x10, x8
  (300, 0xd10043ff#32), -- sub sp, sp, #0x10
  (304, 0xf90003e9#32), -- str x9, [sp]
  (308, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (312, 0x91000009#32), -- add x9, x0, #0x0
  (316, 0xd280000a#32), -- mov x10, #0x0 // =0
  (320, 0xf900012a#32), -- str x10, [x9]
  (324, 0xf9000528#32), -- str x8, [x9, #0x8]
  (328, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (332, 0xf94003e9#32), -- ldr x9, [sp]
  (336, 0x910043ff#32), -- add sp, sp, #0x10
  (340, 0xd65f03c0#32), -- ret
  (344, 0xd10043ff#32), -- sub sp, sp, #0x10
  (348, 0xf90003e9#32), -- str x9, [sp]
  (352, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (356, 0x91000009#32), -- add x9, x0, #0x0
  (360, 0xd280000a#32), -- mov x10, #0x0 // =0
  (364, 0xf900012a#32), -- str x10, [x9]
  (368, 0xd280000a#32), -- mov x10, #0x0 // =0
  (372, 0xf900052a#32), -- str x10, [x9, #0x8]
  (376, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (380, 0xf94003e9#32), -- ldr x9, [sp]
  (384, 0x910043ff#32), -- add sp, sp, #0x10
  (388, 0xd10043ff#32), -- sub sp, sp, #0x10
  (392, 0xf90003e9#32), -- str x9, [sp]
  (396, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (400, 0x91000009#32), -- add x9, x0, #0x0
  (404, 0x91010129#32), -- add x9, x9, #0x40
  (408, 0x5280000a#32), -- mov w10, #0x0 // =0
  (412, 0xb900012a#32), -- str w10, [x9]
  (416, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (420, 0xf94003e9#32), -- ldr x9, [sp]
  (424, 0x910043ff#32), -- add sp, sp, #0x10
  (428, 0xd65f03c0#32), -- ret
  (432, 0xb4001161#32), -- cbz x1, 0x229690 <.LBB63_40>
  (436, 0xd1000449#32), -- sub x9, x2, #0x1
  (440, 0xb100053f#32), -- cmn x9, #0x1
  (444, 0x540010c0#32), -- b.eq 0x229688 <.LBB63_39>
  (448, 0xd10043ff#32), -- sub sp, sp, #0x10
  (452, 0xf90003eb#32), -- str x11, [sp]
  (456, 0xaa0903eb#32), -- mov x11, x9
  (460, 0xd37df16b#32), -- lsl x11, x11, #3
  (464, 0x8b0b002b#32), -- add x11, x1, x11
  (468, 0xf940016a#32), -- ldr x10, [x11]
  (472, 0xf94003eb#32), -- ldr x11, [sp]
  (476, 0x910043ff#32), -- add sp, sp, #0x10
  (480, 0xaa0903e8#32), -- mov x8, x9
  (484, 0xd1000529#32), -- sub x9, x9, #0x1
  (488, 0xb4fffe8a#32), -- cbz x10, 0x22946c <.LBB63_17>
  (492, 0x91000502#32), -- add x2, x8, #0x1
  (496, 0xf100045f#32), -- cmp x2, #0x1
  (500, 0x54000f41#32), -- b.ne 0x229690 <.LBB63_40>
  (504, 0xf9400022#32), -- ldr x2, [x1]
  (508, 0xd10043ff#32) -- sub sp, sp, #0x10
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xf90003e9#32), -- str x9, [sp]
  (516, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (520, 0x91000009#32), -- add x9, x0, #0x0
  (524, 0xd280000a#32), -- mov x10, #0x0 // =0
  (528, 0xf900012a#32), -- str x10, [x9]
  (532, 0xf9000522#32), -- str x2, [x9, #0x8]
  (536, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (540, 0xf94003e9#32), -- ldr x9, [sp]
  (544, 0x910043ff#32), -- add sp, sp, #0x10
  (548, 0xd10043ff#32), -- sub sp, sp, #0x10
  (552, 0xf90003e9#32), -- str x9, [sp]
  (556, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (560, 0x91000009#32), -- add x9, x0, #0x0
  (564, 0x91010129#32), -- add x9, x9, #0x40
  (568, 0x5280000a#32), -- mov w10, #0x0 // =0
  (572, 0xb900012a#32), -- str w10, [x9]
  (576, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (580, 0xf94003e9#32), -- ldr x9, [sp]
  (584, 0x910043ff#32), -- add sp, sp, #0x10
  (588, 0xd65f03c0#32), -- ret
  (592, 0xf1000549#32), -- subs x9, x10, #0x1
  (596, 0x9280000a#32), -- mov x10, #-0x1 // =-1
  (600, 0x9a0a0108#32), -- adc x8, x8, x10
  (604, 0xd10043ff#32), -- sub sp, sp, #0x10
  (608, 0xf90003ea#32), -- str x10, [sp]
  (612, 0xd346fd2a#32), -- lsr x10, x9, #6
  (616, 0xaa08e949#32), -- orr x9, x10, x8, lsl #58
  (620, 0xf94003ea#32), -- ldr x10, [sp]
  (624, 0x910043ff#32), -- add sp, sp, #0x10
  (628, 0xb1000528#32), -- adds x8, x9, #0x1
  (632, 0x540001c3#32), -- b.lo 0x229564 <.LBB63_24>
  (636, 0x5280010a#32), -- mov w10, #0x8 // =8
  (640, 0xa900200a#32), -- stp x10, x8, [x0]
  (644, 0xd10043ff#32), -- sub sp, sp, #0x10
  (648, 0xf90003e9#32), -- str x9, [sp]
  (652, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (656, 0x91000009#32), -- add x9, x0, #0x0
  (660, 0x91010129#32), -- add x9, x9, #0x40
  (664, 0x5280000a#32), -- mov w10, #0x0 // =0
  (668, 0xb900012a#32), -- str w10, [x9]
  (672, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (676, 0xf94003e9#32), -- ldr x9, [sp]
  (680, 0x910043ff#32), -- add sp, sp, #0x10
  (684, 0xd65f03c0#32), -- ret
  (688, 0xd37dfd0a#32), -- lsr x10, x8, #61
  (692, 0xb5000aca#32), -- cbnz x10, 0x2296c0 <.LBB63_41>
  (696, 0xd37df10c#32), -- lsl x12, x8, #3
  (700, 0xd10043ff#32), -- sub sp, sp, #0x10
  (704, 0xf90003e9#32), -- str x9, [sp]
  (708, 0x92410189#32), -- and x9, x12, #0x8000000000000000
  (712, 0xb5000089#32), -- cbnz x9, 0x22958c <.Llower_arm_535>
  (716, 0xf94003e9#32), -- ldr x9, [sp]
  (720, 0x910043ff#32), -- add sp, sp, #0x10
  (724, 0x14000004#32), -- b 0x229598 <.Llower_arm_536>
  (728, 0xf94003e9#32), -- ldr x9, [sp]
  (732, 0x910043ff#32), -- add sp, sp, #0x10
  (736, 0x1400004b#32), -- b 0x2296c0 <.LBB63_41>
  (740, 0xf94000ca#32), -- ldr x10, [x6]
  (744, 0xf94008cd#32), -- ldr x13, [x6, #0x10]
  (748, 0xab0a01ae#32), -- adds x14, x13, x10
  (752, 0x540008e2#32), -- b.hs 0x2296c0 <.LBB63_41>
  (756, 0xb10021df#32), -- cmn x14, #0x8
  (760, 0x540008a8#32), -- b.hi 0x2296c0 <.LBB63_41>
  (764, 0x91001dcb#32) -- add x11, x14, #0x7
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0x927df16b#32), -- and x11, x11, #0xfffffffffffffff8
  (772, 0xcb0e016e#32), -- sub x14, x11, x14
  (776, 0xab0d01cd#32), -- adds x13, x14, x13
  (780, 0x54000802#32), -- b.hs 0x2296c0 <.LBB63_41>
  (784, 0xab0c01ac#32), -- adds x12, x13, x12
  (788, 0x540007c2#32), -- b.hs 0x2296c0 <.LBB63_41>
  (792, 0xf94004ce#32), -- ldr x14, [x6, #0x8]
  (796, 0xeb0e019f#32), -- cmp x12, x14
  (800, 0x54000768#32), -- b.hi 0x2296c0 <.LBB63_41>
  (804, 0x8b0d014a#32), -- add x10, x10, x13
  (808, 0xf90008cc#32), -- str x12, [x6, #0x10]
  (812, 0xb4001361#32), -- cbz x1, 0x22984c <.LBB63_45>
  (816, 0x4b0403eb#32), -- neg w11, w4
  (820, 0xaa1f03ec#32), -- mov x12, xzr
  (824, 0x9100202d#32), -- add x13, x1, #0x8
  (828, 0x1200156b#32), -- and w11, w11, #0x3f
  (832, 0x14000012#32), -- b 0x22963c <.LBB63_35>
  (836, 0xf94001b0#32), -- ldr x16, [x13]
  (840, 0x9ac425ef#32), -- lsr x15, x15, x4
  (844, 0x9acb2210#32), -- lsl x16, x16, x11
  (848, 0xd10005d1#32), -- sub x17, x14, #0x1
  (852, 0xeb09023f#32), -- cmp x17, x9
  (856, 0x910021ad#32), -- add x13, x13, #0x8
  (860, 0xaa0f020f#32), -- orr x15, x16, x15
  (864, 0xd10043ff#32), -- sub sp, sp, #0x10
  (868, 0xf90003e9#32), -- str x9, [sp]
  (872, 0xaa0c03e9#32), -- mov x9, x12
  (876, 0xd37df129#32), -- lsl x9, x9, #3
  (880, 0x8b090149#32), -- add x9, x10, x9
  (884, 0xf900012f#32), -- str x15, [x9]
  (888, 0xf94003e9#32), -- ldr x9, [sp]
  (892, 0x910043ff#32), -- add sp, sp, #0x10
  (896, 0xaa0e03ec#32), -- mov x12, x14
  (900, 0x54fff7e0#32), -- b.eq 0x229534 <.LBB63_23>
  (904, 0xeb02019f#32), -- cmp x12, x2
  (908, 0x54000182#32), -- b.hs 0x229670 <.LBB63_37>
  (912, 0xd10043ff#32), -- sub sp, sp, #0x10
  (916, 0xf90003e9#32), -- str x9, [sp]
  (920, 0x910001a9#32), -- add x9, x13, #0x0
  (924, 0xd1002129#32), -- sub x9, x9, #0x8
  (928, 0xf940012f#32), -- ldr x15, [x9]
  (932, 0xf94003e9#32), -- ldr x9, [sp]
  (936, 0x910043ff#32), -- add sp, sp, #0x10
  (940, 0x9100058e#32), -- add x14, x12, #0x1
  (944, 0xeb0201df#32), -- cmp x14, x2
  (948, 0x54fffc83#32), -- b.lo 0x2295f8 <.LBB63_33>
  (952, 0x14000005#32), -- b 0x229680 <.LBB63_38>
  (956, 0xaa1f03ef#32), -- mov x15, xzr
  (960, 0x9100058e#32), -- add x14, x12, #0x1
  (964, 0xeb0201df#32), -- cmp x14, x2
  (968, 0x54fffbe3#32), -- b.lo 0x2295f8 <.LBB63_33>
  (972, 0xaa1f03f0#32), -- mov x16, xzr
  (976, 0x17ffffde#32), -- b 0x2295fc <.LBB63_34>
  (980, 0xaa1f03e1#32), -- mov x1, xzr
  (984, 0xaa1f03e2#32), -- mov x2, xzr
  (988, 0xa9000801#32), -- stp x1, x2, [x0]
  (992, 0xd10043ff#32), -- sub sp, sp, #0x10
  (996, 0xf90003e9#32), -- str x9, [sp]
  (1000, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1004, 0x91000009#32), -- add x9, x0, #0x0
  (1008, 0x91010129#32), -- add x9, x9, #0x40
  (1012, 0x5280000a#32), -- mov w10, #0x0 // =0
  (1016, 0xb900012a#32), -- str w10, [x9]
  (1020, 0xf94007ea#32) -- ldr x10, [sp, #0x8]
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk4 : List (Nat × BitVec 32) := [
  (1024, 0xf94003e9#32), -- ldr x9, [sp]
  (1028, 0x910043ff#32), -- add sp, sp, #0x10
  (1032, 0xd65f03c0#32), -- ret
  (1036, 0x52800028#32), -- mov w8, #0x1 // =1
  (1040, 0x52900009#32), -- mov w9, #0x8000 // =32768
  (1044, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1048, 0xf90003e9#32), -- str x9, [sp]
  (1052, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1056, 0x91000009#32), -- add x9, x0, #0x0
  (1060, 0x9100c129#32), -- add x9, x9, #0x30
  (1064, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1068, 0xf900012a#32), -- str x10, [x9]
  (1072, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1076, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1080, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1084, 0xf94003e9#32), -- ldr x9, [sp]
  (1088, 0x910043ff#32), -- add sp, sp, #0x10
  (1092, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1096, 0xf90003e9#32), -- str x9, [sp]
  (1100, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1104, 0x91000009#32), -- add x9, x0, #0x0
  (1108, 0x91008129#32), -- add x9, x9, #0x20
  (1112, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1116, 0xf900012a#32), -- str x10, [x9]
  (1120, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1124, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1128, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1132, 0xf94003e9#32), -- ldr x9, [sp]
  (1136, 0x910043ff#32), -- add sp, sp, #0x10
  (1140, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1144, 0xf90003e9#32), -- str x9, [sp]
  (1148, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1152, 0x91000009#32), -- add x9, x0, #0x0
  (1156, 0x91004129#32), -- add x9, x9, #0x10
  (1160, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1164, 0xf900012a#32), -- str x10, [x9]
  (1168, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1172, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1176, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1180, 0xf94003e9#32), -- ldr x9, [sp]
  (1184, 0x910043ff#32), -- add sp, sp, #0x10
  (1188, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1192, 0xf90003e9#32), -- str x9, [sp]
  (1196, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1200, 0x91000009#32), -- add x9, x0, #0x0
  (1204, 0xf9000128#32), -- str x8, [x9]
  (1208, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1212, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1216, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1220, 0xf94003e9#32), -- ldr x9, [sp]
  (1224, 0x910043ff#32), -- add sp, sp, #0x10
  (1228, 0xb9004009#32), -- str w9, [x0, #0x40]
  (1232, 0xd65f03c0#32), -- ret
  (1236, 0x9ac42448#32), -- lsr x8, x2, x4
  (1240, 0x4b0403eb#32), -- neg w11, w4
  (1244, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1248, 0xf90003e9#32), -- str x9, [sp]
  (1252, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1256, 0x91000009#32), -- add x9, x0, #0x0
  (1260, 0x91010129#32), -- add x9, x9, #0x40
  (1264, 0x5280000a#32), -- mov w10, #0x0 // =0
  (1268, 0xb900012a#32), -- str w10, [x9]
  (1272, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1276, 0xf94003e9#32) -- ldr x9, [sp]
]

theorem chunk4_decodes :
    chunk4.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk5 : List (Nat × BitVec 32) := [
  (1280, 0x910043ff#32), -- add sp, sp, #0x10
  (1284, 0x9acb23ea#32), -- lsl x10, xzr, x11
  (1288, 0xaa080148#32), -- orr x8, x10, x8
  (1292, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1296, 0xf90003e9#32), -- str x9, [sp]
  (1300, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1304, 0x91000009#32), -- add x9, x0, #0x0
  (1308, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1312, 0xf900012a#32), -- str x10, [x9]
  (1316, 0xf9000528#32), -- str x8, [x9, #0x8]
  (1320, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1324, 0xf94003e9#32), -- ldr x9, [sp]
  (1328, 0x910043ff#32), -- add sp, sp, #0x10
  (1332, 0xd65f03c0#32), -- ret
  (1336, 0x4b0403eb#32), -- neg w11, w4
  (1340, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1344, 0xf90003e9#32), -- str x9, [sp]
  (1348, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1352, 0x91000009#32), -- add x9, x0, #0x0
  (1356, 0x91010129#32), -- add x9, x9, #0x40
  (1360, 0x5280000a#32), -- mov w10, #0x0 // =0
  (1364, 0xb900012a#32), -- str w10, [x9]
  (1368, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1372, 0xf94003e9#32), -- ldr x9, [sp]
  (1376, 0x910043ff#32), -- add sp, sp, #0x10
  (1380, 0x9acb23ea#32), -- lsl x10, xzr, x11
  (1384, 0xaa1f0148#32), -- orr x8, x10, xzr
  (1388, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1392, 0xf90003e9#32), -- str x9, [sp]
  (1396, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1400, 0x91000009#32), -- add x9, x0, #0x0
  (1404, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1408, 0xf900012a#32), -- str x10, [x9]
  (1412, 0xf9000528#32), -- str x8, [x9, #0x8]
  (1416, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1420, 0xf94003e9#32), -- ldr x9, [sp]
  (1424, 0x910043ff#32), -- add sp, sp, #0x10
  (1428, 0xd65f03c0#32), -- ret
  (1432, 0x9ac4244c#32), -- lsr x12, x2, x4
  (1436, 0xf900014c#32), -- str x12, [x10]
  (1440, 0xb4ffe709#32), -- cbz x9, 0x229534 <.LBB63_23>
  (1444, 0x9100216b#32), -- add x11, x11, #0x8
  (1448, 0xf1000529#32), -- subs x9, x9, #0x1
  (1452, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1456, 0xf90003e9#32), -- str x9, [sp]
  (1460, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1464, 0x91000169#32), -- add x9, x11, #0x0
  (1468, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1472, 0xf900012a#32), -- str x10, [x9]
  (1476, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1480, 0xf94003e9#32), -- ldr x9, [sp]
  (1484, 0x910043ff#32), -- add sp, sp, #0x10
  (1488, 0x9100216b#32), -- add x11, x11, #0x8
  (1492, 0x54fffea1#32), -- b.ne 0x22985c <.LBB63_47>
  (1496, 0x17ffff2a#32) -- b 0x229534 <.LBB63_23>
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

end SszArm.Indices.Linked.NatShr
