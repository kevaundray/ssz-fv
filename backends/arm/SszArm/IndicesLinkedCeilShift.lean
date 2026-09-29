import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.CeilShift

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN13ssz_fv_native7indices10ceil_shift17hfe7605b69b9bc83bE. -/
def address : Nat := 2263988

def byteSize : Nat := 1792

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xaa0403e6#32), -- mov x6, x4
  (4, 0xb4000121#32), -- cbz x1, 0x228bdc <.LBB62_3>
  (8, 0xb4000242#32), -- cbz x2, 0x228c04 <.LBB62_6>
  (12, 0xf9400029#32), -- ldr x9, [x1]
  (16, 0xaa0203e8#32), -- mov x8, x2
  (20, 0x9280000a#32), -- mov x10, #-0x1 // =-1
  (24, 0x9ac3214a#32), -- lsl x10, x10, x3
  (28, 0xea2a013f#32), -- bics xzr, x9, x10
  (32, 0x54000221#32), -- b.ne 0x228c18 <.LBB62_7>
  (36, 0x14000039#32), -- b 0x228cbc <.LBB62_12>
  (40, 0x92800008#32), -- mov x8, #-0x1 // =-1
  (44, 0x9ac32108#32), -- lsl x8, x8, x3
  (48, 0xea28005f#32), -- bics xzr, x2, x8
  (52, 0x540006a0#32), -- b.eq 0x228cbc <.LBB62_12>
  (56, 0x2a0303e9#32), -- mov w9, w3
  (60, 0xb4000702#32), -- cbz x2, 0x228cd0 <.LBB62_14>
  (64, 0xaa1f03ea#32), -- mov x10, xzr
  (68, 0xaa1f03eb#32), -- mov x11, xzr
  (72, 0xaa0203e8#32), -- mov x8, x2
  (76, 0x1400001a#32), -- b 0x228c68 <.LBB62_11>
  (80, 0xaa1f03e8#32), -- mov x8, xzr
  (84, 0x9280000a#32), -- mov x10, #-0x1 // =-1
  (88, 0x9ac3214a#32), -- lsl x10, x10, x3
  (92, 0xea2a03ff#32), -- bics xzr, xzr, x10
  (96, 0x54000540#32), -- b.eq 0x228cbc <.LBB62_12>
  (100, 0x2a0303e9#32), -- mov w9, w3
  (104, 0xd100202a#32), -- sub x10, x1, #0x8
  (108, 0xaa0803ec#32), -- mov x12, x8
  (112, 0xaa0c03eb#32), -- mov x11, x12
  (116, 0xb400050c#32), -- cbz x12, 0x228cc8 <.LBB62_13>
  (120, 0xd10043ff#32), -- sub sp, sp, #0x10
  (124, 0xf90003e9#32), -- str x9, [sp]
  (128, 0xaa0b03e9#32), -- mov x9, x11
  (132, 0xd37df129#32), -- lsl x9, x9, #3
  (136, 0x8b090149#32), -- add x9, x10, x9
  (140, 0xf9400122#32), -- ldr x2, [x9]
  (144, 0xf94003e9#32), -- ldr x9, [sp]
  (148, 0x910043ff#32), -- add sp, sp, #0x10
  (152, 0xd100056c#32), -- sub x12, x11, #0x1
  (156, 0xb4fffea2#32), -- cbz x2, 0x228c24 <.LBB62_8>
  (160, 0xd37ae56a#32), -- lsl x10, x11, #6
  (164, 0xd37afd6b#32), -- lsr x11, x11, #58
  (168, 0x9280000c#32), -- mov x12, #-0x1 // =-1
  (172, 0xf101014a#32), -- subs x10, x10, #0x40
  (176, 0x9a0c016b#32), -- adc x11, x11, x12
  (180, 0xd10043ff#32), -- sub sp, sp, #0x10
  (184, 0xf90003e9#32), -- str x9, [sp]
  (188, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (192, 0xaa0203e9#32), -- mov x9, x2
  (196, 0xd280080a#32), -- mov x10, #0x40 // =64
  (200, 0xb4000089#32), -- cbz x9, 0x228c8c <.Llower_arm_520>
  (204, 0xd100054a#32), -- sub x10, x10, #0x1
  (208, 0xd341fd29#32), -- lsr x9, x9, #1
  (212, 0xb5ffffc9#32), -- cbnz x9, 0x228c80 <.Llower_arm_519>
  (216, 0xaa0a03ec#32), -- mov x12, x10
  (220, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (224, 0xf94003e9#32), -- ldr x9, [sp]
  (228, 0x910043ff#32), -- add sp, sp, #0x10
  (232, 0x5280080d#32), -- mov w13, #0x40 // =64
  (236, 0x4b0c01ac#32), -- sub w12, w13, w12
  (240, 0xab0c014a#32), -- adds x10, x10, x12
  (244, 0x54000062#32), -- b.hs 0x228cb4 <.Llower_arm_521>
  (248, 0xaa0b03eb#32), -- mov x11, x11
  (252, 0x14000002#32) -- b 0x228cb8 <.Llower_arm_522>
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0x9100056b#32), -- add x11, x11, #0x1
  (260, 0x14000009#32), -- b 0x228cdc <.LBB62_15>
  (264, 0x2a0303e4#32), -- mov w4, w3
  (268, 0xaa1f03e5#32), -- mov x5, xzr
  (272, 0x1400017c#32), -- b 0x2292b4 <_ZN13ssz_fv_native3nat3Nat3shr17he988a53a952ee485E>
  (276, 0xaa1f03ea#32), -- mov x10, xzr
  (280, 0x14000004#32), -- b 0x228cdc <.LBB62_15>
  (284, 0xaa1f03e8#32), -- mov x8, xzr
  (288, 0xaa1f03ea#32), -- mov x10, xzr
  (292, 0xaa1f03eb#32), -- mov x11, xzr
  (296, 0xd10043ff#32), -- sub sp, sp, #0x10
  (300, 0xf90003e9#32), -- str x9, [sp]
  (304, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (308, 0xd3407c69#32), -- ubfx x9, x3, #0, #32
  (312, 0xeb09014a#32), -- subs x10, x10, x9
  (316, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (320, 0xf94003e9#32), -- ldr x9, [sp]
  (324, 0x910043ff#32), -- add sp, sp, #0x10
  (328, 0xfa1f016b#32), -- sbcs x11, x11, xzr
  (332, 0x9a8a33ea#32), -- csel x10, xzr, x10, lo
  (336, 0x9a8b33eb#32), -- csel x11, xzr, x11, lo
  (340, 0xb100fd4a#32), -- adds x10, x10, #0x3f
  (344, 0x54000062#32), -- b.hs 0x228d18 <.Llower_arm_523>
  (348, 0xaa0b03eb#32), -- mov x11, x11
  (352, 0x14000002#32), -- b 0x228d1c <.Llower_arm_524>
  (356, 0x9100056b#32), -- add x11, x11, #0x1
  (360, 0xd10043ff#32), -- sub sp, sp, #0x10
  (364, 0xf90003e9#32), -- str x9, [sp]
  (368, 0xd346fd49#32), -- lsr x9, x10, #6
  (372, 0xaa0be92a#32), -- orr x10, x9, x11, lsl #58
  (376, 0xf94003e9#32), -- ldr x9, [sp]
  (380, 0x910043ff#32), -- add sp, sp, #0x10
  (384, 0xb40004ea#32), -- cbz x10, 0x228dd0 <.LBB62_26>
  (388, 0x4b0303eb#32), -- neg w11, w3
  (392, 0x1200156b#32), -- and w11, w11, #0x3f
  (396, 0xb4000741#32), -- cbz x1, 0x228e28 <.LBB62_27>
  (400, 0x340007c3#32), -- cbz w3, 0x228e3c <.LBB62_29>
  (404, 0x9100202c#32), -- add x12, x1, #0x8
  (408, 0xcb0a03ed#32), -- neg x13, x10
  (412, 0x5280002e#32), -- mov w14, #0x1 // =1
  (416, 0x14000008#32), -- b 0x228d74 <.LBB62_20>
  (420, 0x9ac925ef#32), -- lsr x15, x15, x9
  (424, 0x9acb2210#32), -- lsl x16, x16, x11
  (428, 0x910005ce#32), -- add x14, x14, #0x1
  (432, 0x9100218c#32), -- add x12, x12, #0x8
  (436, 0xaa0f020f#32), -- orr x15, x16, x15
  (440, 0xb10005ff#32), -- cmn x15, #0x1
  (444, 0x54000ee1#32), -- b.ne 0x228f4c <.LBB62_38>
  (448, 0x8b0e01af#32), -- add x15, x13, x14
  (452, 0xf10005ff#32), -- cmp x15, #0x1
  (456, 0x54000760#32), -- b.eq 0x228e68 <.LBB62_33>
  (460, 0xd10005cf#32), -- sub x15, x14, #0x1
  (464, 0xeb0801ff#32), -- cmp x15, x8
  (468, 0x54000162#32), -- b.hs 0x228db4 <.LBB62_23>
  (472, 0xd10043ff#32), -- sub sp, sp, #0x10
  (476, 0xf90003e9#32), -- str x9, [sp]
  (480, 0x91000189#32), -- add x9, x12, #0x0
  (484, 0xd1002129#32), -- sub x9, x9, #0x8
  (488, 0xf940012f#32), -- ldr x15, [x9]
  (492, 0xf94003e9#32), -- ldr x9, [sp]
  (496, 0x910043ff#32), -- add sp, sp, #0x10
  (500, 0xaa1f03f0#32), -- mov x16, xzr
  (504, 0xb50000ae#32), -- cbnz x14, 0x228dc0 <.LBB62_24>
  (508, 0x17ffffea#32) -- b 0x228d58 <.LBB62_19>
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xaa1f03ef#32), -- mov x15, xzr
  (516, 0xaa1f03f0#32), -- mov x16, xzr
  (520, 0xb4fffcee#32), -- cbz x14, 0x228d58 <.LBB62_19>
  (524, 0xeb0801df#32), -- cmp x14, x8
  (528, 0x54fffca2#32), -- b.hs 0x228d58 <.LBB62_19>
  (532, 0xf9400190#32), -- ldr x16, [x12]
  (536, 0x17ffffe3#32), -- b 0x228d58 <.LBB62_19>
  (540, 0x52800028#32), -- mov w8, #0x1 // =1
  (544, 0xd10043ff#32), -- sub sp, sp, #0x10
  (548, 0xf90003e9#32), -- str x9, [sp]
  (552, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (556, 0x91000009#32), -- add x9, x0, #0x0
  (560, 0xd280000a#32), -- mov x10, #0x0 // =0
  (564, 0xf900012a#32), -- str x10, [x9]
  (568, 0xf9000528#32), -- str x8, [x9, #0x8]
  (572, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (576, 0xf94003e9#32), -- ldr x9, [sp]
  (580, 0x910043ff#32), -- add sp, sp, #0x10
  (584, 0xd10043ff#32), -- sub sp, sp, #0x10
  (588, 0xf90003e9#32), -- str x9, [sp]
  (592, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (596, 0x91000009#32), -- add x9, x0, #0x0
  (600, 0x91010129#32), -- add x9, x9, #0x40
  (604, 0x5280000a#32), -- mov w10, #0x0 // =0
  (608, 0xb900012a#32), -- str w10, [x9]
  (612, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (616, 0xf94003e9#32), -- ldr x9, [sp]
  (620, 0x910043ff#32), -- add sp, sp, #0x10
  (624, 0xd65f03c0#32), -- ret
  (628, 0x34000883#32), -- cbz w3, 0x228f38 <.LBB62_35>
  (632, 0x9ac9250c#32), -- lsr x12, x8, x9
  (636, 0xb100059f#32), -- cmn x12, #0x1
  (640, 0x54000860#32), -- b.eq 0x228f40 <.LBB62_36>
  (644, 0x14000045#32), -- b 0x228f4c <.LBB62_38>
  (648, 0xaa0a03ec#32), -- mov x12, x10
  (652, 0xaa0803ed#32), -- mov x13, x8
  (656, 0xaa0103ee#32), -- mov x14, x1
  (660, 0xb400010c#32), -- cbz x12, 0x228e68 <.LBB62_33>
  (664, 0xb400080d#32), -- cbz x13, 0x228f4c <.LBB62_38>
  (668, 0xf84085cf#32), -- ldr x15, [x14], #0x8
  (672, 0xd10005ad#32), -- sub x13, x13, #0x1
  (676, 0xd100058c#32), -- sub x12, x12, #0x1
  (680, 0xb10005ff#32), -- cmn x15, #0x1
  (684, 0x54ffff40#32), -- b.eq 0x228e48 <.LBB62_30>
  (688, 0x1400003a#32), -- b 0x228f4c <.LBB62_38>
  (692, 0xb100055f#32), -- cmn x10, #0x1
  (696, 0x540006e1#32), -- b.ne 0x228f48 <.LBB62_37>
  (700, 0x52800028#32), -- mov w8, #0x1 // =1
  (704, 0xd10043ff#32), -- sub sp, sp, #0x10
  (708, 0xf90003e9#32), -- str x9, [sp]
  (712, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (716, 0x91000009#32), -- add x9, x0, #0x0
  (720, 0x91004129#32), -- add x9, x9, #0x10
  (724, 0xd280000a#32), -- mov x10, #0x0 // =0
  (728, 0xf900012a#32), -- str x10, [x9]
  (732, 0xd280000a#32), -- mov x10, #0x0 // =0
  (736, 0xf900052a#32), -- str x10, [x9, #0x8]
  (740, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (744, 0xf94003e9#32), -- ldr x9, [sp]
  (748, 0x910043ff#32), -- add sp, sp, #0x10
  (752, 0xd10043ff#32), -- sub sp, sp, #0x10
  (756, 0xf90003e9#32), -- str x9, [sp]
  (760, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (764, 0x91000009#32) -- add x9, x0, #0x0
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0xf9000128#32), -- str x8, [x9]
  (772, 0xd280000a#32), -- mov x10, #0x0 // =0
  (776, 0xf900052a#32), -- str x10, [x9, #0x8]
  (780, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (784, 0xf94003e9#32), -- ldr x9, [sp]
  (788, 0x910043ff#32), -- add sp, sp, #0x10
  (792, 0xd10043ff#32), -- sub sp, sp, #0x10
  (796, 0xf90003e9#32), -- str x9, [sp]
  (800, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (804, 0x91000009#32), -- add x9, x0, #0x0
  (808, 0x91008129#32), -- add x9, x9, #0x20
  (812, 0xd280000a#32), -- mov x10, #0x0 // =0
  (816, 0xf900012a#32), -- str x10, [x9]
  (820, 0xd280000a#32), -- mov x10, #0x0 // =0
  (824, 0xf900052a#32), -- str x10, [x9, #0x8]
  (828, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (832, 0xf94003e9#32), -- ldr x9, [sp]
  (836, 0x910043ff#32), -- add sp, sp, #0x10
  (840, 0xd10043ff#32), -- sub sp, sp, #0x10
  (844, 0xf90003e9#32), -- str x9, [sp]
  (848, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (852, 0x91000009#32), -- add x9, x0, #0x0
  (856, 0x9100c129#32), -- add x9, x9, #0x30
  (860, 0xd280000a#32), -- mov x10, #0x0 // =0
  (864, 0xf900012a#32), -- str x10, [x9]
  (868, 0xd280000a#32), -- mov x10, #0x0 // =0
  (872, 0xf900052a#32), -- str x10, [x9, #0x8]
  (876, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (880, 0xf94003e9#32), -- ldr x9, [sp]
  (884, 0x910043ff#32), -- add sp, sp, #0x10
  (888, 0x52900008#32), -- mov w8, #0x8000 // =32768
  (892, 0xb9004008#32), -- str w8, [x0, #0x40]
  (896, 0xd65f03c0#32), -- ret
  (900, 0xb100051f#32), -- cmn x8, #0x1
  (904, 0x54000081#32), -- b.ne 0x228f4c <.LBB62_38>
  (908, 0xf100055f#32), -- cmp x10, #0x1
  (912, 0x54000041#32), -- b.ne 0x228f4c <.LBB62_38>
  (916, 0x9100054a#32), -- add x10, x10, #0x1
  (920, 0xf100054d#32), -- subs x13, x10, #0x1
  (924, 0x54000141#32), -- b.ne 0x228f78 <.LBB62_44>
  (928, 0xb40010e1#32), -- cbz x1, 0x229170 <.LBB62_62>
  (932, 0xb4001148#32), -- cbz x8, 0x229180 <.LBB62_64>
  (936, 0xf940002a#32), -- ldr x10, [x1]
  (940, 0x9ac92549#32), -- lsr x9, x10, x9
  (944, 0x34001163#32), -- cbz w3, 0x229190 <.LBB62_66>
  (948, 0xf100051f#32), -- cmp x8, #0x1
  (952, 0x54001060#32), -- b.eq 0x229178 <.LBB62_63>
  (956, 0xf9400428#32), -- ldr x8, [x1, #0x8]
  (960, 0x14000085#32), -- b 0x229188 <.LBB62_65>
  (964, 0xd37dfd4c#32), -- lsr x12, x10, #61
  (968, 0xb500096c#32), -- cbnz x12, 0x2290a8 <.LBB62_61>
  (972, 0xd37df14f#32), -- lsl x15, x10, #3
  (976, 0xd10043ff#32), -- sub sp, sp, #0x10
  (980, 0xf90003e9#32), -- str x9, [sp]
  (984, 0x924101e9#32), -- and x9, x15, #0x8000000000000000
  (988, 0xb5000089#32), -- cbnz x9, 0x228fa0 <.Llower_arm_525>
  (992, 0xf94003e9#32), -- ldr x9, [sp]
  (996, 0x910043ff#32), -- add sp, sp, #0x10
  (1000, 0x14000004#32), -- b 0x228fac <.Llower_arm_526>
  (1004, 0xf94003e9#32), -- ldr x9, [sp]
  (1008, 0x910043ff#32), -- add sp, sp, #0x10
  (1012, 0x14000040#32), -- b 0x2290a8 <.LBB62_61>
  (1016, 0xf94000cc#32), -- ldr x12, [x6]
  (1020, 0xf94008d0#32) -- ldr x16, [x6, #0x10]
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk4 : List (Nat × BitVec 32) := [
  (1024, 0xab0c0211#32), -- adds x17, x16, x12
  (1028, 0x54000782#32), -- b.hs 0x2290a8 <.LBB62_61>
  (1032, 0xb100223f#32), -- cmn x17, #0x8
  (1036, 0x54000748#32), -- b.hi 0x2290a8 <.LBB62_61>
  (1040, 0x91001e2e#32), -- add x14, x17, #0x7
  (1044, 0x927df1ce#32), -- and x14, x14, #0xfffffffffffffff8
  (1048, 0xcb1101d1#32), -- sub x17, x14, x17
  (1052, 0xab100230#32), -- adds x16, x17, x16
  (1056, 0x540006a2#32), -- b.hs 0x2290a8 <.LBB62_61>
  (1060, 0xab0f020f#32), -- adds x15, x16, x15
  (1064, 0x54000662#32), -- b.hs 0x2290a8 <.LBB62_61>
  (1068, 0xf94004d1#32), -- ldr x17, [x6, #0x8]
  (1072, 0xeb1101ff#32), -- cmp x15, x17
  (1076, 0x54000608#32), -- b.hi 0x2290a8 <.LBB62_61>
  (1080, 0x8b10018c#32), -- add x12, x12, x16
  (1084, 0xf90008cf#32), -- str x15, [x6, #0x10]
  (1088, 0xb4000fa1#32), -- cbz x1, 0x2291e8 <.LBB62_67>
  (1092, 0xaa1f03ed#32), -- mov x13, xzr
  (1096, 0x5280002e#32), -- mov w14, #0x1 // =1
  (1100, 0x14000014#32), -- b 0x229050 <.LBB62_56>
  (1104, 0xaa1f03f1#32), -- mov x17, xzr
  (1108, 0x9acb2231#32), -- lsl x17, x17, x11
  (1112, 0xaa110210#32), -- orr x16, x16, x17
  (1116, 0xab0e0210#32), -- adds x16, x16, x14
  (1120, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1124, 0xf90003e9#32), -- str x9, [sp]
  (1128, 0xaa0d03e9#32), -- mov x9, x13
  (1132, 0xd37df129#32), -- lsl x9, x9, #3
  (1136, 0x8b090189#32), -- add x9, x12, x9
  (1140, 0xf9000130#32), -- str x16, [x9]
  (1144, 0xf94003e9#32), -- ldr x9, [sp]
  (1148, 0x910043ff#32), -- add sp, sp, #0x10
  (1152, 0xaa0f03ed#32), -- mov x13, x15
  (1156, 0x54000062#32), -- b.hs 0x229044 <.Llower_arm_527>
  (1160, 0x5280000e#32), -- mov w14, #0x0 // =0
  (1164, 0x14000002#32), -- b 0x229048 <.Llower_arm_528>
  (1168, 0x5280002e#32), -- mov w14, #0x1 // =1
  (1172, 0xeb0f015f#32), -- cmp x10, x15
  (1176, 0x540011c0#32), -- b.eq 0x229284 <.LBB62_73>
  (1180, 0xeb0801bf#32), -- cmp x13, x8
  (1184, 0x540001a2#32), -- b.hs 0x229088 <.LBB62_58>
  (1188, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1192, 0xf90003e9#32), -- str x9, [sp]
  (1196, 0xaa0d03e9#32), -- mov x9, x13
  (1200, 0xd37df129#32), -- lsl x9, x9, #3
  (1204, 0x8b090029#32), -- add x9, x1, x9
  (1208, 0xf940012f#32), -- ldr x15, [x9]
  (1212, 0xf94003e9#32), -- ldr x9, [sp]
  (1216, 0x910043ff#32), -- add sp, sp, #0x10
  (1220, 0x9ac925f0#32), -- lsr x16, x15, x9
  (1224, 0x910005af#32), -- add x15, x13, #0x1
  (1228, 0x350000a3#32), -- cbnz w3, 0x229094 <.LBB62_59>
  (1232, 0x17ffffe3#32), -- b 0x229010 <.LBB62_55>
  (1236, 0x9ac927f0#32), -- lsr x16, xzr, x9
  (1240, 0x910005af#32), -- add x15, x13, #0x1
  (1244, 0x34fffc03#32), -- cbz w3, 0x229010 <.LBB62_55>
  (1248, 0xeb0801ff#32), -- cmp x15, x8
  (1252, 0x54fffb62#32), -- b.hs 0x229004 <.LBB62_53>
  (1256, 0x8b0d0c31#32), -- add x17, x1, x13, lsl #3
  (1260, 0xf9400631#32), -- ldr x17, [x17, #0x8]
  (1264, 0x17ffffd9#32), -- b 0x229008 <.LBB62_54>
  (1268, 0x52800028#32), -- mov w8, #0x1 // =1
  (1272, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1276, 0xf90003e9#32) -- str x9, [sp]
]

theorem chunk4_decodes :
    chunk4.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk5 : List (Nat × BitVec 32) := [
  (1280, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1284, 0x91000009#32), -- add x9, x0, #0x0
  (1288, 0x9100c129#32), -- add x9, x9, #0x30
  (1292, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1296, 0xf900012a#32), -- str x10, [x9]
  (1300, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1304, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1308, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1312, 0xf94003e9#32), -- ldr x9, [sp]
  (1316, 0x910043ff#32), -- add sp, sp, #0x10
  (1320, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1324, 0xf90003e9#32), -- str x9, [sp]
  (1328, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1332, 0x91000009#32), -- add x9, x0, #0x0
  (1336, 0x91008129#32), -- add x9, x9, #0x20
  (1340, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1344, 0xf900012a#32), -- str x10, [x9]
  (1348, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1352, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1356, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1360, 0xf94003e9#32), -- ldr x9, [sp]
  (1364, 0x910043ff#32), -- add sp, sp, #0x10
  (1368, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1372, 0xf90003e9#32), -- str x9, [sp]
  (1376, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1380, 0x91000009#32), -- add x9, x0, #0x0
  (1384, 0x91004129#32), -- add x9, x9, #0x10
  (1388, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1392, 0xf900012a#32), -- str x10, [x9]
  (1396, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1400, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1404, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1408, 0xf94003e9#32), -- ldr x9, [sp]
  (1412, 0x910043ff#32), -- add sp, sp, #0x10
  (1416, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1420, 0xf90003e9#32), -- str x9, [sp]
  (1424, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1428, 0x91000009#32), -- add x9, x0, #0x0
  (1432, 0xf9000128#32), -- str x8, [x9]
  (1436, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1440, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1444, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1448, 0xf94003e9#32), -- ldr x9, [sp]
  (1452, 0x910043ff#32), -- add sp, sp, #0x10
  (1456, 0x52900008#32), -- mov w8, #0x8000 // =32768
  (1460, 0xb9004008#32), -- str w8, [x0, #0x40]
  (1464, 0xd65f03c0#32), -- ret
  (1468, 0x9ac92509#32), -- lsr x9, x8, x9
  (1472, 0x340000e3#32), -- cbz w3, 0x229190 <.LBB62_66>
  (1476, 0xaa1f03e8#32), -- mov x8, xzr
  (1480, 0x14000003#32), -- b 0x229188 <.LBB62_65>
  (1484, 0xaa1f03e9#32), -- mov x9, xzr
  (1488, 0x34000063#32), -- cbz w3, 0x229190 <.LBB62_66>
  (1492, 0x9acb2108#32), -- lsl x8, x8, x11
  (1496, 0xaa080129#32), -- orr x9, x9, x8
  (1500, 0x91000528#32), -- add x8, x9, #0x1
  (1504, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1508, 0xf90003e9#32), -- str x9, [sp]
  (1512, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1516, 0x91000009#32), -- add x9, x0, #0x0
  (1520, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1524, 0xf900012a#32), -- str x10, [x9]
  (1528, 0xf9000528#32), -- str x8, [x9, #0x8]
  (1532, 0xf94007ea#32) -- ldr x10, [sp, #0x8]
]

theorem chunk5_decodes :
    chunk5.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk6 : List (Nat × BitVec 32) := [
  (1536, 0xf94003e9#32), -- ldr x9, [sp]
  (1540, 0x910043ff#32), -- add sp, sp, #0x10
  (1544, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1548, 0xf90003e9#32), -- str x9, [sp]
  (1552, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1556, 0x91000009#32), -- add x9, x0, #0x0
  (1560, 0x91010129#32), -- add x9, x9, #0x40
  (1564, 0x5280000a#32), -- mov w10, #0x0 // =0
  (1568, 0xb900012a#32), -- str w10, [x9]
  (1572, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1576, 0xf94003e9#32), -- ldr x9, [sp]
  (1580, 0x910043ff#32), -- add sp, sp, #0x10
  (1584, 0xd65f03c0#32), -- ret
  (1588, 0x34000243#32), -- cbz w3, 0x229230 <.LBB62_70>
  (1592, 0x9ac92508#32), -- lsr x8, x8, x9
  (1596, 0x91000508#32), -- add x8, x8, #0x1
  (1600, 0xf9000188#32), -- str x8, [x12]
  (1604, 0x910021c8#32), -- add x8, x14, #0x8
  (1608, 0xf10005ad#32), -- subs x13, x13, #0x1
  (1612, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1616, 0xf90003e9#32), -- str x9, [sp]
  (1620, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1624, 0x91000109#32), -- add x9, x8, #0x0
  (1628, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1632, 0xf900012a#32), -- str x10, [x9]
  (1636, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1640, 0xf94003e9#32), -- ldr x9, [sp]
  (1644, 0x910043ff#32), -- add sp, sp, #0x10
  (1648, 0x91002108#32), -- add x8, x8, #0x8
  (1652, 0x54fffea1#32), -- b.ne 0x2291fc <.LBB62_69>
  (1656, 0x14000016#32), -- b 0x229284 <.LBB62_73>
  (1660, 0xb1000509#32), -- adds x9, x8, #0x1
  (1664, 0x54000062#32), -- b.hs 0x229240 <.Llower_arm_529>
  (1668, 0x5280000b#32), -- mov w11, #0x0 // =0
  (1672, 0x14000002#32), -- b 0x229244 <.Llower_arm_530>
  (1676, 0x5280002b#32), -- mov w11, #0x1 // =1
  (1680, 0xf1000948#32), -- subs x8, x10, #0x2
  (1684, 0xa9002d89#32), -- stp x9, x11, [x12]
  (1688, 0x540001c0#32), -- b.eq 0x229284 <.LBB62_73>
  (1692, 0x910041c9#32), -- add x9, x14, #0x10
  (1696, 0xf1000508#32), -- subs x8, x8, #0x1
  (1700, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1704, 0xf90003ea#32), -- str x10, [sp]
  (1708, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (1712, 0x9100012a#32), -- add x10, x9, #0x0
  (1716, 0xd280000b#32), -- mov x11, #0x0 // =0
  (1720, 0xf900014b#32), -- str x11, [x10]
  (1724, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (1728, 0xf94003ea#32), -- ldr x10, [sp]
  (1732, 0x910043ff#32), -- add sp, sp, #0x10
  (1736, 0x91002129#32), -- add x9, x9, #0x8
  (1740, 0x54fffea1#32), -- b.ne 0x229254 <.LBB62_72>
  (1744, 0xa900280c#32), -- stp x12, x10, [x0]
  (1748, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1752, 0xf90003e9#32), -- str x9, [sp]
  (1756, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1760, 0x91000009#32), -- add x9, x0, #0x0
  (1764, 0x91010129#32), -- add x9, x9, #0x40
  (1768, 0x5280000a#32), -- mov w10, #0x0 // =0
  (1772, 0xb900012a#32), -- str w10, [x9]
  (1776, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1780, 0xf94003e9#32), -- ldr x9, [sp]
  (1784, 0x910043ff#32), -- add sp, sp, #0x10
  (1788, 0xd65f03c0#32) -- ret
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

end SszArm.Indices.Linked.CeilShift
