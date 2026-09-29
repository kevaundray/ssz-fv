import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.Emit

/-- Actual ELF entry address of _ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE. -/
def address : Nat := 2294780

def byteSize : Nat := 1996

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10283ff#32), -- sub sp, sp, #0xa0
  (4, 0xa9056ffe#32), -- stp x30, x27, [sp, #0x50]
  (8, 0xa90667fa#32), -- stp x26, x25, [sp, #0x60]
  (12, 0xa9075ff8#32), -- stp x24, x23, [sp, #0x70]
  (16, 0xa90857f6#32), -- stp x22, x21, [sp, #0x80]
  (20, 0xa9094ff4#32), -- stp x20, x19, [sp, #0x90]
  (24, 0xf9400028#32), -- ldr x8, [x1]
  (28, 0x39400049#32), -- ldrb w9, [x2]
  (32, 0xaa0503f5#32), -- mov x21, x5
  (36, 0xaa0403f4#32), -- mov x20, x4
  (40, 0xaa0203f6#32), -- mov x22, x2
  (44, 0xaa0003f3#32), -- mov x19, x0
  (48, 0xb4000948#32), -- cbz x8, 0x230554 <.LBB84_9>
  (52, 0xf100051f#32), -- cmp x8, #0x1
  (56, 0x54000f41#32), -- b.ne 0x23061c <.LBB84_11>
  (60, 0x7100053f#32), -- cmp w9, #0x1
  (64, 0x540008e1#32), -- b.ne 0x230558 <.LBB84_10>
  (68, 0xa9408428#32), -- ldp x8, x1, [x1, #0x8]
  (72, 0xb4001a08#32), -- cbz x8, 0x230784 <.LBB84_40>
  (76, 0xd100042a#32), -- sub x10, x1, #0x1
  (80, 0xb100055f#32), -- cmn x10, #0x1
  (84, 0x54001960#32), -- b.eq 0x23077c <.LBB84_38>
  (88, 0xd10043ff#32), -- sub sp, sp, #0x10
  (92, 0xf90003e9#32), -- str x9, [sp]
  (96, 0xaa0a03e9#32), -- mov x9, x10
  (100, 0xd37df129#32), -- lsl x9, x9, #3
  (104, 0x8b090109#32), -- add x9, x8, x9
  (108, 0xf940012b#32), -- ldr x11, [x9]
  (112, 0xf94003e9#32), -- ldr x9, [sp]
  (116, 0x910043ff#32), -- add sp, sp, #0x10
  (120, 0xaa0a03e9#32), -- mov x9, x10
  (124, 0xd100054a#32), -- sub x10, x10, #0x1
  (128, 0xb4fffe8b#32), -- cbz x11, 0x23044c <.LBB84_5>
  (132, 0x91000529#32), -- add x9, x9, #0x1
  (136, 0xf100053f#32), -- cmp x9, #0x1
  (140, 0x540017c0#32), -- b.eq 0x230780 <.LBB84_39>
  (144, 0x52800028#32), -- mov w8, #0x1                // =1
  (148, 0xd10043ff#32), -- sub sp, sp, #0x10
  (152, 0xf90003e9#32), -- str x9, [sp]
  (156, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (160, 0x91000269#32), -- add x9, x19, #0x0
  (164, 0x9100c129#32), -- add x9, x9, #0x30
  (168, 0xd280000a#32), -- mov x10, #0x0               // =0
  (172, 0xf900012a#32), -- str x10, [x9]
  (176, 0xd280000a#32), -- mov x10, #0x0               // =0
  (180, 0xf900052a#32), -- str x10, [x9, #0x8]
  (184, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (188, 0xf94003e9#32), -- ldr x9, [sp]
  (192, 0x910043ff#32), -- add sp, sp, #0x10
  (196, 0xd10043ff#32), -- sub sp, sp, #0x10
  (200, 0xf90003e9#32), -- str x9, [sp]
  (204, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (208, 0x91000269#32), -- add x9, x19, #0x0
  (212, 0xf9000128#32), -- str x8, [x9]
  (216, 0xd280000a#32), -- mov x10, #0x0               // =0
  (220, 0xf900052a#32), -- str x10, [x9, #0x8]
  (224, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (228, 0xf94003e9#32), -- ldr x9, [sp]
  (232, 0x910043ff#32), -- add sp, sp, #0x10
  (236, 0x52900028#32), -- mov w8, #0x8001             // =32769
  (240, 0xd10043ff#32), -- sub sp, sp, #0x10
  (244, 0xf90003e9#32), -- str x9, [sp]
  (248, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (252, 0x91000269#32) -- add x9, x19, #0x0
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0x91008129#32), -- add x9, x9, #0x20
  (260, 0xd280000a#32), -- mov x10, #0x0               // =0
  (264, 0xf900012a#32), -- str x10, [x9]
  (268, 0xd280000a#32), -- mov x10, #0x0               // =0
  (272, 0xf900052a#32), -- str x10, [x9, #0x8]
  (276, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (280, 0xf94003e9#32), -- ldr x9, [sp]
  (284, 0x910043ff#32), -- add sp, sp, #0x10
  (288, 0xd10043ff#32), -- sub sp, sp, #0x10
  (292, 0xf90003e9#32), -- str x9, [sp]
  (296, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (300, 0x91000269#32), -- add x9, x19, #0x0
  (304, 0x91004129#32), -- add x9, x9, #0x10
  (308, 0xd280000a#32), -- mov x10, #0x0               // =0
  (312, 0xf900012a#32), -- str x10, [x9]
  (316, 0xd280000a#32), -- mov x10, #0x0               // =0
  (320, 0xf900052a#32), -- str x10, [x9, #0x8]
  (324, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (328, 0xf94003e9#32), -- ldr x9, [sp]
  (332, 0x910043ff#32), -- add sp, sp, #0x10
  (336, 0xb9004268#32), -- str w8, [x19, #0x40]
  (340, 0x140000b0#32), -- b 0x230810 <.LBB84_47>
  (344, 0x34000e29#32), -- cbz w9, 0x230718 <.LBB84_30>
  (348, 0x52800028#32), -- mov w8, #0x1                // =1
  (352, 0xd10043ff#32), -- sub sp, sp, #0x10
  (356, 0xf90003e9#32), -- str x9, [sp]
  (360, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (364, 0x91000269#32), -- add x9, x19, #0x0
  (368, 0x91004129#32), -- add x9, x9, #0x10
  (372, 0xd280000a#32), -- mov x10, #0x0               // =0
  (376, 0xf900012a#32), -- str x10, [x9]
  (380, 0xd280000a#32), -- mov x10, #0x0               // =0
  (384, 0xf900052a#32), -- str x10, [x9, #0x8]
  (388, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (392, 0xf94003e9#32), -- ldr x9, [sp]
  (396, 0x910043ff#32), -- add sp, sp, #0x10
  (400, 0xd10043ff#32), -- sub sp, sp, #0x10
  (404, 0xf90003e9#32), -- str x9, [sp]
  (408, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (412, 0x91000269#32), -- add x9, x19, #0x0
  (416, 0xf9000128#32), -- str x8, [x9]
  (420, 0xd280000a#32), -- mov x10, #0x0               // =0
  (424, 0xf900052a#32), -- str x10, [x9, #0x8]
  (428, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (432, 0xf94003e9#32), -- ldr x9, [sp]
  (436, 0x910043ff#32), -- add sp, sp, #0x10
  (440, 0xd10043ff#32), -- sub sp, sp, #0x10
  (444, 0xf90003e9#32), -- str x9, [sp]
  (448, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (452, 0x91000269#32), -- add x9, x19, #0x0
  (456, 0x91008129#32), -- add x9, x9, #0x20
  (460, 0xd280000a#32), -- mov x10, #0x0               // =0
  (464, 0xf900012a#32), -- str x10, [x9]
  (468, 0xd280000a#32), -- mov x10, #0x0               // =0
  (472, 0xf900052a#32), -- str x10, [x9, #0x8]
  (476, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (480, 0xf94003e9#32), -- ldr x9, [sp]
  (484, 0x910043ff#32), -- add sp, sp, #0x10
  (488, 0xd10043ff#32), -- sub sp, sp, #0x10
  (492, 0xf90003e9#32), -- str x9, [sp]
  (496, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (500, 0x91000269#32), -- add x9, x19, #0x0
  (504, 0x9100c129#32), -- add x9, x9, #0x30
  (508, 0xd280000a#32) -- mov x10, #0x0               // =0
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xf900012a#32), -- str x10, [x9]
  (516, 0xd280000a#32), -- mov x10, #0x0               // =0
  (520, 0xf900052a#32), -- str x10, [x9, #0x8]
  (524, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (528, 0xf94003e9#32), -- ldr x9, [sp]
  (532, 0x910043ff#32), -- add sp, sp, #0x10
  (536, 0xb9004268#32), -- str w8, [x19, #0x40]
  (540, 0x1400007e#32), -- b 0x230810 <.LBB84_47>
  (544, 0x71000d3f#32), -- cmp w9, #0x3
  (548, 0x5400060c#32), -- b.gt 0x2306e0 <.LBB84_23>
  (552, 0x7100093f#32), -- cmp w9, #0x2
  (556, 0x54000840#32), -- b.eq 0x230730 <.LBB84_32>
  (560, 0x71000d3f#32), -- cmp w9, #0x3
  (564, 0x54fff941#32), -- b.ne 0x230558 <.LBB84_10>
  (568, 0xd1001509#32), -- sub x9, x8, #0x5
  (572, 0xf100093f#32), -- cmp x9, #0x2
  (576, 0x540012e2#32), -- b.hs 0x230898 <.LBB84_52>
  (580, 0xa94222da#32), -- ldp x26, x8, [x22, #0x20]
  (584, 0xd10043ff#32), -- sub sp, sp, #0x10
  (588, 0xf90003e9#32), -- str x9, [sp]
  (592, 0xd343ff49#32), -- lsr x9, x26, #3
  (596, 0xaa08f537#32), -- orr x23, x9, x8, lsl #61
  (600, 0xf94003e9#32), -- ldr x9, [sp]
  (604, 0x910043ff#32), -- add sp, sp, #0x10
  (608, 0xeb1702bf#32), -- cmp x21, x23
  (612, 0x54002923#32), -- b.lo 0x230b84 <.LBB84_87>
  (616, 0xf9400ed8#32), -- ldr x24, [x22, #0x18]
  (620, 0xeb17031f#32), -- cmp x24, x23
  (624, 0x54002943#32), -- b.lo 0x230b94 <.LBB84_88>
  (628, 0xf9400ad6#32), -- ldr x22, [x22, #0x10]
  (632, 0xaa1403e0#32), -- mov x0, x20
  (636, 0xaa1703e2#32), -- mov x2, x23
  (640, 0x12000b59#32), -- and w25, w26, #0x7
  (644, 0xaa1603e1#32), -- mov x1, x22
  (648, 0x94007393#32), -- bl 0x24d4d0 <memcpy>
  (652, 0x34001a19#32), -- cbz w25, 0x2309c8 <.LBB84_67>
  (656, 0xeb17031f#32), -- cmp x24, x23
  (660, 0x54002969#32), -- b.ls 0x230bbc <.LBB84_91>
  (664, 0x910006e9#32), -- add x9, x23, #0x1
  (668, 0xd10043ff#32), -- sub sp, sp, #0x10
  (672, 0xf90003e9#32), -- str x9, [sp]
  (676, 0xaa1703e9#32), -- mov x9, x23
  (680, 0x8b0902c9#32), -- add x9, x22, x9
  (684, 0x39400128#32), -- ldrb w8, [x9]
  (688, 0xf94003e9#32), -- ldr x9, [sp]
  (692, 0x910043ff#32), -- add sp, sp, #0x10
  (696, 0xeb18013f#32), -- cmp x9, x24
  (700, 0x540000c1#32), -- b.ne 0x2306d0 <.LBB84_22>
  (704, 0xf2400b49#32), -- ands x9, x26, #0x7
  (708, 0x54000080#32), -- b.eq 0x2306d0 <.LBB84_22>
  (712, 0x1280000a#32), -- mov w10, #-0x1              // =-1
  (716, 0x1ac92149#32), -- lsl w9, w10, w9
  (720, 0x0a290108#32), -- bic w8, w8, w9
  (724, 0x52800029#32), -- mov w9, #0x1                // =1
  (728, 0x1ad92129#32), -- lsl w9, w9, w25
  (732, 0x2a090108#32), -- orr w8, w8, w9
  (736, 0x140000bc#32), -- b 0x2309cc <.LBB84_68>
  (740, 0xaa0303e4#32), -- mov x4, x3
  (744, 0x7100113f#32), -- cmp w9, #0x4
  (748, 0x540003c0#32), -- b.eq 0x230760 <.LBB84_35>
  (752, 0x7100153f#32), -- cmp w9, #0x5
  (756, 0x54fff341#32), -- b.ne 0x230558 <.LBB84_10>
  (760, 0xf100311f#32), -- cmp x8, #0xc
  (764, 0x54fff301#32) -- b.ne 0x230558 <.LBB84_10>
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0xb4002555#32), -- cbz x21, 0x230ba4 <.LBB84_89>
  (772, 0xa940e2d7#32), -- ldp x23, x24, [x22, #0x8]
  (776, 0xaa1803e8#32), -- mov x8, x24
  (780, 0xb4001977#32), -- cbz x23, 0x230a34 <.LBB84_75>
  (784, 0xb4001938#32), -- cbz x24, 0x230a30 <.LBB84_74>
  (788, 0xf94002e8#32), -- ldr x8, [x23]
  (792, 0x140000c8#32), -- b 0x230a34 <.LBB84_75>
  (796, 0xb4002475#32), -- cbz x21, 0x230ba4 <.LBB84_89>
  (800, 0x394006c8#32), -- ldrb w8, [x22, #0x1]
  (804, 0x52800029#32), -- mov w9, #0x1                // =1
  (808, 0xf9000269#32), -- str x9, [x19]
  (812, 0x39000288#32), -- strb w8, [x20]
  (816, 0x1400002f#32), -- b 0x2307e8 <.LBB84_46>
  (820, 0x927f0908#32), -- and x8, x8, #0xe
  (824, 0xf100091f#32), -- cmp x8, #0x2
  (828, 0x54fff101#32), -- b.ne 0x230558 <.LBB84_10>
  (832, 0xf9400ad7#32), -- ldr x23, [x22, #0x10]
  (836, 0xeb1502ff#32), -- cmp x23, x21
  (840, 0x54002208#32), -- b.hi 0x230b84 <.LBB84_87>
  (844, 0xf94006c1#32), -- ldr x1, [x22, #0x8]
  (848, 0xaa1403e0#32), -- mov x0, x20
  (852, 0xaa1703e2#32), -- mov x2, x23
  (856, 0x9400735f#32), -- bl 0x24d4d0 <memcpy>
  (860, 0xf9000277#32), -- str x23, [x19]
  (864, 0x14000023#32), -- b 0x2307e8 <.LBB84_46>
  (868, 0xf100251f#32), -- cmp x8, #0x9
  (872, 0x54000f8c#32), -- b.gt 0x230954 <.LBB84_61>
  (876, 0xd1001d09#32), -- sub x9, x8, #0x7
  (880, 0xf100093f#32), -- cmp x9, #0x2
  (884, 0x54000fe2#32), -- b.hs 0x23096c <.LBB84_64>
  (888, 0x52800308#32), -- mov w8, #0x18               // =24
  (892, 0x14000080#32), -- b 0x230978 <.LBB84_66>
  (896, 0xb4000341#32), -- cbz x1, 0x2307e4 <.LBB84_45>
  (900, 0xf9400101#32), -- ldr x1, [x8]
  (904, 0xeb15003f#32), -- cmp x1, x21
  (908, 0x54001f88#32), -- b.hi 0x230b78 <.LBB84_86>
  (912, 0xb40002c1#32), -- cbz x1, 0x2307e4 <.LBB84_45>
  (916, 0xa940a2c9#32), -- ldp x9, x8, [x22, #0x8]
  (920, 0xaa1f03ea#32), -- mov x10, xzr
  (924, 0xb4000069#32), -- cbz x9, 0x2307a4 <.LBB84_44>
  (928, 0xaa1f03eb#32), -- mov x11, xzr
  (932, 0x14000032#32), -- b 0x230868 <.LBB84_50>
  (936, 0xf100215f#32), -- cmp x10, #0x8
  (940, 0x927d092d#32), -- and x13, x9, #0x38
  (944, 0x9100054b#32), -- add x11, x10, #0x1
  (948, 0x9a9f310c#32), -- csel x12, x8, xzr, lo
  (952, 0xeb0b003f#32), -- cmp x1, x11
  (956, 0x91002129#32), -- add x9, x9, #0x8
  (960, 0x9acd258c#32), -- lsr x12, x12, x13
  (964, 0xd10043ff#32), -- sub sp, sp, #0x10
  (968, 0xf90003e9#32), -- str x9, [sp]
  (972, 0xaa0a03e9#32), -- mov x9, x10
  (976, 0x8b090289#32), -- add x9, x20, x9
  (980, 0x3900012c#32), -- strb w12, [x9]
  (984, 0xf94003e9#32), -- ldr x9, [sp]
  (988, 0x910043ff#32), -- add sp, sp, #0x10
  (992, 0xaa0b03ea#32), -- mov x10, x11
  (996, 0x54fffe21#32), -- b.ne 0x2307a4 <.LBB84_44>
  (1000, 0xf9000261#32), -- str x1, [x19]
  (1004, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1008, 0xf90003e9#32), -- str x9, [sp]
  (1012, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1016, 0x91000269#32), -- add x9, x19, #0x0
  (1020, 0x91010129#32) -- add x9, x9, #0x40
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk4 : List (Nat × BitVec 32) := [
  (1024, 0x5280000a#32), -- mov w10, #0x0               // =0
  (1028, 0xb900012a#32), -- str w10, [x9]
  (1032, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1036, 0xf94003e9#32), -- ldr x9, [sp]
  (1040, 0x910043ff#32), -- add sp, sp, #0x10
  (1044, 0xa9494ff4#32), -- ldp x20, x19, [sp, #0x90]
  (1048, 0xa94857f6#32), -- ldp x22, x21, [sp, #0x80]
  (1052, 0xa9475ff8#32), -- ldp x24, x23, [sp, #0x70]
  (1056, 0xa94667fa#32), -- ldp x26, x25, [sp, #0x60]
  (1060, 0xa9456ffe#32), -- ldp x30, x27, [sp, #0x50]
  (1064, 0x910283ff#32), -- add sp, sp, #0xa0
  (1068, 0xd65f03c0#32), -- ret
  (1072, 0xaa1f03ec#32), -- mov x12, xzr
  (1076, 0x927d094e#32), -- and x14, x10, #0x38
  (1080, 0x9100056d#32), -- add x13, x11, #0x1
  (1084, 0x9100214a#32), -- add x10, x10, #0x8
  (1088, 0x9ace258c#32), -- lsr x12, x12, x14
  (1092, 0xeb0d003f#32), -- cmp x1, x13
  (1096, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1100, 0xf90003e9#32), -- str x9, [sp]
  (1104, 0xaa0b03e9#32), -- mov x9, x11
  (1108, 0x8b090289#32), -- add x9, x20, x9
  (1112, 0x3900012c#32), -- strb w12, [x9]
  (1116, 0xf94003e9#32), -- ldr x9, [sp]
  (1120, 0x910043ff#32), -- add sp, sp, #0x10
  (1124, 0xaa0d03eb#32), -- mov x11, x13
  (1128, 0x54fffc00#32), -- b.eq 0x2307e4 <.LBB84_45>
  (1132, 0xd343fd6c#32), -- lsr x12, x11, #3
  (1136, 0xeb08019f#32), -- cmp x12, x8
  (1140, 0x54fffde2#32), -- b.hs 0x23082c <.LBB84_48>
  (1144, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1148, 0xf90003ea#32), -- str x10, [sp]
  (1152, 0xaa0c03ea#32), -- mov x10, x12
  (1156, 0xd37df14a#32), -- lsl x10, x10, #3
  (1160, 0x8b0a012a#32), -- add x10, x9, x10
  (1164, 0xf940014c#32), -- ldr x12, [x10]
  (1168, 0xf94003ea#32), -- ldr x10, [sp]
  (1172, 0x910043ff#32), -- add sp, sp, #0x10
  (1176, 0x17ffffe7#32), -- b 0x230830 <.LBB84_49>
  (1180, 0xf100111f#32), -- cmp x8, #0x4
  (1184, 0x54ffe5e1#32), -- b.ne 0x230558 <.LBB84_10>
  (1188, 0xa94222d9#32), -- ldp x25, x8, [x22, #0x20]
  (1192, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1196, 0xf90003e9#32), -- str x9, [sp]
  (1200, 0xd343ff29#32), -- lsr x9, x25, #3
  (1204, 0xaa08f537#32), -- orr x23, x9, x8, lsl #61
  (1208, 0xf94003e9#32), -- ldr x9, [sp]
  (1212, 0x910043ff#32), -- add sp, sp, #0x10
  (1216, 0xeb1702bf#32), -- cmp x21, x23
  (1220, 0x54001623#32), -- b.lo 0x230b84 <.LBB84_87>
  (1224, 0xf9400ed8#32), -- ldr x24, [x22, #0x18]
  (1228, 0xeb17031f#32), -- cmp x24, x23
  (1232, 0x54001643#32), -- b.lo 0x230b94 <.LBB84_88>
  (1236, 0xf9400ad6#32), -- ldr x22, [x22, #0x10]
  (1240, 0xaa1403e0#32), -- mov x0, x20
  (1244, 0xaa1703e2#32), -- mov x2, x23
  (1248, 0xaa1603e1#32), -- mov x1, x22
  (1252, 0x940072fc#32), -- bl 0x24d4d0 <memcpy>
  (1256, 0xeb17031f#32), -- cmp x24, x23
  (1260, 0x54000a09#32), -- b.ls 0x230a28 <.LBB84_73>
  (1264, 0xeb1702bf#32), -- cmp x21, x23
  (1268, 0x54001609#32), -- b.ls 0x230bb0 <.LBB84_90>
  (1272, 0x910006e9#32), -- add x9, x23, #0x1
  (1276, 0xd10043ff#32) -- sub sp, sp, #0x10
]

theorem chunk4_decodes :
    chunk4.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk5 : List (Nat × BitVec 32) := [
  (1280, 0xf90003e9#32), -- str x9, [sp]
  (1284, 0xaa1703e9#32), -- mov x9, x23
  (1288, 0x8b0902c9#32), -- add x9, x22, x9
  (1292, 0x39400128#32), -- ldrb w8, [x9]
  (1296, 0xf94003e9#32), -- ldr x9, [sp]
  (1300, 0x910043ff#32), -- add sp, sp, #0x10
  (1304, 0xeb18013f#32), -- cmp x9, x24
  (1308, 0x540000c1#32), -- b.ne 0x230930 <.LBB84_60>
  (1312, 0xf2400b29#32), -- ands x9, x25, #0x7
  (1316, 0x54000080#32), -- b.eq 0x230930 <.LBB84_60>
  (1320, 0x1280000a#32), -- mov w10, #-0x1              // =-1
  (1324, 0x1ac92149#32), -- lsl w9, w10, w9
  (1328, 0x0a290108#32), -- bic w8, w8, w9
  (1332, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1336, 0xf90003e9#32), -- str x9, [sp]
  (1340, 0xaa1703e9#32), -- mov x9, x23
  (1344, 0x8b090289#32), -- add x9, x20, x9
  (1348, 0x39000128#32), -- strb w8, [x9]
  (1352, 0xf94003e9#32), -- ldr x9, [sp]
  (1356, 0x910043ff#32), -- add sp, sp, #0x10
  (1360, 0xf9000278#32), -- str x24, [x19]
  (1364, 0x17ffffa6#32), -- b 0x2307e8 <.LBB84_46>
  (1368, 0xf100291f#32), -- cmp x8, #0xa
  (1372, 0x54000520#32), -- b.eq 0x2309fc <.LBB84_70>
  (1376, 0xf1002d1f#32), -- cmp x8, #0xb
  (1380, 0x54ffdfc1#32), -- b.ne 0x230558 <.LBB84_10>
  (1384, 0x52800308#32), -- mov w8, #0x18               // =24
  (1388, 0x14000026#32), -- b 0x230a00 <.LBB84_71>
  (1392, 0xf100251f#32), -- cmp x8, #0x9
  (1396, 0x54ffdf41#32), -- b.ne 0x230558 <.LBB84_10>
  (1400, 0x52800108#32), -- mov w8, #0x8                // =8
  (1404, 0xa9408ec2#32), -- ldp x2, x3, [x22, #0x8]
  (1408, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1412, 0xf90003e9#32), -- str x9, [sp]
  (1416, 0xaa0803e9#32), -- mov x9, x8
  (1420, 0x8b090029#32), -- add x9, x1, x9
  (1424, 0xf9400128#32), -- ldr x8, [x9]
  (1428, 0xf94003e9#32), -- ldr x9, [sp]
  (1432, 0x910043ff#32), -- add sp, sp, #0x10
  (1436, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1440, 0xf90003e9#32), -- str x9, [sp]
  (1444, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1448, 0x910043e9#32), -- add x9, sp, #0x10
  (1452, 0x91002129#32), -- add x9, x9, #0x8
  (1456, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1460, 0xf900012a#32), -- str x10, [x9]
  (1464, 0xf9000528#32), -- str x8, [x9, #0x8]
  (1468, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1472, 0xf94003e9#32), -- ldr x9, [sp]
  (1476, 0x910043ff#32), -- add sp, sp, #0x10
  (1480, 0x14000013#32), -- b 0x230a10 <.LBB84_72>
  (1484, 0x52800028#32), -- mov w8, #0x1                // =1
  (1488, 0xeb1702bf#32), -- cmp x21, x23
  (1492, 0x54000f09#32), -- b.ls 0x230bb0 <.LBB84_90>
  (1496, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1500, 0xf90003e9#32), -- str x9, [sp]
  (1504, 0xaa1703e9#32), -- mov x9, x23
  (1508, 0x8b090289#32), -- add x9, x20, x9
  (1512, 0x39000128#32), -- strb w8, [x9]
  (1516, 0xf94003e9#32), -- ldr x9, [sp]
  (1520, 0x910043ff#32), -- add sp, sp, #0x10
  (1524, 0x910006e8#32), -- add x8, x23, #0x1
  (1528, 0xf9000268#32), -- str x8, [x19]
  (1532, 0x17ffff7c#32) -- b 0x2307e8 <.LBB84_46>
]

theorem chunk5_decodes :
    chunk5.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk6 : List (Nat × BitVec 32) := [
  (1536, 0x52800108#32), -- mov w8, #0x8                // =8
  (1540, 0x8b080028#32), -- add x8, x1, x8
  (1544, 0xa9408ec2#32), -- ldp x2, x3, [x22, #0x8]
  (1548, 0xa9402109#32), -- ldp x9, x8, [x8]
  (1552, 0xa900a3e9#32), -- stp x9, x8, [sp, #0x8]
  (1556, 0x910023e1#32), -- add x1, sp, #0x8
  (1560, 0xaa1303e0#32), -- mov x0, x19
  (1564, 0xaa1403e5#32), -- mov x5, x20
  (1568, 0xaa1503e6#32), -- mov x6, x21
  (1572, 0x9400006a#32), -- bl 0x230bc8 <_ZN13ssz_fv_native5codec10emit_parts17h64cc0a69cd66c152E>
  (1576, 0x17ffff7b#32), -- b 0x230810 <.LBB84_47>
  (1580, 0xf9000278#32), -- str x24, [x19]
  (1584, 0x17ffff6f#32), -- b 0x2307e8 <.LBB84_46>
  (1588, 0xaa1f03e8#32), -- mov x8, xzr
  (1592, 0x39000288#32), -- strb w8, [x20]
  (1596, 0xb40000a4#32), -- cbz x4, 0x230a4c <.LBB84_78>
  (1600, 0xf9400488#32), -- ldr x8, [x4, #0x8]
  (1604, 0xb4000068#32), -- cbz x8, 0x230a4c <.LBB84_78>
  (1608, 0xf9400099#32), -- ldr x25, [x4]
  (1612, 0x14000002#32), -- b 0x230a50 <.LBB84_79>
  (1616, 0xaa1f03f9#32), -- mov x25, xzr
  (1620, 0xa940a029#32), -- ldp x9, x8, [x1, #0x8]
  (1624, 0x8b080508#32), -- add x8, x8, x8, lsl #1
  (1628, 0xd100613a#32), -- sub x26, x9, #0x18
  (1632, 0xd37df11b#32), -- lsl x27, x8, #3
  (1636, 0xb400039b#32), -- cbz x27, 0x230ad0 <.LBB84_84>
  (1640, 0xa9420740#32), -- ldp x0, x1, [x26, #0x20]
  (1644, 0xaa1703e2#32), -- mov x2, x23
  (1648, 0xaa1803e3#32), -- mov x3, x24
  (1652, 0x97ffd2cf#32), -- bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>
  (1656, 0x12001c08#32), -- and w8, w0, #0xff
  (1660, 0x9100635a#32), -- add x26, x26, #0x18
  (1664, 0xd100637b#32), -- sub x27, x27, #0x18
  (1668, 0x35ffff08#32), -- cbnz w8, 0x230a60 <.LBB84_80>
  (1672, 0xf9400341#32), -- ldr x1, [x26]
  (1676, 0xf9400ec2#32), -- ldr x2, [x22, #0x18]
  (1680, 0xd10006a5#32), -- sub x5, x21, #0x1
  (1684, 0x910023e0#32), -- add x0, sp, #0x8
  (1688, 0x91000684#32), -- add x4, x20, #0x1
  (1692, 0xaa1903e3#32), -- mov x3, x25
  (1696, 0x910023f6#32), -- add x22, sp, #0x8
  (1700, 0x97fffe57#32), -- bl 0x2303fc <_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE>
  (1704, 0xb9404bf4#32), -- ldr w20, [sp, #0x48]
  (1708, 0xf94007f5#32), -- ldr x21, [sp, #0x8]
  (1712, 0x34000614#32), -- cbz w20, 0x230b6c <.LBB84_85>
  (1716, 0x91002260#32), -- add x0, x19, #0x8
  (1720, 0x910022c1#32), -- add x1, x22, #0x8
  (1724, 0x52800702#32), -- mov w2, #0x38               // =56
  (1728, 0x94007285#32), -- bl 0x24d4d0 <memcpy>
  (1732, 0xb9404fe8#32), -- ldr w8, [sp, #0x4c]
  (1736, 0xf9000275#32), -- str x21, [x19]
  (1740, 0x29082274#32), -- stp w20, w8, [x19, #0x40]
  (1744, 0x17ffff51#32), -- b 0x230810 <.LBB84_47>
  (1748, 0x52800028#32), -- mov w8, #0x1                // =1
  (1752, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1756, 0xf90003e9#32), -- str x9, [sp]
  (1760, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1764, 0x91000269#32), -- add x9, x19, #0x0
  (1768, 0x9100c129#32), -- add x9, x9, #0x30
  (1772, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1776, 0xf900012a#32), -- str x10, [x9]
  (1780, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1784, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1788, 0xf94007ea#32) -- ldr x10, [sp, #0x8]
]

theorem chunk6_decodes :
    chunk6.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk7 : List (Nat × BitVec 32) := [
  (1792, 0xf94003e9#32), -- ldr x9, [sp]
  (1796, 0x910043ff#32), -- add sp, sp, #0x10
  (1800, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1804, 0xf90003e9#32), -- str x9, [sp]
  (1808, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1812, 0x91000269#32), -- add x9, x19, #0x0
  (1816, 0xf9000128#32), -- str x8, [x9]
  (1820, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1824, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1828, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1832, 0xf94003e9#32), -- ldr x9, [sp]
  (1836, 0x910043ff#32), -- add sp, sp, #0x10
  (1840, 0x52800288#32), -- mov w8, #0x14               // =20
  (1844, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1848, 0xf90003e9#32), -- str x9, [sp]
  (1852, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1856, 0x91000269#32), -- add x9, x19, #0x0
  (1860, 0x91008129#32), -- add x9, x9, #0x20
  (1864, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1868, 0xf900012a#32), -- str x10, [x9]
  (1872, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1876, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1880, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1884, 0xf94003e9#32), -- ldr x9, [sp]
  (1888, 0x910043ff#32), -- add sp, sp, #0x10
  (1892, 0xa9016277#32), -- stp x23, x24, [x19, #0x10]
  (1896, 0xb9004268#32), -- str w8, [x19, #0x40]
  (1900, 0x17ffff2a#32), -- b 0x230810 <.LBB84_47>
  (1904, 0x910006a8#32), -- add x8, x21, #0x1
  (1908, 0xf9000268#32), -- str x8, [x19]
  (1912, 0x17ffff1d#32), -- b 0x2307e8 <.LBB84_46>
  (1916, 0xaa1f03e0#32), -- mov x0, xzr
  (1920, 0xaa1503e2#32), -- mov x2, x21
  (1924, 0x97ffb570#32), -- bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>
  (1928, 0xaa1f03e0#32), -- mov x0, xzr
  (1932, 0xaa1703e1#32), -- mov x1, x23
  (1936, 0xaa1503e2#32), -- mov x2, x21
  (1940, 0x97ffb56c#32), -- bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>
  (1944, 0xaa1f03e0#32), -- mov x0, xzr
  (1948, 0xaa1703e1#32), -- mov x1, x23
  (1952, 0xaa1803e2#32), -- mov x2, x24
  (1956, 0x97ffb568#32), -- bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>
  (1960, 0xaa1f03e0#32), -- mov x0, xzr
  (1964, 0xaa1f03e1#32), -- mov x1, xzr
  (1968, 0x97ffb571#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1972, 0xaa1703e0#32), -- mov x0, x23
  (1976, 0xaa1503e1#32), -- mov x1, x21
  (1980, 0x97ffb56e#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1984, 0xaa1703e0#32), -- mov x0, x23
  (1988, 0xaa1803e1#32), -- mov x1, x24
  (1992, 0x97ffb56b#32) -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
]

theorem chunk7_decodes :
    chunk7.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7

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

theorem chunk4_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk4 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append, member, true_or, or_true]

theorem chunk5_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk5 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append, member, true_or, or_true]

theorem chunk6_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk6 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append, member, true_or, or_true]

theorem chunk7_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk7 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append, member, true_or, or_true]

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, chunk3_decodes, chunk4_decodes, chunk5_decodes, chunk6_decodes, chunk7_decodes, Bool.and_self]

end SszArm.Codec.Linked.Emit
