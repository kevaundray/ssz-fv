import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.DecodeOffsets

/-- Actual ELF entry address of _ZN13ssz_fv_native5codec14decode_offsets17h3986df5c439cd32dE. -/
def address : Nat := 2322732

def byteSize : Nat := 1508

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10603ff#32), -- sub sp, sp, #0x180
  (4, 0xa9127bfd#32), -- stp x29, x30, [sp, #0x120]
  (8, 0xa9136ffc#32), -- stp x28, x27, [sp, #0x130]
  (12, 0xa91467fa#32), -- stp x26, x25, [sp, #0x140]
  (16, 0xa9155ff8#32), -- stp x24, x23, [sp, #0x150]
  (20, 0xa91657f6#32), -- stp x22, x21, [sp, #0x160]
  (24, 0xa9174ff4#32), -- stp x20, x19, [sp, #0x170]
  (28, 0xaa0203f4#32), -- mov x20, x2
  (32, 0xaa0003f3#32), -- mov x19, x0
  (36, 0xb40002e2#32), -- cbz x2, 0x2371ac <.LBB101_7>
  (40, 0xaa0403f5#32), -- mov x21, x4
  (44, 0xb4002c44#32), -- cbz x4, 0x2376e0 <.LBB101_57>
  (48, 0xf10006a8#32), -- subs x8, x21, #0x1
  (52, 0x54002c60#32), -- b.eq 0x2376ec <.LBB101_58>
  (56, 0xf1000aa9#32), -- subs x9, x21, #0x2
  (60, 0x54002c89#32), -- b.ls 0x2376f8 <.LBB101_59>
  (64, 0xf1000eaa#32), -- subs x10, x21, #0x3
  (68, 0x54002ca0#32), -- b.eq 0x237704 <.LBB101_60>
  (72, 0x3940006b#32), -- ldrb w11, [x3]
  (76, 0x3940046c#32), -- ldrb w12, [x3, #0x1]
  (80, 0xaa0503f6#32), -- mov x22, x5
  (84, 0x3940086d#32), -- ldrb w13, [x3, #0x2]
  (88, 0xaa0303f7#32), -- mov x23, x3
  (92, 0xaa0103e4#32), -- mov x4, x1
  (96, 0xaa0c216b#32), -- orr x11, x11, x12, lsl #8
  (100, 0x39400c6c#32), -- ldrb w12, [x3, #0x3]
  (104, 0xaa0d416b#32), -- orr x11, x11, x13, lsl #16
  (108, 0xaa0c6172#32), -- orr x18, x11, x12, lsl #24
  (112, 0xf100068b#32), -- subs x11, x20, #0x1
  (116, 0x54000121#32), -- b.ne 0x2371c4 <.LBB101_9>
  (120, 0xaa1203e0#32), -- mov x0, x18
  (124, 0x14000033#32), -- b 0x237274 <.LBB101_16>
  (128, 0x52800217#32), -- mov w23, #0x10              // =16
  (132, 0x52800089#32), -- mov w9, #0x4                // =4
  (136, 0xaa1f03e8#32), -- mov x8, xzr
  (140, 0xa901d277#32), -- stp x23, x20, [x19, #0x18]
  (144, 0x39004269#32), -- strb w9, [x19, #0x10]
  (148, 0x14000113#32), -- b 0x23760c <.LBB101_45>
  (152, 0xd10012ad#32), -- sub x13, x21, #0x4
  (156, 0xd342fd0c#32), -- lsr x12, x8, #2
  (160, 0xd342fd2e#32), -- lsr x14, x9, #2
  (164, 0xd342fd4f#32), -- lsr x15, x10, #2
  (168, 0xd342fdb0#32), -- lsr x16, x13, #2
  (172, 0x91001ef1#32), -- add x17, x23, #0x7
  (176, 0xb400262c#32), -- cbz x12, 0x2376a0 <.LBB101_51>
  (180, 0xb400258e#32), -- cbz x14, 0x237690 <.LBB101_50>
  (184, 0xb40024ef#32), -- cbz x15, 0x237680 <.LBB101_49>
  (188, 0xb4002450#32), -- cbz x16, 0x237670 <.LBB101_48>
  (192, 0xd10043ff#32), -- sub sp, sp, #0x10
  (196, 0xf90003e9#32), -- str x9, [sp]
  (200, 0x91000229#32), -- add x9, x17, #0x0
  (204, 0xd1000d29#32), -- sub x9, x9, #0x3
  (208, 0x39400120#32), -- ldrb w0, [x9]
  (212, 0xf94003e9#32), -- ldr x9, [sp]
  (216, 0x910043ff#32), -- add sp, sp, #0x10
  (220, 0xd10043ff#32), -- sub sp, sp, #0x10
  (224, 0xf90003e9#32), -- str x9, [sp]
  (228, 0x91000229#32), -- add x9, x17, #0x0
  (232, 0xd1000929#32), -- sub x9, x9, #0x2
  (236, 0x39400121#32), -- ldrb w1, [x9]
  (240, 0xf94003e9#32), -- ldr x9, [sp]
  (244, 0x910043ff#32), -- add sp, sp, #0x10
  (248, 0xd10043ff#32), -- sub sp, sp, #0x10
  (252, 0xf90003e9#32) -- str x9, [sp]
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0x91000229#32), -- add x9, x17, #0x0
  (260, 0xd1000529#32), -- sub x9, x9, #0x1
  (264, 0x39400122#32), -- ldrb w2, [x9]
  (268, 0xf94003e9#32), -- ldr x9, [sp]
  (272, 0x910043ff#32), -- add sp, sp, #0x10
  (276, 0xaa012000#32), -- orr x0, x0, x1, lsl #8
  (280, 0x38404621#32), -- ldrb w1, [x17], #0x4
  (284, 0xaa024000#32), -- orr x0, x0, x2, lsl #16
  (288, 0xaa016000#32), -- orr x0, x0, x1, lsl #24
  (292, 0xeb12001f#32), -- cmp x0, x18
  (296, 0x54001ba3#32), -- b.lo 0x2375c8 <.LBB101_43>
  (300, 0xd1000610#32), -- sub x16, x16, #0x1
  (304, 0xd10005ef#32), -- sub x15, x15, #0x1
  (308, 0xd10005ce#32), -- sub x14, x14, #0x1
  (312, 0xf100056b#32), -- subs x11, x11, #0x1
  (316, 0xd100058c#32), -- sub x12, x12, #0x1
  (320, 0xaa0003f2#32), -- mov x18, x0
  (324, 0x54fffb61#32), -- b.ne 0x2371dc <.LBB101_10>
  (328, 0xeb15001f#32), -- cmp x0, x21
  (332, 0x54000069#32), -- b.ls 0x237284 <.LBB101_18>
  (336, 0x52800129#32), -- mov w9, #0x9                // =9
  (340, 0x140000d3#32), -- b 0x2375cc <.LBB101_44>
  (344, 0x52800608#32), -- mov w8, #0x30               // =48
  (348, 0xd100c3ff#32), -- sub sp, sp, #0x30
  (352, 0xf90003e9#32), -- str x9, [sp]
  (356, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (360, 0xf9000beb#32), -- str x11, [sp, #0x10]
  (364, 0xf9000fec#32), -- str x12, [sp, #0x18]
  (368, 0xf90013ed#32), -- str x13, [sp, #0x20]
  (372, 0xf90017ee#32), -- str x14, [sp, #0x28]
  (376, 0x2a1403e9#32), -- mov w9, w20
  (380, 0xd360fe8a#32), -- lsr x10, x20, #32
  (384, 0x2a0803eb#32), -- mov w11, w8
  (388, 0xd360fd0c#32), -- lsr x12, x8, #32
  (392, 0x9b0b7d2d#32), -- mul x13, x9, x11
  (396, 0xd360fdad#32), -- lsr x13, x13, #32
  (400, 0x9b0b354d#32), -- madd x13, x10, x11, x13
  (404, 0xd360fdab#32), -- lsr x11, x13, #32
  (408, 0x2a0d03ee#32), -- mov w14, w13
  (412, 0x9b0c392e#32), -- madd x14, x9, x12, x14
  (416, 0xd360fdce#32), -- lsr x14, x14, #32
  (420, 0x9b0c2d4d#32), -- madd x13, x10, x12, x11
  (424, 0x8b0e01ad#32), -- add x13, x13, x14
  (428, 0xaa0d03e8#32), -- mov x8, x13
  (432, 0xf94017ee#32), -- ldr x14, [sp, #0x28]
  (436, 0xf94013ed#32), -- ldr x13, [sp, #0x20]
  (440, 0xf9400fec#32), -- ldr x12, [sp, #0x18]
  (444, 0xf9400beb#32), -- ldr x11, [sp, #0x10]
  (448, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (452, 0xf94003e9#32), -- ldr x9, [sp]
  (456, 0x9100c3ff#32), -- add sp, sp, #0x30
  (460, 0xeb0803ff#32), -- cmp xzr, x8
  (464, 0x540014a1#32), -- b.ne 0x237590 <.LBB101_41>
  (468, 0x8b140688#32), -- add x8, x20, x20, lsl #1
  (472, 0xd37ced0a#32), -- lsl x10, x8, #4
  (476, 0xd10043ff#32), -- sub sp, sp, #0x10
  (480, 0xf90003e9#32), -- str x9, [sp]
  (484, 0x92410149#32), -- and x9, x10, #0x8000000000000000
  (488, 0xb5000089#32), -- cbnz x9, 0x237324 <.Llower_arm_725>
  (492, 0xf94003e9#32), -- ldr x9, [sp]
  (496, 0x910043ff#32), -- add sp, sp, #0x10
  (500, 0x14000004#32), -- b 0x237330 <.Llower_arm_726>
  (504, 0xf94003e9#32), -- ldr x9, [sp]
  (508, 0x910043ff#32) -- add sp, sp, #0x10
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0x14000099#32), -- b 0x237590 <.LBB101_41>
  (516, 0xf94002c8#32), -- ldr x8, [x22]
  (520, 0xf9400acb#32), -- ldr x11, [x22, #0x10]
  (524, 0xab08016c#32), -- adds x12, x11, x8
  (528, 0x540012a2#32), -- b.hs 0x237590 <.LBB101_41>
  (532, 0xb100419f#32), -- cmn x12, #0x10
  (536, 0x54001268#32), -- b.hi 0x237590 <.LBB101_41>
  (540, 0x91003d89#32), -- add x9, x12, #0xf
  (544, 0x927ced29#32), -- and x9, x9, #0xfffffffffffffff0
  (548, 0xcb0c012c#32), -- sub x12, x9, x12
  (552, 0xab0b018b#32), -- adds x11, x12, x11
  (556, 0x540011c2#32), -- b.hs 0x237590 <.LBB101_41>
  (560, 0xab0a016a#32), -- adds x10, x11, x10
  (564, 0x54001182#32), -- b.hs 0x237590 <.LBB101_41>
  (568, 0xf94006cc#32), -- ldr x12, [x22, #0x8]
  (572, 0xeb0c015f#32), -- cmp x10, x12
  (576, 0x54001128#32), -- b.hi 0x237590 <.LBB101_41>
  (580, 0x8b0b0108#32), -- add x8, x8, x11
  (584, 0x9100213a#32), -- add x26, x9, #0x8
  (588, 0xcb1403e9#32), -- neg x9, x20
  (592, 0xa900a7e8#32), -- stp x8, x9, [sp, #0x8]
  (596, 0x91000ea8#32), -- add x8, x21, #0x3
  (600, 0x910006ab#32), -- add x11, x21, #0x1
  (604, 0xcb480be8#32), -- neg x8, x8, lsr #2
  (608, 0xf9000aca#32), -- str x10, [x22, #0x10]
  (612, 0x91000aaa#32), -- add x10, x21, #0x2
  (616, 0x52800029#32), -- mov w9, #0x1                // =1
  (620, 0xcb4b0beb#32), -- neg x11, x11, lsr #2
  (624, 0xcb4a0bea#32), -- neg x10, x10, lsr #2
  (628, 0xf9001fe8#32), -- str x8, [sp, #0x38]
  (632, 0xcb140128#32), -- sub x8, x9, x20
  (636, 0xaa1f03fd#32), -- mov x29, xzr
  (640, 0xaa1f03f9#32), -- mov x25, xzr
  (644, 0xf9000fe8#32), -- str x8, [sp, #0x18]
  (648, 0x927ef6a8#32), -- and x8, x21, #0xfffffffffffffffc
  (652, 0x91000ef8#32), -- add x24, x23, #0x3
  (656, 0xa902abeb#32), -- stp x11, x10, [sp, #0x28]
  (660, 0xf90013e8#32), -- str x8, [sp, #0x20]
  (664, 0xf9401fe8#32), -- ldr x8, [sp, #0x38]
  (668, 0xeb1d011f#32), -- cmp x8, x29
  (672, 0x54001780#32), -- b.eq 0x2376bc <.LBB101_53>
  (676, 0xf9401be8#32), -- ldr x8, [sp, #0x30]
  (680, 0xeb1d011f#32), -- cmp x8, x29
  (684, 0x54001780#32), -- b.eq 0x2376c8 <.LBB101_54>
  (688, 0xf94017e8#32), -- ldr x8, [sp, #0x28]
  (692, 0xeb1d011f#32), -- cmp x8, x29
  (696, 0x54001660#32), -- b.eq 0x2376b0 <.LBB101_52>
  (700, 0xf94013e8#32), -- ldr x8, [sp, #0x20]
  (704, 0xeb19011f#32), -- cmp x8, x25
  (708, 0x54001720#32), -- b.eq 0x2376d4 <.LBB101_55>
  (712, 0x8b190309#32), -- add x9, x24, x25
  (716, 0x8b19030b#32), -- add x11, x24, x25
  (720, 0xf9400fec#32), -- ldr x12, [sp, #0x18]
  (724, 0xd10043ff#32), -- sub sp, sp, #0x10
  (728, 0xf90003ea#32), -- str x10, [sp]
  (732, 0x9100012a#32), -- add x10, x9, #0x0
  (736, 0xd1000d4a#32), -- sub x10, x10, #0x3
  (740, 0x39400148#32), -- ldrb w8, [x10]
  (744, 0xf94003ea#32), -- ldr x10, [sp]
  (748, 0x910043ff#32), -- add sp, sp, #0x10
  (752, 0xd10043ff#32), -- sub sp, sp, #0x10
  (756, 0xf90003ea#32), -- str x10, [sp]
  (760, 0x9100012a#32), -- add x10, x9, #0x0
  (764, 0xd100094a#32) -- sub x10, x10, #0x2
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0x39400149#32), -- ldrb w9, [x10]
  (772, 0xf94003ea#32), -- ldr x10, [sp]
  (776, 0x910043ff#32), -- add sp, sp, #0x10
  (780, 0xd10043ff#32), -- sub sp, sp, #0x10
  (784, 0xf90003e9#32), -- str x9, [sp]
  (788, 0x91000169#32), -- add x9, x11, #0x0
  (792, 0xd1000529#32), -- sub x9, x9, #0x1
  (796, 0x3940012a#32), -- ldrb w10, [x9]
  (800, 0xf94003e9#32), -- ldr x9, [sp]
  (804, 0x910043ff#32), -- add sp, sp, #0x10
  (808, 0x3940016b#32), -- ldrb w11, [x11]
  (812, 0xeb1d019f#32), -- cmp x12, x29
  (816, 0xaa1503e1#32), -- mov x1, x21
  (820, 0x540002c0#32), -- b.eq 0x2374b8 <.LBB101_36>
  (824, 0x91001320#32), -- add x0, x25, #0x4
  (828, 0xeb15001f#32), -- cmp x0, x21
  (832, 0x54001362#32), -- b.hs 0x2376d8 <.LBB101_56>
  (836, 0x91001720#32), -- add x0, x25, #0x5
  (840, 0xeb15001f#32), -- cmp x0, x21
  (844, 0x54001302#32), -- b.hs 0x2376d8 <.LBB101_56>
  (848, 0x91001b20#32), -- add x0, x25, #0x6
  (852, 0xeb15001f#32), -- cmp x0, x21
  (856, 0x540012a2#32), -- b.hs 0x2376d8 <.LBB101_56>
  (860, 0x91001f20#32), -- add x0, x25, #0x7
  (864, 0xeb15001f#32), -- cmp x0, x21
  (868, 0x54001242#32), -- b.hs 0x2376d8 <.LBB101_56>
  (872, 0x8b19030c#32), -- add x12, x24, x25
  (876, 0x8b19030e#32), -- add x14, x24, x25
  (880, 0x3940058d#32), -- ldrb w13, [x12, #0x1]
  (884, 0x3940098c#32), -- ldrb w12, [x12, #0x2]
  (888, 0x39400dcf#32), -- ldrb w15, [x14, #0x3]
  (892, 0xaa0c21ac#32), -- orr x12, x13, x12, lsl #8
  (896, 0x394011cd#32), -- ldrb w13, [x14, #0x4]
  (900, 0xaa0f418c#32), -- orr x12, x12, x15, lsl #16
  (904, 0xaa0d6181#32), -- orr x1, x12, x13, lsl #24
  (908, 0xaa092108#32), -- orr x8, x8, x9, lsl #8
  (912, 0xaa0a4108#32), -- orr x8, x8, x10, lsl #16
  (916, 0xaa0b6108#32), -- orr x8, x8, x11, lsl #24
  (920, 0xeb080023#32), -- subs x3, x1, x8
  (924, 0x54000ce3#32), -- b.lo 0x237664 <.LBB101_47>
  (928, 0xeb15003f#32), -- cmp x1, x21
  (932, 0x54000ca8#32), -- b.hi 0x237664 <.LBB101_47>
  (936, 0x910283e0#32), -- add x0, sp, #0xa0
  (940, 0x8b0802e2#32), -- add x2, x23, x8
  (944, 0xaa0403fc#32), -- mov x28, x4
  (948, 0xaa0403e1#32), -- mov x1, x4
  (952, 0xaa1603e4#32), -- mov x4, x22
  (956, 0x97fff22e#32), -- bl 0x233da0 <_ZN13ssz_fv_native5codec11deserialize17h539c5ca52740cbedE>
  (960, 0xb940a3e8#32), -- ldr w8, [sp, #0xa0]
  (964, 0xd10043ff#32), -- sub sp, sp, #0x10
  (968, 0xf90003e9#32), -- str x9, [sp]
  (972, 0x12000109#32), -- and w9, w8, #0x1
  (976, 0x35000089#32), -- cbnz w9, 0x23750c <.Llower_arm_727>
  (980, 0xf94003e9#32), -- ldr x9, [sp]
  (984, 0x910043ff#32), -- add sp, sp, #0x10
  (988, 0x14000004#32), -- b 0x237518 <.Llower_arm_728>
  (992, 0xf94003e9#32), -- ldr x9, [sp]
  (996, 0x910043ff#32), -- add sp, sp, #0x10
  (1000, 0x14000047#32), -- b 0x237630 <.LBB101_46>
  (1004, 0x910283e8#32), -- add x8, sp, #0xa0
  (1008, 0xf9405bfb#32), -- ldr x27, [sp, #0xb0]
  (1012, 0x9101c3e0#32), -- add x0, sp, #0x70
  (1016, 0x91006101#32), -- add x1, x8, #0x18
  (1020, 0x52800502#32) -- mov w2, #0x28               // =40
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk4 : List (Nat × BitVec 32) := [
  (1024, 0x940057e9#32), -- bl 0x24d4d0 <memcpy>
  (1028, 0x9103e3e0#32), -- add x0, sp, #0xf8
  (1032, 0x9101c3e1#32), -- add x1, sp, #0x70
  (1036, 0x52800502#32), -- mov w2, #0x28               // =40
  (1040, 0x940057e5#32), -- bl 0x24d4d0 <memcpy>
  (1044, 0x9103e3e1#32), -- add x1, sp, #0xf8
  (1048, 0xaa1a03e0#32), -- mov x0, x26
  (1052, 0x52800502#32), -- mov w2, #0x28               // =40
  (1056, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1060, 0xf90003e9#32), -- str x9, [sp]
  (1064, 0x91000349#32), -- add x9, x26, #0x0
  (1068, 0xd1002129#32), -- sub x9, x9, #0x8
  (1072, 0xf900013b#32), -- str x27, [x9]
  (1076, 0xf94003e9#32), -- ldr x9, [sp]
  (1080, 0x910043ff#32), -- add sp, sp, #0x10
  (1084, 0x940057da#32), -- bl 0x24d4d0 <memcpy>
  (1088, 0xf9400be8#32), -- ldr x8, [sp, #0x10]
  (1092, 0xd10007bd#32), -- sub x29, x29, #0x1
  (1096, 0x9100c35a#32), -- add x26, x26, #0x30
  (1100, 0x91001339#32), -- add x25, x25, #0x4
  (1104, 0xaa1c03e4#32), -- mov x4, x28
  (1108, 0xeb1d011f#32), -- cmp x8, x29
  (1112, 0x54fff201#32), -- b.ne 0x2373c4 <.LBB101_26>
  (1116, 0xf94007f7#32), -- ldr x23, [sp, #0x8]
  (1120, 0x17ffff09#32), -- b 0x2371b0 <.LBB101_8>
  (1124, 0x6f00e400#32), -- movi v0.2d, #0000000000000000
  (1128, 0xaa1f03f4#32), -- mov x20, xzr
  (1132, 0x52900015#32), -- mov w21, #0x8000            // =32768
  (1136, 0x52800037#32), -- mov w23, #0x1               // =1
  (1140, 0xad0283e0#32), -- stp q0, q0, [sp, #0x50]
  (1144, 0x3d8013e0#32), -- str q0, [sp, #0x40]
  (1148, 0x91006260#32), -- add x0, x19, #0x18
  (1152, 0x910103e1#32), -- add x1, sp, #0x40
  (1156, 0x52800602#32), -- mov w2, #0x30               // =48
  (1160, 0x940057c7#32), -- bl 0x24d4d0 <memcpy>
  (1164, 0x52800028#32), -- mov w8, #0x1                // =1
  (1168, 0xa900d277#32), -- stp x23, x20, [x19, #0x8]
  (1172, 0x29095a75#32), -- stp w21, w22, [x19, #0x48]
  (1176, 0x14000012#32), -- b 0x23760c <.LBB101_45>
  (1180, 0x52800109#32), -- mov w9, #0x8                // =8
  (1184, 0x6f00e400#32), -- movi v0.2d, #0000000000000000
  (1188, 0x52800028#32), -- mov w8, #0x1                // =1
  (1192, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1196, 0xf90003e9#32), -- str x9, [sp]
  (1200, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1204, 0x91000269#32), -- add x9, x19, #0x0
  (1208, 0x91010129#32), -- add x9, x9, #0x40
  (1212, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1216, 0xf900012a#32), -- str x10, [x9]
  (1220, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1224, 0xf94003e9#32), -- ldr x9, [sp]
  (1228, 0x910043ff#32), -- add sp, sp, #0x10
  (1232, 0xf9000668#32), -- str x8, [x19, #0x8]
  (1236, 0xb9004a69#32), -- str w9, [x19, #0x48]
  (1240, 0xad010260#32), -- stp q0, q0, [x19, #0x20]
  (1244, 0x3d800660#32), -- str q0, [x19, #0x10]
  (1248, 0xf9000268#32), -- str x8, [x19]
  (1252, 0xa9574ff4#32), -- ldp x20, x19, [sp, #0x170]
  (1256, 0xa95657f6#32), -- ldp x22, x21, [sp, #0x160]
  (1260, 0xa9555ff8#32), -- ldp x24, x23, [sp, #0x150]
  (1264, 0xa95467fa#32), -- ldp x26, x25, [sp, #0x140]
  (1268, 0xa9536ffc#32), -- ldp x28, x27, [sp, #0x130]
  (1272, 0xa9527bfd#32), -- ldp x29, x30, [sp, #0x120]
  (1276, 0x910603ff#32) -- add sp, sp, #0x180
]

theorem chunk4_decodes :
    chunk4.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk5 : List (Nat × BitVec 32) := [
  (1280, 0xd65f03c0#32), -- ret
  (1284, 0xa94ad3f7#32), -- ldp x23, x20, [sp, #0xa8]
  (1288, 0x910283e8#32), -- add x8, sp, #0xa0
  (1292, 0x9101c3e0#32), -- add x0, sp, #0x70
  (1296, 0x91006101#32), -- add x1, x8, #0x18
  (1300, 0x52800602#32), -- mov w2, #0x30               // =48
  (1304, 0x940057a3#32), -- bl 0x24d4d0 <memcpy>
  (1308, 0x295d5bf5#32), -- ldp w21, w22, [sp, #0xe8]
  (1312, 0x910103e0#32), -- add x0, sp, #0x40
  (1316, 0x9101c3e1#32), -- add x1, sp, #0x70
  (1320, 0x52800602#32), -- mov w2, #0x30               // =48
  (1324, 0x9400579e#32), -- bl 0x24d4d0 <memcpy>
  (1328, 0x35fffa75#32), -- cbnz w21, 0x2375a8 <.LBB101_42>
  (1332, 0x17fffed4#32), -- b 0x2371b0 <.LBB101_8>
  (1336, 0xaa0803e0#32), -- mov x0, x8
  (1340, 0xaa1503e2#32), -- mov x2, x21
  (1344, 0x97ff9ab5#32), -- bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>
  (1348, 0x927ef5a8#32), -- and x8, x13, #0xfffffffffffffffc
  (1352, 0xaa1503e1#32), -- mov x1, x21
  (1356, 0x91001d00#32), -- add x0, x8, #0x7
  (1360, 0x97ff9abd#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1364, 0x927ef548#32), -- and x8, x10, #0xfffffffffffffffc
  (1368, 0xaa1503e1#32), -- mov x1, x21
  (1372, 0x91001900#32), -- add x0, x8, #0x6
  (1376, 0x97ff9ab9#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1380, 0x927ef528#32), -- and x8, x9, #0xfffffffffffffffc
  (1384, 0xaa1503e1#32), -- mov x1, x21
  (1388, 0x91001500#32), -- add x0, x8, #0x5
  (1392, 0x97ff9ab5#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1396, 0x927ef508#32), -- and x8, x8, #0xfffffffffffffffc
  (1400, 0xaa1503e1#32), -- mov x1, x21
  (1404, 0x91001100#32), -- add x0, x8, #0x4
  (1408, 0x97ff9ab1#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1412, 0x91000b20#32), -- add x0, x25, #0x2
  (1416, 0xaa1503e1#32), -- mov x1, x21
  (1420, 0x97ff9aae#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1424, 0xaa1903e0#32), -- mov x0, x25
  (1428, 0xaa1503e1#32), -- mov x1, x21
  (1432, 0x97ff9aab#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1436, 0x91000720#32), -- add x0, x25, #0x1
  (1440, 0xaa1503e1#32), -- mov x1, x21
  (1444, 0x97ff9aa8#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1448, 0x91000f20#32), -- add x0, x25, #0x3
  (1452, 0xaa1503e1#32), -- mov x1, x21
  (1456, 0x97ff9aa5#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1460, 0xaa1f03e0#32), -- mov x0, xzr
  (1464, 0xaa1f03e1#32), -- mov x1, xzr
  (1468, 0x97ff9aa2#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1472, 0x52800020#32), -- mov w0, #0x1                // =1
  (1476, 0x52800021#32), -- mov w1, #0x1                // =1
  (1480, 0x97ff9a9f#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1484, 0x52800040#32), -- mov w0, #0x2                // =2
  (1488, 0x52800041#32), -- mov w1, #0x2                // =2
  (1492, 0x97ff9a9c#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1496, 0x52800060#32), -- mov w0, #0x3                // =3
  (1500, 0x52800061#32), -- mov w1, #0x3                // =3
  (1504, 0x97ff9a99#32) -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
]

theorem chunk5_decodes :
    chunk5.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5

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

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, chunk3_decodes, chunk4_decodes, chunk5_decodes, Bool.and_self]

end SszArm.Codec.Linked.DecodeOffsets
