import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.DecodeList

/-- Actual ELF entry address of _ZN13ssz_fv_native5codec11decode_list17h1123a2f8d52877c5E. -/
def address : Nat := 2324240

def byteSize : Nat := 2724

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10303ff#32), -- sub sp, sp, #0xc0
  (4, 0xa9067bfd#32), -- stp x29, x30, [sp, #0x60]
  (8, 0xa9076ffc#32), -- stp x28, x27, [sp, #0x70]
  (12, 0xa90867fa#32), -- stp x26, x25, [sp, #0x80]
  (16, 0xa9095ff8#32), -- stp x24, x23, [sp, #0x90]
  (20, 0xa90a57f6#32), -- stp x22, x21, [sp, #0xa0]
  (24, 0xa90b4ff4#32), -- stp x20, x19, [sp, #0xb0]
  (28, 0xb4000ae4#32), -- cbz x4, 0x237888 <.LBB102_9>
  (32, 0xd2c00028#32), -- mov x8, #0x100000000        // =4294967296
  (36, 0xeb08009f#32), -- cmp x4, x8
  (40, 0x54000060#32), -- b.eq 0x237744 <.LBB102_3>
  (44, 0xd360fc88#32), -- lsr x8, x4, #32
  (48, 0xb4000568#32), -- cbz x8, 0x2377ec <.LBB102_4>
  (52, 0x528002a8#32), -- mov w8, #0x15               // =21
  (56, 0x52800029#32), -- mov w9, #0x1                // =1
  (60, 0xd10043ff#32), -- sub sp, sp, #0x10
  (64, 0xf90003e9#32), -- str x9, [sp]
  (68, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (72, 0x91000009#32), -- add x9, x0, #0x0
  (76, 0x9100e129#32), -- add x9, x9, #0x38
  (80, 0xd280000a#32), -- mov x10, #0x0               // =0
  (84, 0xf900012a#32), -- str x10, [x9]
  (88, 0xd280000a#32), -- mov x10, #0x0               // =0
  (92, 0xf900052a#32), -- str x10, [x9, #0x8]
  (96, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (100, 0xf94003e9#32), -- ldr x9, [sp]
  (104, 0x910043ff#32), -- add sp, sp, #0x10
  (108, 0xd10043ff#32), -- sub sp, sp, #0x10
  (112, 0xf90003e9#32), -- str x9, [sp]
  (116, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (120, 0x91000009#32), -- add x9, x0, #0x0
  (124, 0x9100a129#32), -- add x9, x9, #0x28
  (128, 0xd280000a#32), -- mov x10, #0x0               // =0
  (132, 0xf900012a#32), -- str x10, [x9]
  (136, 0xd280000a#32), -- mov x10, #0x0               // =0
  (140, 0xf900052a#32), -- str x10, [x9, #0x8]
  (144, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (148, 0xf94003e9#32), -- ldr x9, [sp]
  (152, 0x910043ff#32), -- add sp, sp, #0x10
  (156, 0xd10043ff#32), -- sub sp, sp, #0x10
  (160, 0xf90003e9#32), -- str x9, [sp]
  (164, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (168, 0x91000009#32), -- add x9, x0, #0x0
  (172, 0x91004129#32), -- add x9, x9, #0x10
  (176, 0xd280000a#32), -- mov x10, #0x0               // =0
  (180, 0xf900012a#32), -- str x10, [x9]
  (184, 0xd280000a#32), -- mov x10, #0x0               // =0
  (188, 0xf900052a#32), -- str x10, [x9, #0x8]
  (192, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (196, 0xf94003e9#32), -- ldr x9, [sp]
  (200, 0x910043ff#32), -- add sp, sp, #0x10
  (204, 0xf9001004#32), -- str x4, [x0, #0x20]
  (208, 0xb9004808#32), -- str w8, [x0, #0x48]
  (212, 0xa9002409#32), -- stp x9, x9, [x0]
  (216, 0x1400003f#32), -- b 0x2378e4 <.LBB102_10>
  (220, 0xb40004e4#32), -- cbz x4, 0x237888 <.LBB102_9>
  (224, 0xaa0003f3#32), -- mov x19, x0
  (228, 0xaa0103e0#32), -- mov x0, x1
  (232, 0xaa0203f8#32), -- mov x24, x2
  (236, 0xaa0303f6#32), -- mov x22, x3
  (240, 0xaa0503f4#32), -- mov x20, x5
  (244, 0xaa0403f5#32), -- mov x21, x4
  (248, 0xaa0103f7#32), -- mov x23, x1
  (252, 0x97ffe619#32) -- bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0xd10043ff#32), -- sub sp, sp, #0x10
  (260, 0xf90003e9#32), -- str x9, [sp]
  (264, 0x12000009#32), -- and w9, w0, #0x1
  (268, 0x34000089#32), -- cbz w9, 0x23782c <.Llower_arm_729>
  (272, 0xf94003e9#32), -- ldr x9, [sp]
  (276, 0x910043ff#32), -- add sp, sp, #0x10
  (280, 0x14000004#32), -- b 0x237838 <.Llower_arm_730>
  (284, 0xf94003e9#32), -- ldr x9, [sp]
  (288, 0x910043ff#32), -- add sp, sp, #0x10
  (292, 0x14000034#32), -- b 0x237904 <.LBB102_11>
  (296, 0x910023e0#32), -- add x0, sp, #0x8
  (300, 0xaa1703e1#32), -- mov x1, x23
  (304, 0xaa1403e2#32), -- mov x2, x20
  (308, 0x910023fd#32), -- add x29, sp, #0x8
  (312, 0x97fffca3#32), -- bl 0x236ad4 <_ZN13ssz_fv_native6schema13measure_fixed17hd34cfd77f8373849E>
  (316, 0xa940eff9#32), -- ldp x25, x27, [sp, #0x8]
  (320, 0xb9404bfc#32), -- ldr w28, [sp, #0x48]
  (324, 0xf9400ffa#32), -- ldr x26, [sp, #0x18]
  (328, 0x3400125c#32), -- cbz w28, 0x237aa0 <.LBB102_16>
  (332, 0x91008260#32), -- add x0, x19, #0x20
  (336, 0x910063a1#32), -- add x1, x29, #0x18
  (340, 0x52800502#32), -- mov w2, #0x28               // =40
  (344, 0x9400571a#32), -- bl 0x24d4d0 <memcpy>
  (348, 0xb9404fe8#32), -- ldr w8, [sp, #0x4c]
  (352, 0xa9016a7b#32), -- stp x27, x26, [x19, #0x10]
  (356, 0xf9000679#32), -- str x25, [x19, #0x8]
  (360, 0x2909227c#32), -- stp w28, w8, [x19, #0x48]
  (364, 0x52800028#32), -- mov w8, #0x1                // =1
  (368, 0xf9000268#32), -- str x8, [x19]
  (372, 0x14000018#32), -- b 0x2378e4 <.LBB102_10>
  (376, 0x52800088#32), -- mov w8, #0x4                // =4
  (380, 0x52800209#32), -- mov w9, #0x10               // =16
  (384, 0xd10043ff#32), -- sub sp, sp, #0x10
  (388, 0xf90003e9#32), -- str x9, [sp]
  (392, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (396, 0x91000009#32), -- add x9, x0, #0x0
  (400, 0xd280000a#32), -- mov x10, #0x0               // =0
  (404, 0xf900012a#32), -- str x10, [x9]
  (408, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (412, 0xf94003e9#32), -- ldr x9, [sp]
  (416, 0x910043ff#32), -- add sp, sp, #0x10
  (420, 0x39004008#32), -- strb w8, [x0, #0x10]
  (424, 0xd10043ff#32), -- sub sp, sp, #0x10
  (428, 0xf90003ea#32), -- str x10, [sp]
  (432, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (436, 0x9100000a#32), -- add x10, x0, #0x0
  (440, 0x9100614a#32), -- add x10, x10, #0x18
  (444, 0xf9000149#32), -- str x9, [x10]
  (448, 0xd280000b#32), -- mov x11, #0x0               // =0
  (452, 0xf900054b#32), -- str x11, [x10, #0x8]
  (456, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (460, 0xf94003ea#32), -- ldr x10, [sp]
  (464, 0x910043ff#32), -- add sp, sp, #0x10
  (468, 0xa94b4ff4#32), -- ldp x20, x19, [sp, #0xb0]
  (472, 0xa94a57f6#32), -- ldp x22, x21, [sp, #0xa0]
  (476, 0xa9495ff8#32), -- ldp x24, x23, [sp, #0x90]
  (480, 0xa94867fa#32), -- ldp x26, x25, [sp, #0x80]
  (484, 0xa9476ffc#32), -- ldp x28, x27, [sp, #0x70]
  (488, 0xa9467bfd#32), -- ldp x29, x30, [sp, #0x60]
  (492, 0x910303ff#32), -- add sp, sp, #0xc0
  (496, 0xd65f03c0#32), -- ret
  (500, 0xaa1303e8#32), -- mov x8, x19
  (504, 0xaa1503e9#32), -- mov x9, x21
  (508, 0xf10012bf#32) -- cmp x21, #0x4
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0x54000542#32), -- b.hs 0x2379b8 <.LBB102_14>
  (516, 0x5280008a#32), -- mov w10, #0x4               // =4
  (520, 0xf9001909#32), -- str x9, [x8, #0x30]
  (524, 0x52800029#32), -- mov w9, #0x1                // =1
  (528, 0xd10043ff#32), -- sub sp, sp, #0x10
  (532, 0xf90003e9#32), -- str x9, [sp]
  (536, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (540, 0x91000109#32), -- add x9, x8, #0x0
  (544, 0x9100e129#32), -- add x9, x9, #0x38
  (548, 0xd280000a#32), -- mov x10, #0x0               // =0
  (552, 0xf900012a#32), -- str x10, [x9]
  (556, 0xd280000a#32), -- mov x10, #0x0               // =0
  (560, 0xf900052a#32), -- str x10, [x9, #0x8]
  (564, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (568, 0xf94003e9#32), -- ldr x9, [sp]
  (572, 0x910043ff#32), -- add sp, sp, #0x10
  (576, 0xd10043ff#32), -- sub sp, sp, #0x10
  (580, 0xf90003e9#32), -- str x9, [sp]
  (584, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (588, 0x91000109#32), -- add x9, x8, #0x0
  (592, 0x91004129#32), -- add x9, x9, #0x10
  (596, 0xd280000a#32), -- mov x10, #0x0               // =0
  (600, 0xf900012a#32), -- str x10, [x9]
  (604, 0xd280000a#32), -- mov x10, #0x0               // =0
  (608, 0xf900052a#32), -- str x10, [x9, #0x8]
  (612, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (616, 0xf94003e9#32), -- ldr x9, [sp]
  (620, 0x910043ff#32), -- add sp, sp, #0x10
  (624, 0xd10043ff#32), -- sub sp, sp, #0x10
  (628, 0xf90003e9#32), -- str x9, [sp]
  (632, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (636, 0x91000109#32), -- add x9, x8, #0x0
  (640, 0x91008129#32), -- add x9, x9, #0x20
  (644, 0xf900012a#32), -- str x10, [x9]
  (648, 0xd280000b#32), -- mov x11, #0x0               // =0
  (652, 0xf900052b#32), -- str x11, [x9, #0x8]
  (656, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (660, 0xf94003e9#32), -- ldr x9, [sp]
  (664, 0x910043ff#32), -- add sp, sp, #0x10
  (668, 0xb900490a#32), -- str w10, [x8, #0x48]
  (672, 0xa9002509#32), -- stp x9, x9, [x8]
  (676, 0x17ffffcc#32), -- b 0x2378e4 <.LBB102_10>
  (680, 0x39400acb#32), -- ldrb w11, [x22, #0x2]
  (684, 0x394006cc#32), -- ldrb w12, [x22, #0x1]
  (688, 0x39400ecd#32), -- ldrb w13, [x22, #0x3]
  (692, 0xd370bd6b#32), -- lsl x11, x11, #16
  (696, 0xaa0c216c#32), -- orr x12, x11, x12, lsl #8
  (700, 0x394002cb#32), -- ldrb w11, [x22]
  (704, 0xaa0d618a#32), -- orr x10, x12, x13, lsl #24
  (708, 0xaa0b014a#32), -- orr x10, x10, x11
  (712, 0xf100115f#32), -- cmp x10, #0x4
  (716, 0x54000c02#32), -- b.hs 0x237b5c <.LBB102_27>
  (720, 0xd10043ff#32), -- sub sp, sp, #0x10
  (724, 0xf90003e9#32), -- str x9, [sp]
  (728, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (732, 0x91000109#32), -- add x9, x8, #0x0
  (736, 0x9100e129#32), -- add x9, x9, #0x38
  (740, 0xd280000a#32), -- mov x10, #0x0               // =0
  (744, 0xf900012a#32), -- str x10, [x9]
  (748, 0xd280000a#32), -- mov x10, #0x0               // =0
  (752, 0xf900052a#32), -- str x10, [x9, #0x8]
  (756, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (760, 0xf94003e9#32), -- ldr x9, [sp]
  (764, 0x910043ff#32) -- add sp, sp, #0x10
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0x52800169#32), -- mov w9, #0xb                // =11
  (772, 0xd10043ff#32), -- sub sp, sp, #0x10
  (776, 0xf90003e9#32), -- str x9, [sp]
  (780, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (784, 0x91000109#32), -- add x9, x8, #0x0
  (788, 0x9100a129#32), -- add x9, x9, #0x28
  (792, 0xd280000a#32), -- mov x10, #0x0               // =0
  (796, 0xf900012a#32), -- str x10, [x9]
  (800, 0xd280000a#32), -- mov x10, #0x0               // =0
  (804, 0xf900052a#32), -- str x10, [x9, #0x8]
  (808, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (812, 0xf94003e9#32), -- ldr x9, [sp]
  (816, 0x910043ff#32), -- add sp, sp, #0x10
  (820, 0xd10043ff#32), -- sub sp, sp, #0x10
  (824, 0xf90003e9#32), -- str x9, [sp]
  (828, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (832, 0x91000109#32), -- add x9, x8, #0x0
  (836, 0x91006129#32), -- add x9, x9, #0x18
  (840, 0xd280000a#32), -- mov x10, #0x0               // =0
  (844, 0xf900012a#32), -- str x10, [x9]
  (848, 0xd280000a#32), -- mov x10, #0x0               // =0
  (852, 0xf900052a#32), -- str x10, [x9, #0x8]
  (856, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (860, 0xf94003e9#32), -- ldr x9, [sp]
  (864, 0x910043ff#32), -- add sp, sp, #0x10
  (868, 0xd10043ff#32), -- sub sp, sp, #0x10
  (872, 0xf90003e9#32), -- str x9, [sp]
  (876, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (880, 0x91000109#32), -- add x9, x8, #0x0
  (884, 0x91004129#32), -- add x9, x9, #0x10
  (888, 0xd280000a#32), -- mov x10, #0x0               // =0
  (892, 0xf900012a#32), -- str x10, [x9]
  (896, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (900, 0xf94003e9#32), -- ldr x9, [sp]
  (904, 0x910043ff#32), -- add sp, sp, #0x10
  (908, 0x1400016c#32), -- b 0x23804c <.LBB102_48>
  (912, 0xaa1303e8#32), -- mov x8, x19
  (916, 0xd10043ff#32), -- sub sp, sp, #0x10
  (920, 0xf90003e9#32), -- str x9, [sp]
  (924, 0x12000329#32), -- and w9, w25, #0x1
  (928, 0x34000089#32), -- cbz w9, 0x237ac0 <.Llower_arm_731>
  (932, 0xf94003e9#32), -- ldr x9, [sp]
  (936, 0x910043ff#32), -- add sp, sp, #0x10
  (940, 0x14000004#32), -- b 0x237acc <.Llower_arm_732>
  (944, 0xf94003e9#32), -- ldr x9, [sp]
  (948, 0x910043ff#32), -- add sp, sp, #0x10
  (952, 0x17ffff90#32), -- b 0x237908 <.LBB102_12>
  (956, 0xaa1503e9#32), -- mov x9, x21
  (960, 0xb40010fb#32), -- cbz x27, 0x237cec <.LBB102_31>
  (964, 0xaa1a03ea#32), -- mov x10, x26
  (968, 0xb400114a#32), -- cbz x10, 0x237d00 <.LBB102_34>
  (972, 0x8b0a0f6b#32), -- add x11, x27, x10, lsl #3
  (976, 0xd100054a#32), -- sub x10, x10, #0x1
  (980, 0xd10043ff#32), -- sub sp, sp, #0x10
  (984, 0xf90003e9#32), -- str x9, [sp]
  (988, 0x91000169#32), -- add x9, x11, #0x0
  (992, 0xd1002129#32), -- sub x9, x9, #0x8
  (996, 0xf940012b#32), -- ldr x11, [x9]
  (1000, 0xf94003e9#32), -- ldr x9, [sp]
  (1004, 0x910043ff#32), -- add sp, sp, #0x10
  (1008, 0xb4fffecb#32), -- cbz x11, 0x237ad8 <.LBB102_19>
  (1012, 0xd100074b#32), -- sub x11, x26, #0x1
  (1016, 0xb100057f#32), -- cmn x11, #0x1
  (1020, 0x540001e0#32) -- b.eq 0x237b48 <.LBB102_25>
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk4 : List (Nat × BitVec 32) := [
  (1024, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1028, 0xf90003e9#32), -- str x9, [sp]
  (1032, 0xaa0b03e9#32), -- mov x9, x11
  (1036, 0xd37df129#32), -- lsl x9, x9, #3
  (1040, 0x8b090369#32), -- add x9, x27, x9
  (1044, 0xf940012c#32), -- ldr x12, [x9]
  (1048, 0xf94003e9#32), -- ldr x9, [sp]
  (1052, 0x910043ff#32), -- add sp, sp, #0x10
  (1056, 0xaa0b03ea#32), -- mov x10, x11
  (1060, 0xd100056b#32), -- sub x11, x11, #0x1
  (1064, 0xb4fffe8c#32), -- cbz x12, 0x237b08 <.LBB102_22>
  (1068, 0x9100054a#32), -- add x10, x10, #0x1
  (1072, 0xf100095f#32), -- cmp x10, #0x2
  (1076, 0x54001868#32), -- b.hi 0x237e50 <.LBB102_39>
  (1080, 0xf9400379#32), -- ldr x25, [x27]
  (1084, 0xf1000b5f#32), -- cmp x26, #0x2
  (1088, 0x54001783#32), -- b.lo 0x237e40 <.LBB102_37>
  (1092, 0xf940076a#32), -- ldr x10, [x27, #0x8]
  (1096, 0x140000bb#32), -- b 0x237e44 <.LBB102_38>
  (1100, 0xf240057f#32), -- tst x11, #0x3
  (1104, 0x54000620#32), -- b.eq 0x237c24 <.LBB102_29>
  (1108, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1112, 0xf90003e9#32), -- str x9, [sp]
  (1116, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1120, 0x91000109#32), -- add x9, x8, #0x0
  (1124, 0x9100e129#32), -- add x9, x9, #0x38
  (1128, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1132, 0xf900012a#32), -- str x10, [x9]
  (1136, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1140, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1144, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1148, 0xf94003e9#32), -- ldr x9, [sp]
  (1152, 0x910043ff#32), -- add sp, sp, #0x10
  (1156, 0x52800149#32), -- mov w9, #0xa                // =10
  (1160, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1164, 0xf90003e9#32), -- str x9, [sp]
  (1168, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1172, 0x91000109#32), -- add x9, x8, #0x0
  (1176, 0x9100a129#32), -- add x9, x9, #0x28
  (1180, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1184, 0xf900012a#32), -- str x10, [x9]
  (1188, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1192, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1196, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1200, 0xf94003e9#32), -- ldr x9, [sp]
  (1204, 0x910043ff#32), -- add sp, sp, #0x10
  (1208, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1212, 0xf90003e9#32), -- str x9, [sp]
  (1216, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1220, 0x91000109#32), -- add x9, x8, #0x0
  (1224, 0x91006129#32), -- add x9, x9, #0x18
  (1228, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1232, 0xf900012a#32), -- str x10, [x9]
  (1236, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1240, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1244, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1248, 0xf94003e9#32), -- ldr x9, [sp]
  (1252, 0x910043ff#32), -- add sp, sp, #0x10
  (1256, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1260, 0xf90003e9#32), -- str x9, [sp]
  (1264, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1268, 0x91000109#32), -- add x9, x8, #0x0
  (1272, 0x91004129#32), -- add x9, x9, #0x10
  (1276, 0xd280000a#32) -- mov x10, #0x0               // =0
]

theorem chunk4_decodes :
    chunk4.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk5 : List (Nat × BitVec 32) := [
  (1280, 0xf900012a#32), -- str x10, [x9]
  (1284, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1288, 0xf94003e9#32), -- ldr x9, [sp]
  (1292, 0x910043ff#32), -- add sp, sp, #0x10
  (1296, 0x1400010b#32), -- b 0x23804c <.LBB102_48>
  (1300, 0xeb09015f#32), -- cmp x10, x9
  (1304, 0x54000cc9#32), -- b.ls 0x237dc0 <.LBB102_35>
  (1308, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1312, 0xf90003e9#32), -- str x9, [sp]
  (1316, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1320, 0x91000109#32), -- add x9, x8, #0x0
  (1324, 0x9100e129#32), -- add x9, x9, #0x38
  (1328, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1332, 0xf900012a#32), -- str x10, [x9]
  (1336, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1340, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1344, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1348, 0xf94003e9#32), -- ldr x9, [sp]
  (1352, 0x910043ff#32), -- add sp, sp, #0x10
  (1356, 0x52800129#32), -- mov w9, #0x9                // =9
  (1360, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1364, 0xf90003e9#32), -- str x9, [sp]
  (1368, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1372, 0x91000109#32), -- add x9, x8, #0x0
  (1376, 0x9100a129#32), -- add x9, x9, #0x28
  (1380, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1384, 0xf900012a#32), -- str x10, [x9]
  (1388, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1392, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1396, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1400, 0xf94003e9#32), -- ldr x9, [sp]
  (1404, 0x910043ff#32), -- add sp, sp, #0x10
  (1408, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1412, 0xf90003e9#32), -- str x9, [sp]
  (1416, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1420, 0x91000109#32), -- add x9, x8, #0x0
  (1424, 0x91006129#32), -- add x9, x9, #0x18
  (1428, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1432, 0xf900012a#32), -- str x10, [x9]
  (1436, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1440, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1444, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1448, 0xf94003e9#32), -- ldr x9, [sp]
  (1452, 0x910043ff#32), -- add sp, sp, #0x10
  (1456, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1460, 0xf90003e9#32), -- str x9, [sp]
  (1464, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1468, 0x91000109#32), -- add x9, x8, #0x0
  (1472, 0x91004129#32), -- add x9, x9, #0x10
  (1476, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1480, 0xf900012a#32), -- str x10, [x9]
  (1484, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1488, 0xf94003e9#32), -- ldr x9, [sp]
  (1492, 0x910043ff#32), -- add sp, sp, #0x10
  (1496, 0x140000d9#32), -- b 0x23804c <.LBB102_48>
  (1500, 0xb40000ba#32), -- cbz x26, 0x237d00 <.LBB102_34>
  (1504, 0xeb09035f#32), -- cmp x26, x9
  (1508, 0x54000ae8#32), -- b.hi 0x237e50 <.LBB102_39>
  (1512, 0xaa1a03f9#32), -- mov x25, x26
  (1516, 0x1400007e#32), -- b 0x237ef4 <.LBB102_45>
  (1520, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1524, 0xf90003e9#32), -- str x9, [sp]
  (1528, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1532, 0x91000109#32) -- add x9, x8, #0x0
]

theorem chunk5_decodes :
    chunk5.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk6 : List (Nat × BitVec 32) := [
  (1536, 0x9100e129#32), -- add x9, x9, #0x38
  (1540, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1544, 0xf900012a#32), -- str x10, [x9]
  (1548, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1552, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1556, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1560, 0xf94003e9#32), -- ldr x9, [sp]
  (1564, 0x910043ff#32), -- add sp, sp, #0x10
  (1568, 0x528000c9#32), -- mov w9, #0x6                // =6
  (1572, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1576, 0xf90003e9#32), -- str x9, [sp]
  (1580, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1584, 0x91000109#32), -- add x9, x8, #0x0
  (1588, 0x9100a129#32), -- add x9, x9, #0x28
  (1592, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1596, 0xf900012a#32), -- str x10, [x9]
  (1600, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1604, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1608, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1612, 0xf94003e9#32), -- ldr x9, [sp]
  (1616, 0x910043ff#32), -- add sp, sp, #0x10
  (1620, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1624, 0xf90003e9#32), -- str x9, [sp]
  (1628, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1632, 0x91000109#32), -- add x9, x8, #0x0
  (1636, 0x91006129#32), -- add x9, x9, #0x18
  (1640, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1644, 0xf900012a#32), -- str x10, [x9]
  (1648, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1652, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1656, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1660, 0xf94003e9#32), -- ldr x9, [sp]
  (1664, 0x910043ff#32), -- add sp, sp, #0x10
  (1668, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1672, 0xf90003e9#32), -- str x9, [sp]
  (1676, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1680, 0x91000109#32), -- add x9, x8, #0x0
  (1684, 0x91004129#32), -- add x9, x9, #0x10
  (1688, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1692, 0xf900012a#32), -- str x10, [x9]
  (1696, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1700, 0xf94003e9#32), -- ldr x9, [sp]
  (1704, 0x910043ff#32), -- add sp, sp, #0x10
  (1708, 0x140000a4#32), -- b 0x23804c <.LBB102_48>
  (1712, 0xd342fd59#32), -- lsr x25, x10, #2
  (1716, 0x910023e0#32), -- add x0, sp, #0x8
  (1720, 0x910143e2#32), -- add x2, sp, #0x50
  (1724, 0xaa1803e1#32), -- mov x1, x24
  (1728, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1732, 0xf90003e9#32), -- str x9, [sp]
  (1736, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1740, 0x910043e9#32), -- add x9, sp, #0x10
  (1744, 0x91014129#32), -- add x9, x9, #0x50
  (1748, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1752, 0xf900012a#32), -- str x10, [x9]
  (1756, 0xf9000539#32), -- str x25, [x9, #0x8]
  (1760, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1764, 0xf94003e9#32), -- ldr x9, [sp]
  (1768, 0x910043ff#32), -- add sp, sp, #0x10
  (1772, 0x94000238#32), -- bl 0x2386dc <_ZN13ssz_fv_native5codec7bounded17haa64e3a0177cad3fE>
  (1776, 0xb9404be8#32), -- ldr w8, [sp, #0x48]
  (1780, 0x350014e8#32), -- cbnz w8, 0x2380a0 <.LBB102_50>
  (1784, 0xaa1303e0#32), -- mov x0, x19
  (1788, 0xaa1703e1#32) -- mov x1, x23
]

theorem chunk6_decodes :
    chunk6.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk7 : List (Nat × BitVec 32) := [
  (1792, 0xaa1903e2#32), -- mov x2, x25
  (1796, 0xaa1603e3#32), -- mov x3, x22
  (1800, 0xaa1503e4#32), -- mov x4, x21
  (1804, 0xaa1403e5#32), -- mov x5, x20
  (1808, 0xa94b4ff4#32), -- ldp x20, x19, [sp, #0xb0]
  (1812, 0xa94a57f6#32), -- ldp x22, x21, [sp, #0xa0]
  (1816, 0xa9495ff8#32), -- ldp x24, x23, [sp, #0x90]
  (1820, 0xa94867fa#32), -- ldp x26, x25, [sp, #0x80]
  (1824, 0xa9476ffc#32), -- ldp x28, x27, [sp, #0x70]
  (1828, 0xa9467bfd#32), -- ldp x29, x30, [sp, #0x60]
  (1832, 0x910303ff#32), -- add sp, sp, #0xc0
  (1836, 0x17fffcbc#32), -- b 0x23712c <_ZN13ssz_fv_native5codec14decode_offsets17h3986df5c439cd32dE>
  (1840, 0xaa1f03ea#32), -- mov x10, xzr
  (1844, 0xeb19013f#32), -- cmp x9, x25
  (1848, 0xfa0a03ff#32), -- ngcs xzr, x10
  (1852, 0x54000382#32), -- b.hs 0x237ebc <.LBB102_40>
  (1856, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1860, 0xf90003e9#32), -- str x9, [sp]
  (1864, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1868, 0x91000109#32), -- add x9, x8, #0x0
  (1872, 0x9100e129#32), -- add x9, x9, #0x38
  (1876, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1880, 0xf900012a#32), -- str x10, [x9]
  (1884, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1888, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1892, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1896, 0xf94003e9#32), -- ldr x9, [sp]
  (1900, 0x910043ff#32), -- add sp, sp, #0x10
  (1904, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1908, 0xf90003e9#32), -- str x9, [sp]
  (1912, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1916, 0x91000109#32), -- add x9, x8, #0x0
  (1920, 0x91004129#32), -- add x9, x9, #0x10
  (1924, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1928, 0xf900012a#32), -- str x10, [x9]
  (1932, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1936, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1940, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1944, 0xf94003e9#32), -- ldr x9, [sp]
  (1948, 0x910043ff#32), -- add sp, sp, #0x10
  (1952, 0xa9026d09#32), -- stp x9, x27, [x8, #0x20]
  (1956, 0xf900191a#32), -- str x26, [x8, #0x30]
  (1960, 0x14000064#32), -- b 0x238048 <.LBB102_47>
  (1964, 0xd100236a#32), -- sub x10, x27, #0x8
  (1968, 0xb400019a#32), -- cbz x26, 0x237ef0 <.LBB102_44>
  (1972, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1976, 0xf90003e9#32), -- str x9, [sp]
  (1980, 0xaa1a03e9#32), -- mov x9, x26
  (1984, 0xd37df129#32), -- lsl x9, x9, #3
  (1988, 0x8b090149#32), -- add x9, x10, x9
  (1992, 0xf940012b#32), -- ldr x11, [x9]
  (1996, 0xf94003e9#32), -- ldr x9, [sp]
  (2000, 0x910043ff#32), -- add sp, sp, #0x10
  (2004, 0xf100075a#32), -- subs x26, x26, #0x1
  (2008, 0xb4fffecb#32), -- cbz x11, 0x237ec0 <.LBB102_41>
  (2012, 0x54001021#32), -- b.ne 0x2380f0 <.LBB102_52>
  (2016, 0xb4001619#32), -- cbz x25, 0x2381b0 <.LBB102_53>
  (2020, 0xd10103ff#32), -- sub sp, sp, #0x40
  (2024, 0xf90003ea#32), -- str x10, [sp]
  (2028, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (2032, 0xf9000bec#32), -- str x12, [sp, #0x10]
  (2036, 0xf9000fed#32), -- str x13, [sp, #0x18]
  (2040, 0xf90013ee#32), -- str x14, [sp, #0x20]
  (2044, 0xf90017ef#32) -- str x15, [sp, #0x28]
]

theorem chunk7_decodes :
    chunk7.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk8 : List (Nat × BitVec 32) := [
  (2048, 0xf9001bf0#32), -- str x16, [sp, #0x30]
  (2052, 0xf9001ff1#32), -- str x17, [sp, #0x38]
  (2056, 0xaa0903ea#32), -- mov x10, x9
  (2060, 0xaa1903eb#32), -- mov x11, x25
  (2064, 0xd280000d#32), -- mov x13, #0x0               // =0
  (2068, 0xb400028b#32), -- cbz x11, 0x237f74 <.Llower_arm_736>
  (2072, 0xd280000c#32), -- mov x12, #0x0               // =0
  (2076, 0xd2800811#32), -- mov x17, #0x40              // =64
  (2080, 0xd37ffd90#32), -- lsr x16, x12, #63
  (2084, 0xd37ff98c#32), -- lsl x12, x12, #1
  (2088, 0xaa4afd8c#32), -- orr x12, x12, x10, lsr #63
  (2092, 0xd37ff94a#32), -- lsl x10, x10, #1
  (2096, 0xd37ff9ad#32), -- lsl x13, x13, #1
  (2100, 0xcb0b018e#32), -- sub x14, x12, x11
  (2104, 0xb50000f0#32), -- cbnz x16, 0x237f64 <.Llower_arm_734>
  (2108, 0x8a2c016f#32), -- bic x15, x11, x12
  (2112, 0xca0b0190#32), -- eor x16, x12, x11
  (2116, 0x8a3001d0#32), -- bic x16, x14, x16
  (2120, 0xaa1001ef#32), -- orr x15, x15, x16
  (2124, 0xd37ffdef#32), -- lsr x15, x15, #63
  (2128, 0xb500006f#32), -- cbnz x15, 0x237f6c <.Llower_arm_735>
  (2132, 0xaa0e03ec#32), -- mov x12, x14
  (2136, 0xb24001ad#32), -- orr x13, x13, #0x1
  (2140, 0xd1000631#32), -- sub x17, x17, #0x1
  (2144, 0xb5fffe11#32), -- cbnz x17, 0x237f30 <.Llower_arm_733>
  (2148, 0xaa0d03fa#32), -- mov x26, x13
  (2152, 0xf9401ff1#32), -- ldr x17, [sp, #0x38]
  (2156, 0xf9401bf0#32), -- ldr x16, [sp, #0x30]
  (2160, 0xf94017ef#32), -- ldr x15, [sp, #0x28]
  (2164, 0xf94013ee#32), -- ldr x14, [sp, #0x20]
  (2168, 0xf9400fed#32), -- ldr x13, [sp, #0x18]
  (2172, 0xf9400bec#32), -- ldr x12, [sp, #0x10]
  (2176, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (2180, 0xf94003ea#32), -- ldr x10, [sp]
  (2184, 0x910103ff#32), -- add sp, sp, #0x40
  (2188, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2192, 0xf90003eb#32), -- str x11, [sp]
  (2196, 0x9b197f4b#32), -- mul x11, x26, x25
  (2200, 0xcb0b012a#32), -- sub x10, x9, x11
  (2204, 0xf94003eb#32), -- ldr x11, [sp]
  (2208, 0x910043ff#32), -- add sp, sp, #0x10
  (2212, 0xb400054a#32), -- cbz x10, 0x23805c <.LBB102_49>
  (2216, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2220, 0xf90003e9#32), -- str x9, [sp]
  (2224, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2228, 0x91000109#32), -- add x9, x8, #0x0
  (2232, 0x9100e129#32), -- add x9, x9, #0x38
  (2236, 0xd280000a#32), -- mov x10, #0x0               // =0
  (2240, 0xf900012a#32), -- str x10, [x9]
  (2244, 0xd280000a#32), -- mov x10, #0x0               // =0
  (2248, 0xf900052a#32), -- str x10, [x9, #0x8]
  (2252, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (2256, 0xf94003e9#32), -- ldr x9, [sp]
  (2260, 0x910043ff#32), -- add sp, sp, #0x10
  (2264, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2268, 0xf90003e9#32), -- str x9, [sp]
  (2272, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2276, 0x91000109#32), -- add x9, x8, #0x0
  (2280, 0x91004129#32), -- add x9, x9, #0x10
  (2284, 0xd280000a#32), -- mov x10, #0x0               // =0
  (2288, 0xf900012a#32), -- str x10, [x9]
  (2292, 0xd280000a#32), -- mov x10, #0x0               // =0
  (2296, 0xf900052a#32), -- str x10, [x9, #0x8]
  (2300, 0xf94007ea#32) -- ldr x10, [sp, #0x8]
]

theorem chunk8_decodes :
    chunk8.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk9 : List (Nat × BitVec 32) := [
  (2304, 0xf94003e9#32), -- ldr x9, [sp]
  (2308, 0x910043ff#32), -- add sp, sp, #0x10
  (2312, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2316, 0xf90003ea#32), -- str x10, [sp]
  (2320, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (2324, 0x9100010a#32), -- add x10, x8, #0x0
  (2328, 0x9100814a#32), -- add x10, x10, #0x20
  (2332, 0xf9000149#32), -- str x9, [x10]
  (2336, 0xd280000b#32), -- mov x11, #0x0               // =0
  (2340, 0xf900054b#32), -- str x11, [x10, #0x8]
  (2344, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (2348, 0xf94003ea#32), -- ldr x10, [sp]
  (2352, 0x910043ff#32), -- add sp, sp, #0x10
  (2356, 0xf9001919#32), -- str x25, [x8, #0x30]
  (2360, 0x528000a9#32), -- mov w9, #0x5                // =5
  (2364, 0x5280002a#32), -- mov w10, #0x1               // =1
  (2368, 0xb9004909#32), -- str w9, [x8, #0x48]
  (2372, 0xa900290a#32), -- stp x10, x10, [x8]
  (2376, 0x17fffe23#32), -- b 0x2378e4 <.LBB102_10>
  (2380, 0x910023e0#32), -- add x0, sp, #0x8
  (2384, 0x910143e2#32), -- add x2, sp, #0x50
  (2388, 0xaa1803e1#32), -- mov x1, x24
  (2392, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2396, 0xf90003e9#32), -- str x9, [sp]
  (2400, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2404, 0x910043e9#32), -- add x9, sp, #0x10
  (2408, 0x91014129#32), -- add x9, x9, #0x50
  (2412, 0xd280000a#32), -- mov x10, #0x0               // =0
  (2416, 0xf900012a#32), -- str x10, [x9]
  (2420, 0xf900053a#32), -- str x26, [x9, #0x8]
  (2424, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (2428, 0xf94003e9#32), -- ldr x9, [sp]
  (2432, 0x910043ff#32), -- add sp, sp, #0x10
  (2436, 0x94000192#32), -- bl 0x2386dc <_ZN13ssz_fv_native5codec7bounded17haa64e3a0177cad3fE>
  (2440, 0xb9404be8#32), -- ldr w8, [sp, #0x48]
  (2444, 0x340000c8#32), -- cbz w8, 0x2380b4 <.LBB102_51>
  (2448, 0x91002260#32), -- add x0, x19, #0x8
  (2452, 0x910023e1#32), -- add x1, sp, #0x8
  (2456, 0x52800902#32), -- mov w2, #0x48               // =72
  (2460, 0x94005509#32), -- bl 0x24d4d0 <memcpy>
  (2464, 0x17fffdf3#32), -- b 0x23787c <.LBB102_8>
  (2468, 0xaa1303e0#32), -- mov x0, x19
  (2472, 0xaa1703e1#32), -- mov x1, x23
  (2476, 0xaa1a03e2#32), -- mov x2, x26
  (2480, 0xaa1903e3#32), -- mov x3, x25
  (2484, 0xaa1603e4#32), -- mov x4, x22
  (2488, 0xaa1503e5#32), -- mov x5, x21
  (2492, 0xaa1403e6#32), -- mov x6, x20
  (2496, 0xa94b4ff4#32), -- ldp x20, x19, [sp, #0xb0]
  (2500, 0xa94a57f6#32), -- ldp x22, x21, [sp, #0xa0]
  (2504, 0xa9495ff8#32), -- ldp x24, x23, [sp, #0x90]
  (2508, 0xa94867fa#32), -- ldp x26, x25, [sp, #0x80]
  (2512, 0xa9476ffc#32), -- ldp x28, x27, [sp, #0x70]
  (2516, 0xa9467bfd#32), -- ldp x29, x30, [sp, #0x60]
  (2520, 0x910303ff#32), -- add sp, sp, #0xc0
  (2524, 0x17fffb49#32), -- b 0x236e10 <_ZN13ssz_fv_native5codec12decode_fixed17hd268ce61b5ac9b5fE>
  (2528, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2532, 0xf90003e9#32), -- str x9, [sp]
  (2536, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2540, 0x91000109#32), -- add x9, x8, #0x0
  (2544, 0x9100e129#32), -- add x9, x9, #0x38
  (2548, 0xd280000a#32), -- mov x10, #0x0               // =0
  (2552, 0xf900012a#32), -- str x10, [x9]
  (2556, 0xd280000a#32) -- mov x10, #0x0               // =0
]

theorem chunk9_decodes :
    chunk9.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk10 : List (Nat × BitVec 32) := [
  (2560, 0xf900052a#32), -- str x10, [x9, #0x8]
  (2564, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (2568, 0xf94003e9#32), -- ldr x9, [sp]
  (2572, 0x910043ff#32), -- add sp, sp, #0x10
  (2576, 0x52900049#32), -- mov w9, #0x8002             // =32770
  (2580, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2584, 0xf90003e9#32), -- str x9, [sp]
  (2588, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2592, 0x91000109#32), -- add x9, x8, #0x0
  (2596, 0x9100a129#32), -- add x9, x9, #0x28
  (2600, 0xd280000a#32), -- mov x10, #0x0               // =0
  (2604, 0xf900012a#32), -- str x10, [x9]
  (2608, 0xd280000a#32), -- mov x10, #0x0               // =0
  (2612, 0xf900052a#32), -- str x10, [x9, #0x8]
  (2616, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (2620, 0xf94003e9#32), -- ldr x9, [sp]
  (2624, 0x910043ff#32), -- add sp, sp, #0x10
  (2628, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2632, 0xf90003e9#32), -- str x9, [sp]
  (2636, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2640, 0x91000109#32), -- add x9, x8, #0x0
  (2644, 0x91006129#32), -- add x9, x9, #0x18
  (2648, 0xd280000a#32), -- mov x10, #0x0               // =0
  (2652, 0xf900012a#32), -- str x10, [x9]
  (2656, 0xd280000a#32), -- mov x10, #0x0               // =0
  (2660, 0xf900052a#32), -- str x10, [x9, #0x8]
  (2664, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (2668, 0xf94003e9#32), -- ldr x9, [sp]
  (2672, 0x910043ff#32), -- add sp, sp, #0x10
  (2676, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2680, 0xf90003e9#32), -- str x9, [sp]
  (2684, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2688, 0x91000109#32), -- add x9, x8, #0x0
  (2692, 0x91004129#32), -- add x9, x9, #0x10
  (2696, 0xd280000a#32), -- mov x10, #0x0               // =0
  (2700, 0xf900012a#32), -- str x10, [x9]
  (2704, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (2708, 0xf94003e9#32), -- ldr x9, [sp]
  (2712, 0x910043ff#32), -- add sp, sp, #0x10
  (2716, 0x17ffffa8#32), -- b 0x23804c <.LBB102_48>
  (2720, 0x97ff9933#32) -- bl 0x21e67c <_ZN4core5slice4sort6shared9smallsort22panic_on_ord_violation17h3e94085727ccf329E>
]

theorem chunk10_decodes :
    chunk10.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 ++ chunk8 ++ chunk9 ++ chunk10

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

theorem chunk8_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk8 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append, member, true_or, or_true]

theorem chunk9_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk9 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append, member, true_or, or_true]

theorem chunk10_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk10 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append, member, true_or, or_true]

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, chunk3_decodes, chunk4_decodes, chunk5_decodes, chunk6_decodes, chunk7_decodes, chunk8_decodes, chunk9_decodes, chunk10_decodes, Bool.and_self]

end SszArm.Codec.Linked.DecodeList
