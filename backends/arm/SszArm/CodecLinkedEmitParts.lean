import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.EmitParts

/-- Actual ELF entry address of _ZN13ssz_fv_native5codec10emit_parts17h64cc0a69cd66c152E. -/
def address : Nat := 2296776

def byteSize : Nat := 1192

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10383ff#32), -- sub sp, sp, #0xe0
  (4, 0xa9087bfd#32), -- stp x29, x30, [sp, #0x80]
  (8, 0xa9096ffc#32), -- stp x28, x27, [sp, #0x90]
  (12, 0xa90a67fa#32), -- stp x26, x25, [sp, #0xa0]
  (16, 0xa90b5ff8#32), -- stp x24, x23, [sp, #0xb0]
  (20, 0xa90c57f6#32), -- stp x22, x21, [sp, #0xc0]
  (24, 0xa90d4ff4#32), -- stp x20, x19, [sp, #0xd0]
  (28, 0xaa0203f6#32), -- mov x22, x2
  (32, 0xaa0003fa#32), -- mov x26, x0
  (36, 0xa9029be5#32), -- stp x5, x6, [sp, #0x28]
  (40, 0xb4000ee4#32), -- cbz x4, 0x230dcc <.LBB85_26>
  (44, 0xf9400488#32), -- ldr x8, [x4, #0x8]
  (48, 0xb4000ea8#32), -- cbz x8, 0x230dcc <.LBB85_26>
  (52, 0xf9401094#32), -- ldr x20, [x4, #0x20]
  (56, 0xeb03011f#32), -- cmp x8, x3
  (60, 0xf90003fa#32), -- str x26, [sp]
  (64, 0x9a833108#32), -- csel x8, x8, x3, lo
  (68, 0xf90013e8#32), -- str x8, [sp, #0x20]
  (72, 0xb4001663#32), -- cbz x3, 0x230edc <.LBB85_39>
  (76, 0xf9400089#32), -- ldr x9, [x4]
  (80, 0xf9400035#32), -- ldr x21, [x1]
  (84, 0xaa1f03fa#32), -- mov x26, xzr
  (88, 0x91002021#32), -- add x1, x1, #0x8
  (92, 0xf9400028#32), -- ldr x8, [x1]
  (96, 0xaa1f03f8#32), -- mov x24, xzr
  (100, 0xf9000fe1#32), -- str x1, [sp, #0x18]
  (104, 0xa900a7e8#32), -- stp x8, x9, [sp, #0x8]
  (108, 0x14000006#32), -- b 0x230c4c <.LBB85_5>
  (112, 0xf94013e8#32), -- ldr x8, [sp, #0x20]
  (116, 0x91000718#32), -- add x24, x24, #0x1
  (120, 0xaa1b03fa#32), -- mov x26, x27
  (124, 0xeb08031f#32), -- cmp x24, x8
  (128, 0x540014c0#32), -- b.eq 0x230ee0 <.LBB85_40>
  (132, 0xf9400fe9#32), -- ldr x9, [sp, #0x18]
  (136, 0xb40000f5#32), -- cbz x21, 0x230c6c <.LBB85_8>
  (140, 0xf94007e8#32), -- ldr x8, [sp, #0x8]
  (144, 0xeb08031f#32), -- cmp x24, x8
  (148, 0x54002042#32), -- b.hs 0x231064 <.LBB85_48>
  (152, 0x52800308#32), -- mov w8, #0x18               // =24
  (156, 0x9b085708#32), -- madd x8, x24, x8, x21
  (160, 0x91004109#32), -- add x9, x8, #0x10
  (164, 0x5280050a#32), -- mov w10, #0x28              // =40
  (168, 0xf9400be8#32), -- ldr x8, [sp, #0x10]
  (172, 0xf940013d#32), -- ldr x29, [x9]
  (176, 0x9b0a231c#32), -- madd x28, x24, x10, x8
  (180, 0xa9414f88#32), -- ldp x8, x19, [x28, #0x10]
  (184, 0xb40002a8#32), -- cbz x8, 0x230cd4 <.LBB85_15>
  (188, 0xd100066a#32), -- sub x10, x19, #0x1
  (192, 0xb100055f#32), -- cmn x10, #0x1
  (196, 0x54000200#32), -- b.eq 0x230ccc <.LBB85_13>
  (200, 0xd10043ff#32), -- sub sp, sp, #0x10
  (204, 0xf90003e9#32), -- str x9, [sp]
  (208, 0xaa0a03e9#32), -- mov x9, x10
  (212, 0xd37df129#32), -- lsl x9, x9, #3
  (216, 0x8b090109#32), -- add x9, x8, x9
  (220, 0xf940012b#32), -- ldr x11, [x9]
  (224, 0xf94003e9#32), -- ldr x9, [sp]
  (228, 0x910043ff#32), -- add sp, sp, #0x10
  (232, 0xaa0a03e9#32), -- mov x9, x10
  (236, 0xd100054a#32), -- sub x10, x10, #0x1
  (240, 0xb4fffe8b#32), -- cbz x11, 0x230c88 <.LBB85_10>
  (244, 0x91000529#32), -- add x9, x9, #0x1
  (248, 0xf100053f#32), -- cmp x9, #0x1
  (252, 0x54000060#32) -- b.eq 0x230cd0 <.LBB85_14>
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0x1400009e#32), -- b 0x230f40 <.LBB85_42>
  (260, 0xb4000053#32), -- cbz x19, 0x230cd4 <.LBB85_15>
  (264, 0xf9400113#32), -- ldr x19, [x8]
  (268, 0x52800608#32), -- mov w8, #0x30               // =48
  (272, 0x9b085b17#32), -- madd x23, x24, x8, x22
  (276, 0xb40003d5#32), -- cbz x21, 0x230d54 <.LBB85_21>
  (280, 0xaa1d03e0#32), -- mov x0, x29
  (284, 0x940000e3#32), -- bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>
  (288, 0xd10043ff#32), -- sub sp, sp, #0x10
  (292, 0xf90003e9#32), -- str x9, [sp]
  (296, 0x12000009#32), -- and w9, w0, #0x1
  (300, 0x34000089#32), -- cbz w9, 0x230d04 <.Llower_arm_635>
  (304, 0xf94003e9#32), -- ldr x9, [sp]
  (308, 0x910043ff#32), -- add sp, sp, #0x10
  (312, 0x14000004#32), -- b 0x230d10 <.Llower_arm_636>
  (316, 0xf94003e9#32), -- ldr x9, [sp]
  (320, 0x910043ff#32), -- add sp, sp, #0x10
  (324, 0x14000012#32), -- b 0x230d54 <.LBB85_21>
  (328, 0xab1a027b#32), -- adds x27, x19, x26
  (332, 0x540019a2#32), -- b.hs 0x231048 <.LBB85_46>
  (336, 0xf9401be8#32), -- ldr x8, [sp, #0x30]
  (340, 0xeb08037f#32), -- cmp x27, x8
  (344, 0x54001948#32), -- b.hi 0x231048 <.LBB85_46>
  (348, 0xf94017e8#32), -- ldr x8, [sp, #0x28]
  (352, 0x9100e3e0#32), -- add x0, sp, #0x38
  (356, 0xaa1d03e1#32), -- mov x1, x29
  (360, 0xaa1703e2#32), -- mov x2, x23
  (364, 0xaa1c03e3#32), -- mov x3, x28
  (368, 0xaa1303e5#32), -- mov x5, x19
  (372, 0x8b1a0104#32), -- add x4, x8, x26
  (376, 0x97fffdaf#32), -- bl 0x2303fc <_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE>
  (380, 0xb9407bf3#32), -- ldr w19, [sp, #0x78]
  (384, 0x35000e73#32), -- cbnz w19, 0x230f14 <.LBB85_41>
  (388, 0xaa1403f9#32), -- mov x25, x20
  (392, 0x17ffffba#32), -- b 0x230c38 <.LBB85_4>
  (396, 0xf9401be8#32), -- ldr x8, [sp, #0x30]
  (400, 0x9100135b#32), -- add x27, x26, #0x4
  (404, 0xeb08037f#32), -- cmp x27, x8
  (408, 0x54001748#32), -- b.hi 0x231048 <.LBB85_46>
  (412, 0xf94017e8#32), -- ldr x8, [sp, #0x28]
  (416, 0xd358fe89#32), -- lsr x9, x20, #24
  (420, 0xd350fe8a#32), -- lsr x10, x20, #16
  (424, 0xd348fe8b#32), -- lsr x11, x20, #8
  (428, 0xab140279#32), -- adds x25, x19, x20
  (432, 0x8b1a0108#32), -- add x8, x8, x26
  (436, 0x39000114#32), -- strb w20, [x8]
  (440, 0x39000d09#32), -- strb w9, [x8, #0x3]
  (444, 0x3900090a#32), -- strb w10, [x8, #0x2]
  (448, 0x3900050b#32), -- strb w11, [x8, #0x1]
  (452, 0x54001562#32), -- b.hs 0x231038 <.LBB85_45>
  (456, 0xf9401be8#32), -- ldr x8, [sp, #0x30]
  (460, 0xeb08033f#32), -- cmp x25, x8
  (464, 0x54001508#32), -- b.hi 0x231038 <.LBB85_45>
  (468, 0xf94017e8#32), -- ldr x8, [sp, #0x28]
  (472, 0x9100e3e0#32), -- add x0, sp, #0x38
  (476, 0xaa1d03e1#32), -- mov x1, x29
  (480, 0xaa1703e2#32), -- mov x2, x23
  (484, 0xaa1c03e3#32), -- mov x3, x28
  (488, 0xaa1303e5#32), -- mov x5, x19
  (492, 0x8b140104#32), -- add x4, x8, x20
  (496, 0x97fffd91#32), -- bl 0x2303fc <_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE>
  (500, 0xb9407bf3#32), -- ldr w19, [sp, #0x78]
  (504, 0x35000ab3#32), -- cbnz w19, 0x230f14 <.LBB85_41>
  (508, 0xaa1903f4#32) -- mov x20, x25
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0x17ffff9c#32), -- b 0x230c38 <.LBB85_4>
  (516, 0xb40006e3#32), -- cbz x3, 0x230ea8 <.LBB85_37>
  (520, 0x8b030469#32), -- add x9, x3, x3, lsl #1
  (524, 0xa9405c28#32), -- ldp x8, x23, [x1]
  (528, 0xaa1f03f8#32), -- mov x24, xzr
  (532, 0xd37ced33#32), -- lsl x19, x9, #4
  (536, 0xb4000388#32), -- cbz x8, 0x230e50 <.LBB85_34>
  (540, 0x91004114#32), -- add x20, x8, #0x10
  (544, 0x910006f5#32), -- add x21, x23, #0x1
  (548, 0xf10006b5#32), -- subs x21, x21, #0x1
  (552, 0x54001340#32), -- b.eq 0x231058 <.LBB85_47>
  (556, 0xf9401be8#32), -- ldr x8, [sp, #0x30]
  (560, 0xeb180105#32), -- subs x5, x8, x24
  (564, 0x54001163#32), -- b.lo 0x231028 <.LBB85_44>
  (568, 0xf94017e8#32), -- ldr x8, [sp, #0x28]
  (572, 0xf8418681#32), -- ldr x1, [x20], #0x18
  (576, 0x9100e3e0#32), -- add x0, sp, #0x38
  (580, 0xaa1603e2#32), -- mov x2, x22
  (584, 0xaa1f03e3#32), -- mov x3, xzr
  (588, 0x8b180104#32), -- add x4, x8, x24
  (592, 0x97fffd79#32), -- bl 0x2303fc <_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE>
  (596, 0xb9407bf9#32), -- ldr w25, [sp, #0x78]
  (600, 0x35000319#32), -- cbnz w25, 0x230e80 <.LBB85_36>
  (604, 0xf9401fe8#32), -- ldr x8, [sp, #0x38]
  (608, 0xd100c273#32), -- sub x19, x19, #0x30
  (612, 0x9100c2d6#32), -- add x22, x22, #0x30
  (616, 0x8b180118#32), -- add x24, x8, x24
  (620, 0xb5fffdd3#32), -- cbnz x19, 0x230dec <.LBB85_29>
  (624, 0x1400001d#32), -- b 0x230eac <.LBB85_38>
  (628, 0xf9401fe8#32), -- ldr x8, [sp, #0x38]
  (632, 0xf100c273#32), -- subs x19, x19, #0x30
  (636, 0x9100c2d6#32), -- add x22, x22, #0x30
  (640, 0x8b180118#32), -- add x24, x8, x24
  (644, 0x54000300#32), -- b.eq 0x230eac <.LBB85_38>
  (648, 0xf9401be8#32), -- ldr x8, [sp, #0x30]
  (652, 0xeb180105#32), -- subs x5, x8, x24
  (656, 0x54000e83#32), -- b.lo 0x231028 <.LBB85_44>
  (660, 0xf94017e8#32), -- ldr x8, [sp, #0x28]
  (664, 0x9100e3e0#32), -- add x0, sp, #0x38
  (668, 0xaa1703e1#32), -- mov x1, x23
  (672, 0xaa1603e2#32), -- mov x2, x22
  (676, 0xaa1f03e3#32), -- mov x3, xzr
  (680, 0x8b180104#32), -- add x4, x8, x24
  (684, 0x97fffd62#32), -- bl 0x2303fc <_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE>
  (688, 0xb9407bf9#32), -- ldr w25, [sp, #0x78]
  (692, 0x34fffe19#32), -- cbz w25, 0x230e3c <.LBB85_33>
  (696, 0x9100e3e8#32), -- add x8, sp, #0x38
  (700, 0xf9401ff3#32), -- ldr x19, [sp, #0x38]
  (704, 0x91002340#32), -- add x0, x26, #0x8
  (708, 0x91002101#32), -- add x1, x8, #0x8
  (712, 0x52800702#32), -- mov w2, #0x38               // =56
  (716, 0x9400718f#32), -- bl 0x24d4d0 <memcpy>
  (720, 0xb9407fe8#32), -- ldr w8, [sp, #0x7c]
  (724, 0xf9000353#32), -- str x19, [x26]
  (728, 0x29082359#32), -- stp w25, w8, [x26, #0x40]
  (732, 0x14000059#32), -- b 0x231008 <.LBB85_43>
  (736, 0xaa1f03f8#32), -- mov x24, xzr
  (740, 0xf9000358#32), -- str x24, [x26]
  (744, 0xd10043ff#32), -- sub sp, sp, #0x10
  (748, 0xf90003e9#32), -- str x9, [sp]
  (752, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (756, 0x91000349#32), -- add x9, x26, #0x0
  (760, 0x91010129#32), -- add x9, x9, #0x40
  (764, 0x5280000a#32) -- mov w10, #0x0               // =0
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0xb900012a#32), -- str w10, [x9]
  (772, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (776, 0xf94003e9#32), -- ldr x9, [sp]
  (780, 0x910043ff#32), -- add sp, sp, #0x10
  (784, 0x1400004c#32), -- b 0x231008 <.LBB85_43>
  (788, 0xaa1403f9#32), -- mov x25, x20
  (792, 0xf94003e8#32), -- ldr x8, [sp]
  (796, 0xf9000119#32), -- str x25, [x8]
  (800, 0xd10043ff#32), -- sub sp, sp, #0x10
  (804, 0xf90003e9#32), -- str x9, [sp]
  (808, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (812, 0x91000109#32), -- add x9, x8, #0x0
  (816, 0x91010129#32), -- add x9, x9, #0x40
  (820, 0x5280000a#32), -- mov w10, #0x0               // =0
  (824, 0xb900012a#32), -- str w10, [x9]
  (828, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (832, 0xf94003e9#32), -- ldr x9, [sp]
  (836, 0x910043ff#32), -- add sp, sp, #0x10
  (840, 0x1400003e#32), -- b 0x231008 <.LBB85_43>
  (844, 0xf94003f5#32), -- ldr x21, [sp]
  (848, 0x9100e3e8#32), -- add x8, sp, #0x38
  (852, 0xf9401ff4#32), -- ldr x20, [sp, #0x38]
  (856, 0x91002101#32), -- add x1, x8, #0x8
  (860, 0x52800702#32), -- mov w2, #0x38               // =56
  (864, 0x910022a0#32), -- add x0, x21, #0x8
  (868, 0x94007169#32), -- bl 0x24d4d0 <memcpy>
  (872, 0xb9407fe8#32), -- ldr w8, [sp, #0x7c]
  (876, 0xf90002b4#32), -- str x20, [x21]
  (880, 0x290822b3#32), -- stp w19, w8, [x21, #0x40]
  (884, 0x14000033#32), -- b 0x231008 <.LBB85_43>
  (888, 0xf94003e9#32), -- ldr x9, [sp]
  (892, 0x52800028#32), -- mov w8, #0x1                // =1
  (896, 0xd10043ff#32), -- sub sp, sp, #0x10
  (900, 0xf90003ea#32), -- str x10, [sp]
  (904, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (908, 0x9100012a#32), -- add x10, x9, #0x0
  (912, 0xf9000148#32), -- str x8, [x10]
  (916, 0xd280000b#32), -- mov x11, #0x0               // =0
  (920, 0xf900054b#32), -- str x11, [x10, #0x8]
  (924, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (928, 0xf94003ea#32), -- ldr x10, [sp]
  (932, 0x910043ff#32), -- add sp, sp, #0x10
  (936, 0x52900028#32), -- mov w8, #0x8001             // =32769
  (940, 0xd10043ff#32), -- sub sp, sp, #0x10
  (944, 0xf90003ea#32), -- str x10, [sp]
  (948, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (952, 0x9100012a#32), -- add x10, x9, #0x0
  (956, 0x9100c14a#32), -- add x10, x10, #0x30
  (960, 0xd280000b#32), -- mov x11, #0x0               // =0
  (964, 0xf900014b#32), -- str x11, [x10]
  (968, 0xd280000b#32), -- mov x11, #0x0               // =0
  (972, 0xf900054b#32), -- str x11, [x10, #0x8]
  (976, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (980, 0xf94003ea#32), -- ldr x10, [sp]
  (984, 0x910043ff#32), -- add sp, sp, #0x10
  (988, 0xd10043ff#32), -- sub sp, sp, #0x10
  (992, 0xf90003ea#32), -- str x10, [sp]
  (996, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (1000, 0x9100012a#32), -- add x10, x9, #0x0
  (1004, 0x9100814a#32), -- add x10, x10, #0x20
  (1008, 0xd280000b#32), -- mov x11, #0x0               // =0
  (1012, 0xf900014b#32), -- str x11, [x10]
  (1016, 0xd280000b#32), -- mov x11, #0x0               // =0
  (1020, 0xf900054b#32) -- str x11, [x10, #0x8]
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk4 : List (Nat × BitVec 32) := [
  (1024, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (1028, 0xf94003ea#32), -- ldr x10, [sp]
  (1032, 0x910043ff#32), -- add sp, sp, #0x10
  (1036, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1040, 0xf90003ea#32), -- str x10, [sp]
  (1044, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (1048, 0x9100012a#32), -- add x10, x9, #0x0
  (1052, 0x9100414a#32), -- add x10, x10, #0x10
  (1056, 0xd280000b#32), -- mov x11, #0x0               // =0
  (1060, 0xf900014b#32), -- str x11, [x10]
  (1064, 0xd280000b#32), -- mov x11, #0x0               // =0
  (1068, 0xf900054b#32), -- str x11, [x10, #0x8]
  (1072, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (1076, 0xf94003ea#32), -- ldr x10, [sp]
  (1080, 0x910043ff#32), -- add sp, sp, #0x10
  (1084, 0xb9004128#32), -- str w8, [x9, #0x40]
  (1088, 0xa94d4ff4#32), -- ldp x20, x19, [sp, #0xd0]
  (1092, 0xa94c57f6#32), -- ldp x22, x21, [sp, #0xc0]
  (1096, 0xa94b5ff8#32), -- ldp x24, x23, [sp, #0xb0]
  (1100, 0xa94a67fa#32), -- ldp x26, x25, [sp, #0xa0]
  (1104, 0xa9496ffc#32), -- ldp x28, x27, [sp, #0x90]
  (1108, 0xa9487bfd#32), -- ldp x29, x30, [sp, #0x80]
  (1112, 0x910383ff#32), -- add sp, sp, #0xe0
  (1116, 0xd65f03c0#32), -- ret
  (1120, 0xf9401be1#32), -- ldr x1, [sp, #0x30]
  (1124, 0xaa1803e0#32), -- mov x0, x24
  (1128, 0xaa0103e2#32), -- mov x2, x1
  (1132, 0x97ffb443#32), -- bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>
  (1136, 0xf9401be2#32), -- ldr x2, [sp, #0x30]
  (1140, 0xaa1403e0#32), -- mov x0, x20
  (1144, 0xaa1903e1#32), -- mov x1, x25
  (1148, 0x97ffb43f#32), -- bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>
  (1152, 0xf9401be2#32), -- ldr x2, [sp, #0x30]
  (1156, 0xaa1a03e0#32), -- mov x0, x26
  (1160, 0xaa1b03e1#32), -- mov x1, x27
  (1164, 0x97ffb43b#32), -- bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>
  (1168, 0xaa1703e0#32), -- mov x0, x23
  (1172, 0xaa1703e1#32), -- mov x1, x23
  (1176, 0x97ffb444#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (1180, 0xf94007e1#32), -- ldr x1, [sp, #0x8]
  (1184, 0xaa1803e0#32), -- mov x0, x24
  (1188, 0x97ffb441#32) -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
]

theorem chunk4_decodes :
    chunk4.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4

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

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, chunk3_decodes, chunk4_decodes, Bool.and_self]

end SszArm.Codec.Linked.EmitParts
