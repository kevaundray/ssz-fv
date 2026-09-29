import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.MeasureParts

/-- Actual ELF entry address of _ZN13ssz_fv_native5codec13measure_parts17h3804244188cbc0c8E. -/
def address : Nat := 2298172

def byteSize : Nat := 1700

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10643ff#32), -- sub sp, sp, #0x190
  (4, 0xa9137bfd#32), -- stp x29, x30, [sp, #0x130]
  (8, 0xa9146ffc#32), -- stp x28, x27, [sp, #0x140]
  (12, 0xa91567fa#32), -- stp x26, x25, [sp, #0x150]
  (16, 0xa9165ff8#32), -- stp x24, x23, [sp, #0x160]
  (20, 0xa91757f6#32), -- stp x22, x21, [sp, #0x170]
  (24, 0xa9184ff4#32), -- stp x20, x19, [sp, #0x180]
  (28, 0xa940583b#32), -- ldp x27, x22, [x1]
  (32, 0x2a0503f9#32), -- mov w25, w5
  (36, 0xaa0403f4#32), -- mov x20, x4
  (40, 0xaa0303f5#32), -- mov x21, x3
  (44, 0xaa0103f7#32), -- mov x23, x1
  (48, 0xaa0203f8#32), -- mov x24, x2
  (52, 0xaa0003f3#32), -- mov x19, x0
  (56, 0xeb16007f#32), -- cmp x3, x22
  (60, 0x9a963068#32), -- csel x8, x3, x22, lo
  (64, 0xf100037f#32), -- cmp x27, #0x0
  (68, 0x9a88007a#32), -- csel x26, x3, x8, eq
  (72, 0xb40002db#32), -- cbz x27, 0x2311dc <.LBB87_5>
  (76, 0x8b1606c8#32), -- add x8, x22, x22, lsl #1
  (80, 0xd37df11c#32), -- lsl x28, x8, #3
  (84, 0xaa1b03e8#32), -- mov x8, x27
  (88, 0xb40002bc#32), -- cbz x28, 0x2311e8 <.LBB87_6>
  (92, 0xf9400900#32), -- ldr x0, [x8, #0x10]
  (96, 0x9100611d#32), -- add x29, x8, #0x18
  (100, 0x97ffffb4#32), -- bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>
  (104, 0xd100639c#32), -- sub x28, x28, #0x18
  (108, 0xaa1d03e8#32), -- mov x8, x29
  (112, 0xd10043ff#32), -- sub sp, sp, #0x10
  (116, 0xf90003e9#32), -- str x9, [sp]
  (120, 0x12000009#32), -- and w9, w0, #0x1
  (124, 0x35000089#32), -- cbnz w9, 0x2311c8 <.Llower_arm_639>
  (128, 0xf94003e9#32), -- ldr x9, [sp]
  (132, 0x910043ff#32), -- add sp, sp, #0x10
  (136, 0x14000004#32), -- b 0x2311d4 <.Llower_arm_640>
  (140, 0xf94003e9#32), -- ldr x9, [sp]
  (144, 0x910043ff#32), -- add sp, sp, #0x10
  (148, 0x17fffff1#32), -- b 0x231194 <.LBB87_2>
  (152, 0x2a1f03e0#32), -- mov w0, wzr
  (156, 0x14000005#32), -- b 0x2311ec <.LBB87_7>
  (160, 0xaa1603e0#32), -- mov x0, x22
  (164, 0x97ffffa4#32), -- bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>
  (168, 0x14000002#32), -- b 0x2311ec <.LBB87_7>
  (172, 0x52800020#32), -- mov w0, #0x1                // =1
  (176, 0x910053e9#32), -- add x9, sp, #0x14
  (180, 0x52000008#32), -- eor w8, w0, #0x1
  (184, 0x910063ea#32), -- add x10, sp, #0x18
  (188, 0xa904a7f5#32), -- stp x21, x9, [sp, #0x48]
  (192, 0x910043e9#32), -- add x9, sp, #0x10
  (196, 0x0a080328#32), -- and w8, w25, w8
  (200, 0xa905abe9#32), -- stp x9, x10, [sp, #0x58]
  (204, 0x9100a3e9#32), -- add x9, sp, #0x28
  (208, 0x390043e0#32), -- strb w0, [sp, #0x10]
  (212, 0x390053e8#32), -- strb w8, [sp, #0x14]
  (216, 0xd10043ff#32), -- sub sp, sp, #0x10
  (220, 0xf90003e9#32), -- str x9, [sp]
  (224, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (228, 0x910043e9#32), -- add x9, sp, #0x10
  (232, 0x91006129#32), -- add x9, x9, #0x18
  (236, 0xd280000a#32), -- mov x10, #0x0               // =0
  (240, 0xf900012a#32), -- str x10, [x9]
  (244, 0xd280000a#32), -- mov x10, #0x0               // =0
  (248, 0xf900052a#32), -- str x10, [x9, #0x8]
  (252, 0xf94007ea#32) -- ldr x10, [sp, #0x8]
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0xf94003e9#32), -- ldr x9, [sp]
  (260, 0x910043ff#32), -- add sp, sp, #0x10
  (264, 0xd10043ff#32), -- sub sp, sp, #0x10
  (268, 0xf90003e9#32), -- str x9, [sp]
  (272, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (276, 0x910043e9#32), -- add x9, sp, #0x10
  (280, 0x9100a129#32), -- add x9, x9, #0x28
  (284, 0xd280000a#32), -- mov x10, #0x0               // =0
  (288, 0xf900012a#32), -- str x10, [x9]
  (292, 0xd280000a#32), -- mov x10, #0x0               // =0
  (296, 0xf900052a#32), -- str x10, [x9, #0x8]
  (300, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (304, 0xf94003e9#32), -- ldr x9, [sp]
  (308, 0x910043ff#32), -- add sp, sp, #0x10
  (312, 0xa903e3f7#32), -- stp x23, x24, [sp, #0x38]
  (316, 0xf90037e9#32), -- str x9, [sp, #0x68]
  (320, 0xd10043ff#32), -- sub sp, sp, #0x10
  (324, 0xf90003e9#32), -- str x9, [sp]
  (328, 0x12000109#32), -- and w9, w8, #0x1
  (332, 0x34000089#32), -- cbz w9, 0x231298 <.Llower_arm_641>
  (336, 0xf94003e9#32), -- ldr x9, [sp]
  (340, 0x910043ff#32), -- add sp, sp, #0x10
  (344, 0x14000004#32), -- b 0x2312a4 <.Llower_arm_642>
  (348, 0xf94003e9#32), -- ldr x9, [sp]
  (352, 0x910043ff#32), -- add sp, sp, #0x10
  (356, 0x14000033#32), -- b 0x23136c <.LBB87_17>
  (360, 0xb400087a#32), -- cbz x26, 0x2313b0 <.LBB87_23>
  (364, 0xf9400288#32), -- ldr x8, [x20]
  (368, 0xf9400a8a#32), -- ldr x10, [x20, #0x10]
  (372, 0xab08014b#32), -- adds x11, x10, x8
  (376, 0x54001242#32), -- b.hs 0x2314fc <.LBB87_29>
  (380, 0xb100217f#32), -- cmn x11, #0x8
  (384, 0x54001208#32), -- b.hi 0x2314fc <.LBB87_29>
  (388, 0x91001d69#32), -- add x9, x11, #0x7
  (392, 0x927df129#32), -- and x9, x9, #0xfffffffffffffff8
  (396, 0xcb0b012b#32), -- sub x11, x9, x11
  (400, 0xab0a016a#32), -- adds x10, x11, x10
  (404, 0x54001162#32), -- b.hs 0x2314fc <.LBB87_29>
  (408, 0x8b1a0b4b#32), -- add x11, x26, x26, lsl #2
  (412, 0xd37df16b#32), -- lsl x11, x11, #3
  (416, 0xab0b014b#32), -- adds x11, x10, x11
  (420, 0x540010e2#32), -- b.hs 0x2314fc <.LBB87_29>
  (424, 0xf940068c#32), -- ldr x12, [x20, #0x8]
  (428, 0xeb0c017f#32), -- cmp x11, x12
  (432, 0x54001088#32), -- b.hi 0x2314fc <.LBB87_29>
  (436, 0xaa1f03f7#32), -- mov x23, xzr
  (440, 0x8b0a0118#32), -- add x24, x8, x10
  (444, 0x910343f9#32), -- add x25, sp, #0xd0
  (448, 0x9100413d#32), -- add x29, x9, #0x10
  (452, 0xf9000a8b#32), -- str x11, [x20, #0x10]
  (456, 0x910343e0#32), -- add x0, sp, #0xd0
  (460, 0x9100e3e1#32), -- add x1, sp, #0x38
  (464, 0xaa1703e2#32), -- mov x2, x23
  (468, 0xaa1403e3#32), -- mov x3, x20
  (472, 0x94000191#32), -- bl 0x231958 <_ZN13ssz_fv_native5codec13measure_parts28_$u7b$$u7b$closure$u7d$$u7d$17hbcad779f9c302ea9E>
  (476, 0xb94113fc#32), -- ldr w28, [sp, #0x110]
  (480, 0x350012dc#32), -- cbnz w28, 0x231574 <.LBB87_36>
  (484, 0xa94d2fea#32), -- ldp x10, x11, [sp, #0xd0]
  (488, 0x910006f7#32), -- add x23, x23, #0x1
  (492, 0xa9412728#32), -- ldp x8, x9, [x25, #0x10]
  (496, 0xeb17035f#32), -- cmp x26, x23
  (500, 0xa93f2faa#32), -- stp x10, x11, [x29, #-0x10]
  (504, 0xd10043ff#32), -- sub sp, sp, #0x10
  (508, 0xf90003e9#32) -- str x9, [sp]
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0x91000329#32), -- add x9, x25, #0x0
  (516, 0x91008129#32), -- add x9, x9, #0x20
  (520, 0xf940012a#32), -- ldr x10, [x9]
  (524, 0xf94003e9#32), -- ldr x9, [sp]
  (528, 0x910043ff#32), -- add sp, sp, #0x10
  (532, 0xa90027a8#32), -- stp x8, x9, [x29]
  (536, 0xf9000baa#32), -- str x10, [x29, #0x10]
  (540, 0x9100a3bd#32), -- add x29, x29, #0x28
  (544, 0xa911a7e8#32), -- stp x8, x9, [sp, #0x118]
  (548, 0xf90097ea#32), -- str x10, [sp, #0x128]
  (552, 0x54fffd01#32), -- b.ne 0x231304 <.LBB87_15>
  (556, 0x14000010#32), -- b 0x2313a8 <.LBB87_22>
  (560, 0xb400023a#32), -- cbz x26, 0x2313b0 <.LBB87_23>
  (564, 0xaa1f03f7#32), -- mov x23, xzr
  (568, 0x910343f9#32), -- add x25, sp, #0xd0
  (572, 0x52800118#32), -- mov w24, #0x8               // =8
  (576, 0x910343e0#32), -- add x0, sp, #0xd0
  (580, 0x9100e3e1#32), -- add x1, sp, #0x38
  (584, 0xaa1703e2#32), -- mov x2, x23
  (588, 0xaa1403e3#32), -- mov x3, x20
  (592, 0x94000173#32), -- bl 0x231958 <_ZN13ssz_fv_native5codec13measure_parts28_$u7b$$u7b$closure$u7d$$u7d$17hbcad779f9c302ea9E>
  (596, 0xb94113e8#32), -- ldr w8, [sp, #0x110]
  (600, 0x350009a8#32), -- cbnz w8, 0x2314c8 <.LBB87_28>
  (604, 0x910006f7#32), -- add x23, x23, #0x1
  (608, 0xeb17035f#32), -- cmp x26, x23
  (612, 0x54fffee1#32), -- b.ne 0x23137c <.LBB87_19>
  (616, 0xaa1f03fa#32), -- mov x26, xzr
  (620, 0xb500009b#32), -- cbnz x27, 0x2313b8 <.LBB87_24>
  (624, 0x14000036#32), -- b 0x231484 <.LBB87_26>
  (628, 0x52800118#32), -- mov w24, #0x8               // =8
  (632, 0xb400069b#32), -- cbz x27, 0x231484 <.LBB87_26>
  (636, 0xeb1502df#32), -- cmp x22, x21
  (640, 0x54000640#32), -- b.eq 0x231484 <.LBB87_26>
  (644, 0x52800028#32), -- mov w8, #0x1                // =1
  (648, 0xd10043ff#32), -- sub sp, sp, #0x10
  (652, 0xf90003e9#32), -- str x9, [sp]
  (656, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (660, 0x91000269#32), -- add x9, x19, #0x0
  (664, 0x91004129#32), -- add x9, x9, #0x10
  (668, 0xd280000a#32), -- mov x10, #0x0               // =0
  (672, 0xf900012a#32), -- str x10, [x9]
  (676, 0xd280000a#32), -- mov x10, #0x0               // =0
  (680, 0xf900052a#32), -- str x10, [x9, #0x8]
  (684, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (688, 0xf94003e9#32), -- ldr x9, [sp]
  (692, 0x910043ff#32), -- add sp, sp, #0x10
  (696, 0xd10043ff#32), -- sub sp, sp, #0x10
  (700, 0xf90003e9#32), -- str x9, [sp]
  (704, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (708, 0x91000269#32), -- add x9, x19, #0x0
  (712, 0xf9000128#32), -- str x8, [x9]
  (716, 0xd280000a#32), -- mov x10, #0x0               // =0
  (720, 0xf900052a#32), -- str x10, [x9, #0x8]
  (724, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (728, 0xf94003e9#32), -- ldr x9, [sp]
  (732, 0x910043ff#32), -- add sp, sp, #0x10
  (736, 0xd10043ff#32), -- sub sp, sp, #0x10
  (740, 0xf90003e9#32), -- str x9, [sp]
  (744, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (748, 0x91000269#32), -- add x9, x19, #0x0
  (752, 0x91008129#32), -- add x9, x9, #0x20
  (756, 0xd280000a#32), -- mov x10, #0x0               // =0
  (760, 0xf900012a#32), -- str x10, [x9]
  (764, 0xd280000a#32) -- mov x10, #0x0               // =0
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0xf900052a#32), -- str x10, [x9, #0x8]
  (772, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (776, 0xf94003e9#32), -- ldr x9, [sp]
  (780, 0x910043ff#32), -- add sp, sp, #0x10
  (784, 0xd10043ff#32), -- sub sp, sp, #0x10
  (788, 0xf90003e9#32), -- str x9, [sp]
  (792, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (796, 0x91000269#32), -- add x9, x19, #0x0
  (800, 0x9100c129#32), -- add x9, x9, #0x30
  (804, 0xd280000a#32), -- mov x10, #0x0               // =0
  (808, 0xf900012a#32), -- str x10, [x9]
  (812, 0xd280000a#32), -- mov x10, #0x0               // =0
  (816, 0xf900052a#32), -- str x10, [x9, #0x8]
  (820, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (824, 0xf94003e9#32), -- ldr x9, [sp]
  (828, 0x910043ff#32), -- add sp, sp, #0x10
  (832, 0xb9004268#32), -- str w8, [x19, #0x40]
  (836, 0x1400004d#32), -- b 0x2315b4 <.LBB87_38>
  (840, 0xa9418be1#32), -- ldp x1, x2, [sp, #0x18]
  (844, 0x910343e0#32), -- add x0, sp, #0xd0
  (848, 0xa94293e3#32), -- ldp x3, x4, [sp, #0x28]
  (852, 0xaa1403e5#32), -- mov x5, x20
  (856, 0x910343f7#32), -- add x23, sp, #0xd0
  (860, 0x97ffc8e5#32), -- bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>
  (864, 0xa94d53f5#32), -- ldp x21, x20, [sp, #0xd0]
  (868, 0xb94113f6#32), -- ldr w22, [sp, #0x110]
  (872, 0x340003b6#32), -- cbz w22, 0x231518 <.LBB87_30>
  (876, 0x91004260#32), -- add x0, x19, #0x10
  (880, 0x910042e1#32), -- add x1, x23, #0x10
  (884, 0x52800602#32), -- mov w2, #0x30               // =48
  (888, 0x94007007#32), -- bl 0x24d4d0 <memcpy>
  (892, 0xb94117e8#32), -- ldr w8, [sp, #0x114]
  (896, 0xa9005275#32), -- stp x21, x20, [x19]
  (900, 0x29082276#32), -- stp w22, w8, [x19, #0x40]
  (904, 0x1400003c#32), -- b 0x2315b4 <.LBB87_38>
  (908, 0xa9412b29#32), -- ldp x9, x10, [x25, #0x10]
  (912, 0xa9012a69#32), -- stp x9, x10, [x19, #0x10]
  (916, 0xa94fa7eb#32), -- ldp x11, x9, [sp, #0xf8]
  (920, 0xf9407bea#32), -- ldr x10, [sp, #0xf0]
  (924, 0xa902a66b#32), -- stp x11, x9, [x19, #0x28]
  (928, 0xa94d33e9#32), -- ldp x9, x12, [sp, #0xd0]
  (932, 0xf94087eb#32), -- ldr x11, [sp, #0x108]
  (936, 0xf900126a#32), -- str x10, [x19, #0x20]
  (940, 0xa9003269#32), -- stp x9, x12, [x19]
  (944, 0xb94117e9#32), -- ldr w9, [sp, #0x114]
  (948, 0xf9001e6b#32), -- str x11, [x19, #0x38]
  (952, 0x29082668#32), -- stp w8, w9, [x19, #0x40]
  (956, 0x1400002f#32), -- b 0x2315b4 <.LBB87_38>
  (960, 0x6f00e400#32), -- movi v0.2d, #0000000000000000
  (964, 0xaa1f03f4#32), -- mov x20, xzr
  (968, 0x5290001c#32), -- mov w28, #0x8000            // =32768
  (972, 0x52800035#32), -- mov w21, #0x1               // =1
  (976, 0xad0403e0#32), -- stp q0, q0, [sp, #0x80]
  (980, 0x3d801fe0#32), -- str q0, [sp, #0x70]
  (984, 0x14000022#32), -- b 0x23159c <.LBB87_37>
  (988, 0xb40005f5#32), -- cbz x21, 0x2315d4 <.LBB87_39>
  (992, 0xd1000689#32), -- sub x9, x20, #0x1
  (996, 0xb100053f#32), -- cmn x9, #0x1
  (1000, 0x54000b40#32), -- b.eq 0x23168c <.LBB87_43>
  (1004, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1008, 0xf90003eb#32), -- str x11, [sp]
  (1012, 0xaa0903eb#32), -- mov x11, x9
  (1016, 0xd37df16b#32), -- lsl x11, x11, #3
  (1020, 0x8b0b02ab#32) -- add x11, x21, x11
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk4 : List (Nat × BitVec 32) := [
  (1024, 0xf940016a#32), -- ldr x10, [x11]
  (1028, 0xf94003eb#32), -- ldr x11, [sp]
  (1032, 0x910043ff#32), -- add sp, sp, #0x10
  (1036, 0xaa0903e8#32), -- mov x8, x9
  (1040, 0xd1000529#32), -- sub x9, x9, #0x1
  (1044, 0xb4fffe8a#32), -- cbz x10, 0x231520 <.LBB87_32>
  (1048, 0x91000508#32), -- add x8, x8, #0x1
  (1052, 0xf100051f#32), -- cmp x8, #0x1
  (1056, 0x540004a1#32), -- b.ne 0x2315f0 <.LBB87_42>
  (1060, 0xf94002a8#32), -- ldr x8, [x21]
  (1064, 0xd2c00029#32), -- mov x9, #0x100000000        // =4294967296
  (1068, 0xeb09011f#32), -- cmp x8, x9
  (1072, 0x540003e1#32), -- b.ne 0x2315e8 <.LBB87_41>
  (1076, 0x14000020#32), -- b 0x2315f0 <.LBB87_42>
  (1080, 0xa94d53f5#32), -- ldp x21, x20, [sp, #0xd0]
  (1084, 0x910283e0#32), -- add x0, sp, #0xa0
  (1088, 0x91004321#32), -- add x1, x25, #0x10
  (1092, 0x52800602#32), -- mov w2, #0x30               // =48
  (1096, 0x94006fd3#32), -- bl 0x24d4d0 <memcpy>
  (1100, 0xb94117f6#32), -- ldr w22, [sp, #0x114]
  (1104, 0x9101c3e0#32), -- add x0, sp, #0x70
  (1108, 0x910283e1#32), -- add x1, sp, #0xa0
  (1112, 0x52800602#32), -- mov w2, #0x30               // =48
  (1116, 0x94006fce#32), -- bl 0x24d4d0 <memcpy>
  (1120, 0x91004260#32), -- add x0, x19, #0x10
  (1124, 0x9101c3e1#32), -- add x1, sp, #0x70
  (1128, 0x52800602#32), -- mov w2, #0x30               // =48
  (1132, 0xa9005275#32), -- stp x21, x20, [x19]
  (1136, 0x94006fc9#32), -- bl 0x24d4d0 <memcpy>
  (1140, 0x29085a7c#32), -- stp w28, w22, [x19, #0x40]
  (1144, 0xa9584ff4#32), -- ldp x20, x19, [sp, #0x180]
  (1148, 0xa95757f6#32), -- ldp x22, x21, [sp, #0x170]
  (1152, 0xa9565ff8#32), -- ldp x24, x23, [sp, #0x160]
  (1156, 0xa95567fa#32), -- ldp x26, x25, [sp, #0x150]
  (1160, 0xa9546ffc#32), -- ldp x28, x27, [sp, #0x140]
  (1164, 0xa9537bfd#32), -- ldp x29, x30, [sp, #0x130]
  (1168, 0x910643ff#32), -- add sp, sp, #0x190
  (1172, 0xd65f03c0#32), -- ret
  (1176, 0xb40005d4#32), -- cbz x20, 0x23168c <.LBB87_43>
  (1180, 0xd2c00028#32), -- mov x8, #0x100000000        // =4294967296
  (1184, 0xeb08029f#32), -- cmp x20, x8
  (1188, 0xaa1403e8#32), -- mov x8, x20
  (1192, 0x54000060#32), -- b.eq 0x2315f0 <.LBB87_42>
  (1196, 0xd360fd08#32), -- lsr x8, x8, #32
  (1200, 0xb4000508#32), -- cbz x8, 0x23168c <.LBB87_43>
  (1204, 0x52800028#32), -- mov w8, #0x1                // =1
  (1208, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1212, 0xf90003e9#32), -- str x9, [sp]
  (1216, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1220, 0x91000269#32), -- add x9, x19, #0x0
  (1224, 0x9100c129#32), -- add x9, x9, #0x30
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
  (1268, 0x91000269#32), -- add x9, x19, #0x0
  (1272, 0xf9000128#32), -- str x8, [x9]
  (1276, 0xd280000a#32) -- mov x10, #0x0               // =0
]

theorem chunk4_decodes :
    chunk4.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk5 : List (Nat × BitVec 32) := [
  (1280, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1284, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1288, 0xf94003e9#32), -- ldr x9, [sp]
  (1292, 0x910043ff#32), -- add sp, sp, #0x10
  (1296, 0x528002a8#32), -- mov w8, #0x15               // =21
  (1300, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1304, 0xf90003e9#32), -- str x9, [sp]
  (1308, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1312, 0x91000269#32), -- add x9, x19, #0x0
  (1316, 0x91008129#32), -- add x9, x9, #0x20
  (1320, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1324, 0xf900012a#32), -- str x10, [x9]
  (1328, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1332, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1336, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1340, 0xf94003e9#32), -- ldr x9, [sp]
  (1344, 0x910043ff#32), -- add sp, sp, #0x10
  (1348, 0xa9015275#32), -- stp x21, x20, [x19, #0x10]
  (1352, 0xb9004268#32), -- str w8, [x19, #0x40]
  (1356, 0x17ffffcb#32), -- b 0x2315b4 <.LBB87_38>
  (1360, 0xa941a3e9#32), -- ldp x9, x8, [sp, #0x18]
  (1364, 0xb40008c9#32), -- cbz x9, 0x2317a8 <.LBB87_51>
  (1368, 0xd100050b#32), -- sub x11, x8, #0x1
  (1372, 0xb100057f#32), -- cmn x11, #0x1
  (1376, 0x54000820#32), -- b.eq 0x2317a0 <.LBB87_49>
  (1380, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1384, 0xf90003ea#32), -- str x10, [sp]
  (1388, 0xaa0b03ea#32), -- mov x10, x11
  (1392, 0xd37df14a#32), -- lsl x10, x10, #3
  (1396, 0x8b0a012a#32), -- add x10, x9, x10
  (1400, 0xf940014c#32), -- ldr x12, [x10]
  (1404, 0xf94003ea#32), -- ldr x10, [sp]
  (1408, 0x910043ff#32), -- add sp, sp, #0x10
  (1412, 0xaa0b03ea#32), -- mov x10, x11
  (1416, 0xd100056b#32), -- sub x11, x11, #0x1
  (1420, 0xb4fffe8c#32), -- cbz x12, 0x231698 <.LBB87_45>
  (1424, 0x91000548#32), -- add x8, x10, #0x1
  (1428, 0xf100051f#32), -- cmp x8, #0x1
  (1432, 0x54000680#32), -- b.eq 0x2317a4 <.LBB87_50>
  (1436, 0x52800028#32), -- mov w8, #0x1                // =1
  (1440, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1444, 0xf90003e9#32), -- str x9, [sp]
  (1448, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1452, 0x91000269#32), -- add x9, x19, #0x0
  (1456, 0x9100c129#32), -- add x9, x9, #0x30
  (1460, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1464, 0xf900012a#32), -- str x10, [x9]
  (1468, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1472, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1476, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1480, 0xf94003e9#32), -- ldr x9, [sp]
  (1484, 0x910043ff#32), -- add sp, sp, #0x10
  (1488, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1492, 0xf90003e9#32), -- str x9, [sp]
  (1496, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1500, 0x91000269#32), -- add x9, x19, #0x0
  (1504, 0xf9000128#32), -- str x8, [x9]
  (1508, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1512, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1516, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1520, 0xf94003e9#32), -- ldr x9, [sp]
  (1524, 0x910043ff#32), -- add sp, sp, #0x10
  (1528, 0x52900028#32), -- mov w8, #0x8001             // =32769
  (1532, 0xd10043ff#32) -- sub sp, sp, #0x10
]

theorem chunk5_decodes :
    chunk5.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk6 : List (Nat × BitVec 32) := [
  (1536, 0xf90003e9#32), -- str x9, [sp]
  (1540, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1544, 0x91000269#32), -- add x9, x19, #0x0
  (1548, 0x91008129#32), -- add x9, x9, #0x20
  (1552, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1556, 0xf900012a#32), -- str x10, [x9]
  (1560, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1564, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1568, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1572, 0xf94003e9#32), -- ldr x9, [sp]
  (1576, 0x910043ff#32), -- add sp, sp, #0x10
  (1580, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1584, 0xf90003e9#32), -- str x9, [sp]
  (1588, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1592, 0x91000269#32), -- add x9, x19, #0x0
  (1596, 0x91004129#32), -- add x9, x9, #0x10
  (1600, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1604, 0xf900012a#32), -- str x10, [x9]
  (1608, 0xd280000a#32), -- mov x10, #0x0               // =0
  (1612, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1616, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1620, 0xf94003e9#32), -- ldr x9, [sp]
  (1624, 0x910043ff#32), -- add sp, sp, #0x10
  (1628, 0xb9004268#32), -- str w8, [x19, #0x40]
  (1632, 0x17ffff86#32), -- b 0x2315b4 <.LBB87_38>
  (1636, 0xb4000048#32), -- cbz x8, 0x2317a8 <.LBB87_51>
  (1640, 0xf9400128#32), -- ldr x8, [x9]
  (1644, 0xa9006a78#32), -- stp x24, x26, [x19]
  (1648, 0xa9015275#32), -- stp x21, x20, [x19, #0x10]
  (1652, 0xf9001268#32), -- str x8, [x19, #0x20]
  (1656, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1660, 0xf90003e9#32), -- str x9, [sp]
  (1664, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1668, 0x91000269#32), -- add x9, x19, #0x0
  (1672, 0x91010129#32), -- add x9, x9, #0x40
  (1676, 0x5280000a#32), -- mov w10, #0x0               // =0
  (1680, 0xb900012a#32), -- str w10, [x9]
  (1684, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1688, 0xf94003e9#32), -- ldr x9, [sp]
  (1692, 0x910043ff#32), -- add sp, sp, #0x10
  (1696, 0x17ffff76#32) -- b 0x2315b4 <.LBB87_38>
]

theorem chunk6_decodes :
    chunk6.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6

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

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, chunk3_decodes, chunk4_decodes, chunk5_decodes, chunk6_decodes, Bool.and_self]

end SszArm.Codec.Linked.MeasureParts
