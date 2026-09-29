import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.HelperIndices

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN13ssz_fv_native7indices14helper_indices17h979a25fb577b4251E. -/
def address : Nat := 2368612

def byteSize : Nat := 3856

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd105c3ff#32), -- sub sp, sp, #0x170
  (4, 0xa9117bfd#32), -- stp x29, x30, [sp, #0x110]
  (8, 0xa9126ffc#32), -- stp x28, x27, [sp, #0x120]
  (12, 0xa91367fa#32), -- stp x26, x25, [sp, #0x130]
  (16, 0xa9145ff8#32), -- stp x24, x23, [sp, #0x140]
  (20, 0xa91557f6#32), -- stp x22, x21, [sp, #0x150]
  (24, 0xa9164ff4#32), -- stp x20, x19, [sp, #0x160]
  (28, 0xaa0003f3#32), -- mov x19, x0
  (32, 0xb4001882#32), -- cbz x2, 0x242794 <.LBB125_42>
  (36, 0x8b021028#32), -- add x8, x1, x2, lsl #4
  (40, 0xaa0103f8#32), -- mov x24, x1
  (44, 0xaa0303f5#32), -- mov x21, x3
  (48, 0xaa0203f4#32), -- mov x20, x2
  (52, 0xaa1f03ec#32), -- mov x12, xzr
  (56, 0x91000441#32), -- add x1, x2, #0x1
  (60, 0xf90047e8#32), -- str x8, [sp, #0x88]
  (64, 0xaa1803e8#32), -- mov x8, x24
  (68, 0xeb01019f#32), -- cmp x12, x1
  (72, 0x54006880#32), -- b.eq 0x2431bc <.LBB125_131>
  (76, 0xa8c1250b#32), -- ldp x11, x9, [x8], #0x10
  (80, 0x9100058a#32), -- add x10, x12, #0x1
  (84, 0x8b0c130c#32), -- add x12, x24, x12, lsl #4
  (88, 0xaa1803ef#32), -- mov x15, x24
  (92, 0xf100013f#32), -- cmp x9, #0x0
  (96, 0xd100216e#32), -- sub x14, x11, #0x8
  (100, 0x54000061#32), -- b.ne 0x2424d4 <.Llower_arm_1041>
  (104, 0x5280000d#32), -- mov w13, #0x0 // =0
  (108, 0x14000002#32), -- b 0x2424d8 <.Llower_arm_1042>
  (112, 0x5280002d#32), -- mov w13, #0x1 // =1
  (116, 0xeb0c01ff#32), -- cmp x15, x12
  (120, 0x540011e0#32), -- b.eq 0x242718 <.LBB125_38>
  (124, 0xa94041f1#32), -- ldp x17, x16, [x15]
  (128, 0xb4000291#32), -- cbz x17, 0x242534 <.LBB125_11>
  (132, 0xd1002232#32), -- sub x18, x17, #0x8
  (136, 0xaa1003e0#32), -- mov x0, x16
  (140, 0xb40001a0#32), -- cbz x0, 0x242524 <.LBB125_10>
  (144, 0xd10043ff#32), -- sub sp, sp, #0x10
  (148, 0xf90003e9#32), -- str x9, [sp]
  (152, 0xaa0003e9#32), -- mov x9, x0
  (156, 0xd37df129#32), -- lsl x9, x9, #3
  (160, 0x8b090249#32), -- add x9, x18, x9
  (164, 0xf9400123#32), -- ldr x3, [x9]
  (168, 0xf94003e9#32), -- ldr x9, [sp]
  (172, 0x910043ff#32), -- add sp, sp, #0x10
  (176, 0xd1000402#32), -- sub x2, x0, #0x1
  (180, 0xaa0203e0#32), -- mov x0, x2
  (184, 0xb4fffea3#32), -- cbz x3, 0x2424f0 <.LBB125_7>
  (188, 0x91000440#32), -- add x0, x2, #0x1
  (192, 0xaa0d03e2#32), -- mov x2, x13
  (196, 0xaa0903f2#32), -- mov x18, x9
  (200, 0xb500014b#32), -- cbnz x11, 0x242554 <.LBB125_12>
  (204, 0x14000016#32), -- b 0x242588 <.LBB125_15>
  (208, 0xf100021f#32), -- cmp x16, #0x0
  (212, 0x54000061#32), -- b.ne 0x242544 <.Llower_arm_1043>
  (216, 0x52800000#32), -- mov w0, #0x0 // =0
  (220, 0x14000002#32), -- b 0x242548 <.Llower_arm_1044>
  (224, 0x52800020#32), -- mov w0, #0x1 // =1
  (228, 0xaa0d03e2#32), -- mov x2, x13
  (232, 0xaa0903f2#32), -- mov x18, x9
  (236, 0xb40001cb#32), -- cbz x11, 0x242588 <.LBB125_15>
  (240, 0xb4000232#32), -- cbz x18, 0x242598 <.LBB125_16>
  (244, 0xd10043ff#32), -- sub sp, sp, #0x10
  (248, 0xf90003e9#32), -- str x9, [sp]
  (252, 0xaa1203e9#32) -- mov x9, x18
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0xd37df129#32), -- lsl x9, x9, #3
  (260, 0x8b0901c9#32), -- add x9, x14, x9
  (264, 0xf9400123#32), -- ldr x3, [x9]
  (268, 0xf94003e9#32), -- ldr x9, [sp]
  (272, 0x910043ff#32), -- add sp, sp, #0x10
  (276, 0xd1000642#32), -- sub x2, x18, #0x1
  (280, 0xaa0203f2#32), -- mov x18, x2
  (284, 0xb4fffea3#32), -- cbz x3, 0x242554 <.LBB125_12>
  (288, 0x91000442#32), -- add x2, x2, #0x1
  (292, 0xeb02001f#32), -- cmp x0, x2
  (296, 0x910041ef#32), -- add x15, x15, #0x10
  (300, 0x54fffa41#32), -- b.ne 0x2424d8 <.Llower_arm_1042>
  (304, 0x14000004#32), -- b 0x2425a4 <.LBB125_17>
  (308, 0xeb1f001f#32), -- cmp x0, xzr
  (312, 0x910041ef#32), -- add x15, x15, #0x10
  (316, 0x54fff9c1#32), -- b.ne 0x2424d8 <.Llower_arm_1042>
  (320, 0xb40007d1#32), -- cbz x17, 0x24269c <.LBB125_29>
  (324, 0xd1000400#32), -- sub x0, x0, #0x1
  (328, 0xb50001ab#32), -- cbnz x11, 0x2425e0 <.LBB125_20>
  (332, 0x14000030#32), -- b 0x242670 <.LBB125_26>
  (336, 0xd10043ff#32), -- sub sp, sp, #0x10
  (340, 0xf90003e9#32), -- str x9, [sp]
  (344, 0xaa0003e9#32), -- mov x9, x0
  (348, 0xd37df129#32), -- lsl x9, x9, #3
  (352, 0x8b090169#32), -- add x9, x11, x9
  (356, 0xf9400122#32), -- ldr x2, [x9]
  (360, 0xf94003e9#32), -- ldr x9, [sp]
  (364, 0x910043ff#32), -- add sp, sp, #0x10
  (368, 0xeb02025f#32), -- cmp x18, x2
  (372, 0xd1000400#32), -- sub x0, x0, #0x1
  (376, 0x54000981#32), -- b.ne 0x24270c <.LBB125_37>
  (380, 0xb100041f#32), -- cmn x0, #0x1
  (384, 0x54000d40#32), -- b.eq 0x24278c <.LBB125_41>
  (388, 0xeb10001f#32), -- cmp x0, x16
  (392, 0x54000182#32), -- b.hs 0x24261c <.LBB125_23>
  (396, 0xd10043ff#32), -- sub sp, sp, #0x10
  (400, 0xf90003e9#32), -- str x9, [sp]
  (404, 0xaa0003e9#32), -- mov x9, x0
  (408, 0xd37df129#32), -- lsl x9, x9, #3
  (412, 0x8b090229#32), -- add x9, x17, x9
  (416, 0xf9400132#32), -- ldr x18, [x9]
  (420, 0xf94003e9#32), -- ldr x9, [sp]
  (424, 0x910043ff#32), -- add sp, sp, #0x10
  (428, 0xeb09001f#32), -- cmp x0, x9
  (432, 0x54fffd03#32), -- b.lo 0x2425b4 <.LBB125_19>
  (436, 0x14000004#32), -- b 0x242628 <.LBB125_24>
  (440, 0xaa1f03f2#32), -- mov x18, xzr
  (444, 0xeb09001f#32), -- cmp x0, x9
  (448, 0x54fffc83#32), -- b.lo 0x2425b4 <.LBB125_19>
  (452, 0xaa1f03e2#32), -- mov x2, xzr
  (456, 0xeb1f025f#32), -- cmp x18, xzr
  (460, 0xd1000400#32), -- sub x0, x0, #0x1
  (464, 0x54fffd60#32), -- b.eq 0x2425e0 <.LBB125_20>
  (468, 0x14000035#32), -- b 0x24270c <.LBB125_37>
  (472, 0xd10043ff#32), -- sub sp, sp, #0x10
  (476, 0xf90003e9#32), -- str x9, [sp]
  (480, 0xaa0003e9#32), -- mov x9, x0
  (484, 0xd37df129#32), -- lsl x9, x9, #3
  (488, 0x8b090229#32), -- add x9, x17, x9
  (492, 0xf9400132#32), -- ldr x18, [x9]
  (496, 0xf94003e9#32), -- ldr x9, [sp]
  (500, 0x910043ff#32), -- add sp, sp, #0x10
  (504, 0xf100001f#32), -- cmp x0, #0x0
  (508, 0xd1000400#32) -- sub x0, x0, #0x1
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0x9a9f0122#32), -- csel x2, x9, xzr, eq
  (516, 0xeb02025f#32), -- cmp x18, x2
  (520, 0x54000501#32), -- b.ne 0x24270c <.LBB125_37>
  (524, 0xb100041f#32), -- cmn x0, #0x1
  (528, 0x540008c0#32), -- b.eq 0x24278c <.LBB125_41>
  (532, 0xeb10001f#32), -- cmp x0, x16
  (536, 0x54fffe03#32), -- b.lo 0x24263c <.LBB125_25>
  (540, 0xaa1f03f2#32), -- mov x18, xzr
  (544, 0xf100001f#32), -- cmp x0, #0x0
  (548, 0xd1000400#32), -- sub x0, x0, #0x1
  (552, 0x9a9f0122#32), -- csel x2, x9, xzr, eq
  (556, 0xeb0203ff#32), -- cmp xzr, x2
  (560, 0x54fffee0#32), -- b.eq 0x242670 <.LBB125_26>
  (564, 0x1400001d#32), -- b 0x24270c <.LBB125_37>
  (568, 0xb40002cb#32), -- cbz x11, 0x2426f4 <.LBB125_35>
  (572, 0xd1000411#32), -- sub x17, x0, #0x1
  (576, 0x14000004#32), -- b 0x2426b4 <.LBB125_32>
  (580, 0xeb02025f#32), -- cmp x18, x2
  (584, 0xd1000631#32), -- sub x17, x17, #0x1
  (588, 0x540002e1#32), -- b.ne 0x24270c <.LBB125_37>
  (592, 0xb100063f#32), -- cmn x17, #0x1
  (596, 0x540006a0#32), -- b.eq 0x24278c <.LBB125_41>
  (600, 0xf100023f#32), -- cmp x17, #0x0
  (604, 0xaa1f03e2#32), -- mov x2, xzr
  (608, 0x9a9f0212#32), -- csel x18, x16, xzr, eq
  (612, 0xeb09023f#32), -- cmp x17, x9
  (616, 0x54fffee2#32), -- b.hs 0x2426a8 <.LBB125_31>
  (620, 0xd10043ff#32), -- sub sp, sp, #0x10
  (624, 0xf90003e9#32), -- str x9, [sp]
  (628, 0xaa1103e9#32), -- mov x9, x17
  (632, 0xd37df129#32), -- lsl x9, x9, #3
  (636, 0x8b090169#32), -- add x9, x11, x9
  (640, 0xf9400122#32), -- ldr x2, [x9]
  (644, 0xf94003e9#32), -- ldr x9, [sp]
  (648, 0x910043ff#32), -- add sp, sp, #0x10
  (652, 0x17ffffee#32), -- b 0x2426a8 <.LBB125_31>
  (656, 0xb40004c0#32), -- cbz x0, 0x24278c <.LBB125_41>
  (660, 0xf1000400#32), -- subs x0, x0, #0x1
  (664, 0x9a9f0212#32), -- csel x18, x16, xzr, eq
  (668, 0x9a9f0122#32), -- csel x2, x9, xzr, eq
  (672, 0xeb02025f#32), -- cmp x18, x2
  (676, 0x54ffff60#32), -- b.eq 0x2426f4 <.LBB125_35>
  (680, 0xeb02025f#32), -- cmp x18, x2
  (684, 0x54ffee41#32), -- b.ne 0x2424d8 <.Llower_arm_1042>
  (688, 0x1400001e#32), -- b 0x24278c <.LBB125_41>
  (692, 0xf94047e9#32), -- ldr x9, [sp, #0x88]
  (696, 0xaa0a03ec#32), -- mov x12, x10
  (700, 0xeb09011f#32), -- cmp x8, x9
  (704, 0x54ffec21#32), -- b.ne 0x2424a8 <.LBB125_2>
  (708, 0x910323e0#32), -- add x0, sp, #0xc8
  (712, 0xaa1803e1#32), -- mov x1, x24
  (716, 0xaa1403e2#32), -- mov x2, x20
  (720, 0xaa1803e3#32), -- mov x3, x24
  (724, 0xaa1403e4#32), -- mov x4, x20
  (728, 0x94000fe9#32), -- bl 0x2466e0 <_ZN13ssz_fv_native7indices18reject_claim_paths17hef042388294333e5E>
  (732, 0xb9410be8#32), -- ldr w8, [sp, #0x108]
  (736, 0x350008c8#32), -- cbnz w8, 0x24285c <.LBB125_44>
  (740, 0xaa1f03e0#32), -- mov x0, xzr
  (744, 0xd10043ff#32), -- sub sp, sp, #0x10
  (748, 0xf90003e9#32), -- str x9, [sp]
  (752, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (756, 0x910043e9#32), -- add x9, sp, #0x10
  (760, 0x91016129#32), -- add x9, x9, #0x58
  (764, 0xd280000a#32) -- mov x10, #0x0 // =0
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0xf900012a#32), -- str x10, [x9]
  (772, 0xf9000538#32), -- str x24, [x9, #0x8]
  (776, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (780, 0xf94003e9#32), -- ldr x9, [sp]
  (784, 0x910043ff#32), -- add sp, sp, #0x10
  (788, 0x9280000c#32), -- mov x12, #-0x1 // =-1
  (792, 0xaa1803ee#32), -- mov x14, x24
  (796, 0xa90257f3#32), -- stp x19, x21, [sp, #0x20]
  (800, 0xf9001ff4#32), -- str x20, [sp, #0x38]
  (804, 0x1400004a#32), -- b 0x2428b0 <.LBB125_47>
  (808, 0x52800548#32), -- mov w8, #0x2a // =42
  (812, 0x14000002#32), -- b 0x242798 <.LBB125_43>
  (816, 0x52800528#32), -- mov w8, #0x29 // =41
  (820, 0x52800029#32), -- mov w9, #0x1 // =1
  (824, 0xd10043ff#32), -- sub sp, sp, #0x10
  (828, 0xf90003e9#32), -- str x9, [sp]
  (832, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (836, 0x910043e9#32), -- add x9, sp, #0x10
  (840, 0x91036129#32), -- add x9, x9, #0xd8
  (844, 0xd280000a#32), -- mov x10, #0x0 // =0
  (848, 0xf900012a#32), -- str x10, [x9]
  (852, 0xd280000a#32), -- mov x10, #0x0 // =0
  (856, 0xf900052a#32), -- str x10, [x9, #0x8]
  (860, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (864, 0xf94003e9#32), -- ldr x9, [sp]
  (868, 0x910043ff#32), -- add sp, sp, #0x10
  (872, 0xd10043ff#32), -- sub sp, sp, #0x10
  (876, 0xf90003ea#32), -- str x10, [sp]
  (880, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (884, 0x910043ea#32), -- add x10, sp, #0x10
  (888, 0x9103214a#32), -- add x10, x10, #0xc8
  (892, 0xf9000149#32), -- str x9, [x10]
  (896, 0xd280000b#32), -- mov x11, #0x0 // =0
  (900, 0xf900054b#32), -- str x11, [x10, #0x8]
  (904, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (908, 0xf94003ea#32), -- ldr x10, [sp]
  (912, 0x910043ff#32), -- add sp, sp, #0x10
  (916, 0xd10043ff#32), -- sub sp, sp, #0x10
  (920, 0xf90003e9#32), -- str x9, [sp]
  (924, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (928, 0x910043e9#32), -- add x9, sp, #0x10
  (932, 0x9103a129#32), -- add x9, x9, #0xe8
  (936, 0xd280000a#32), -- mov x10, #0x0 // =0
  (940, 0xf900012a#32), -- str x10, [x9]
  (944, 0xd280000a#32), -- mov x10, #0x0 // =0
  (948, 0xf900052a#32), -- str x10, [x9, #0x8]
  (952, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (956, 0xf94003e9#32), -- ldr x9, [sp]
  (960, 0x910043ff#32), -- add sp, sp, #0x10
  (964, 0xd10043ff#32), -- sub sp, sp, #0x10
  (968, 0xf90003e9#32), -- str x9, [sp]
  (972, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (976, 0x910043e9#32), -- add x9, sp, #0x10
  (980, 0x9103e129#32), -- add x9, x9, #0xf8
  (984, 0xd280000a#32), -- mov x10, #0x0 // =0
  (988, 0xf900012a#32), -- str x10, [x9]
  (992, 0xd280000a#32), -- mov x10, #0x0 // =0
  (996, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1000, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1004, 0xf94003e9#32), -- ldr x9, [sp]
  (1008, 0x910043ff#32), -- add sp, sp, #0x10
  (1012, 0xb9010be8#32), -- str w8, [sp, #0x108]
  (1016, 0x910323e1#32), -- add x1, sp, #0xc8
  (1020, 0xaa1303e0#32) -- mov x0, x19
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk4 : List (Nat × BitVec 32) := [
  (1024, 0x52800902#32), -- mov w2, #0x48 // =72
  (1028, 0x94002b1a#32), -- bl 0x24d4d0 <memcpy>
  (1032, 0xa9564ff4#32), -- ldp x20, x19, [sp, #0x160]
  (1036, 0xa95557f6#32), -- ldp x22, x21, [sp, #0x150]
  (1040, 0xa9545ff8#32), -- ldp x24, x23, [sp, #0x140]
  (1044, 0xa95367fa#32), -- ldp x26, x25, [sp, #0x130]
  (1048, 0xa9526ffc#32), -- ldp x28, x27, [sp, #0x120]
  (1052, 0xa9517bfd#32), -- ldp x29, x30, [sp, #0x110]
  (1056, 0x9105c3ff#32), -- add sp, sp, #0x170
  (1060, 0xd65f03c0#32), -- ret
  (1064, 0xa94353ee#32), -- ldp x14, x20, [sp, #0x30]
  (1068, 0x9280000c#32), -- mov x12, #-0x1 // =-1
  (1072, 0xf94047e8#32), -- ldr x8, [sp, #0x88]
  (1076, 0xf9403fe0#32), -- ldr x0, [sp, #0x78]
  (1080, 0xa94237f7#32), -- ldp x23, x13, [sp, #0x20]
  (1084, 0x910041ce#32), -- add x14, x14, #0x10
  (1088, 0x91000400#32), -- add x0, x0, #0x1
  (1092, 0xeb0801df#32), -- cmp x14, x8
  (1096, 0x54001ec0#32), -- b.eq 0x242c84 <.LBB125_82>
  (1100, 0xa94021c9#32), -- ldp x9, x8, [x14]
  (1104, 0xf9003fe0#32), -- str x0, [sp, #0x78]
  (1108, 0xf9001bee#32), -- str x14, [sp, #0x30]
  (1112, 0xb4000289#32), -- cbz x9, 0x24290c <.LBB125_52>
  (1116, 0xd1002129#32), -- sub x9, x9, #0x8
  (1120, 0xb4fffe48#32), -- cbz x8, 0x24288c <.LBB125_46>
  (1124, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1128, 0xf90003ea#32), -- str x10, [sp]
  (1132, 0xaa0803ea#32), -- mov x10, x8
  (1136, 0xd37df14a#32), -- lsl x10, x10, #3
  (1140, 0x8b0a012a#32), -- add x10, x9, x10
  (1144, 0xf940014b#32), -- ldr x11, [x10]
  (1148, 0xf94003ea#32), -- ldr x10, [sp]
  (1152, 0x910043ff#32), -- add sp, sp, #0x10
  (1156, 0xaa0803ea#32), -- mov x10, x8
  (1160, 0xd1000508#32), -- sub x8, x8, #0x1
  (1164, 0xb4fffeab#32), -- cbz x11, 0x2428c4 <.LBB125_49>
  (1168, 0xd37ae548#32), -- lsl x8, x10, #6
  (1172, 0xd37afd4a#32), -- lsr x10, x10, #58
  (1176, 0xf1010109#32), -- subs x9, x8, #0x40
  (1180, 0xaa0b03e8#32), -- mov x8, x11
  (1184, 0x9a0c014a#32), -- adc x10, x10, x12
  (1188, 0x14000004#32), -- b 0x242918 <.LBB125_54>
  (1192, 0xb4fffc08#32), -- cbz x8, 0x24288c <.LBB125_46>
  (1196, 0xaa1f03e9#32), -- mov x9, xzr
  (1200, 0xaa1f03ea#32), -- mov x10, xzr
  (1204, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1208, 0xf90003e9#32), -- str x9, [sp]
  (1212, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1216, 0xaa0803e9#32), -- mov x9, x8
  (1220, 0xd280080a#32), -- mov x10, #0x40 // =64
  (1224, 0xb4000089#32), -- cbz x9, 0x24293c <.Llower_arm_1046>
  (1228, 0xd100054a#32), -- sub x10, x10, #0x1
  (1232, 0xd341fd29#32), -- lsr x9, x9, #1
  (1236, 0xb5ffffc9#32), -- cbnz x9, 0x242930 <.Llower_arm_1045>
  (1240, 0xaa0a03e8#32), -- mov x8, x10
  (1244, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1248, 0xf94003e9#32), -- ldr x9, [sp]
  (1252, 0x910043ff#32), -- add sp, sp, #0x10
  (1256, 0x5280080b#32), -- mov w11, #0x40 // =64
  (1260, 0x4b080168#32), -- sub w8, w11, w8
  (1264, 0xab080128#32), -- adds x8, x9, x8
  (1268, 0x54000062#32), -- b.hs 0x242964 <.Llower_arm_1047>
  (1272, 0xaa0a03e9#32), -- mov x9, x10
  (1276, 0x14000002#32) -- b 0x242968 <.Llower_arm_1048>
]

theorem chunk4_decodes :
    chunk4.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk5 : List (Nat × BitVec 32) := [
  (1280, 0x91000549#32), -- add x9, x10, #0x1
  (1284, 0xf100050b#32), -- subs x11, x8, #0x1
  (1288, 0x9a0c012a#32), -- adc x10, x9, x12
  (1292, 0xf100091f#32), -- cmp x8, #0x2
  (1296, 0xfa1f013f#32), -- sbcs xzr, x9, xzr
  (1300, 0xa904afea#32), -- stp x10, x11, [sp, #0x48]
  (1304, 0x54fff883#32), -- b.lo 0x24288c <.LBB125_46>
  (1308, 0xeb14001f#32), -- cmp x0, x20
  (1312, 0x54004e82#32), -- b.hs 0x243354 <.LBB125_141>
  (1316, 0x8b001308#32), -- add x8, x24, x0, lsl #4
  (1320, 0xaa1f03fb#32), -- mov x27, xzr
  (1324, 0xaa1f03fc#32), -- mov x28, xzr
  (1328, 0xa9406909#32), -- ldp x9, x26, [x8]
  (1332, 0xd100212d#32), -- sub x13, x9, #0x8
  (1336, 0xf90043e9#32), -- str x9, [sp, #0x80]
  (1340, 0xf90023ed#32), -- str x13, [sp, #0x40]
  (1344, 0x14000008#32), -- b 0x2429c4 <.LBB125_58>
  (1348, 0xf9403bfb#32), -- ldr x27, [sp, #0x70]
  (1352, 0xf9402be8#32), -- ldr x8, [sp, #0x50]
  (1356, 0xa94673f8#32), -- ldp x24, x28, [sp, #0x60]
  (1360, 0xeb08037f#32), -- cmp x27, x8
  (1364, 0xa94423ed#32), -- ldp x13, x8, [sp, #0x40]
  (1368, 0xfa08039f#32), -- sbcs xzr, x28, x8
  (1372, 0x54fff662#32), -- b.hs 0x24288c <.LBB125_46>
  (1376, 0xb100076b#32), -- adds x11, x27, #0x1
  (1380, 0xf94043e8#32), -- ldr x8, [sp, #0x80]
  (1384, 0x54000062#32), -- b.hs 0x2429d8 <.Llower_arm_1049>
  (1388, 0xaa1c03ec#32), -- mov x12, x28
  (1392, 0x14000002#32), -- b 0x2429dc <.Llower_arm_1050>
  (1396, 0x9100078c#32), -- add x12, x28, #0x1
  (1400, 0xa906afec#32), -- stp x12, x11, [sp, #0x68]
  (1404, 0xb4000288#32), -- cbz x8, 0x242a30 <.LBB125_63>
  (1408, 0xaa1a03ea#32), -- mov x10, x26
  (1412, 0xb40005aa#32), -- cbz x10, 0x242a9c <.LBB125_65>
  (1416, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1420, 0xf90003e9#32), -- str x9, [sp]
  (1424, 0xaa0a03e9#32), -- mov x9, x10
  (1428, 0xd37df129#32), -- lsl x9, x9, #3
  (1432, 0x8b0901a9#32), -- add x9, x13, x9
  (1436, 0xf9400128#32), -- ldr x8, [x9]
  (1440, 0xf94003e9#32), -- ldr x9, [sp]
  (1444, 0x910043ff#32), -- add sp, sp, #0x10
  (1448, 0xaa0a03e9#32), -- mov x9, x10
  (1452, 0xd100054a#32), -- sub x10, x10, #0x1
  (1456, 0xb4fffea8#32), -- cbz x8, 0x2429e8 <.LBB125_60>
  (1460, 0xd37ae52a#32), -- lsl x10, x9, #6
  (1464, 0xd37afd2b#32), -- lsr x11, x9, #58
  (1468, 0xf1010149#32), -- subs x9, x10, #0x40
  (1472, 0x9280000a#32), -- mov x10, #-0x1 // =-1
  (1476, 0x9a0a016a#32), -- adc x10, x11, x10
  (1480, 0x14000007#32), -- b 0x242a48 <.LBB125_64>
  (1484, 0xaa1f03e9#32), -- mov x9, xzr
  (1488, 0xaa1f03ea#32), -- mov x10, xzr
  (1492, 0xaa1f03eb#32), -- mov x11, xzr
  (1496, 0xaa1f03ec#32), -- mov x12, xzr
  (1500, 0xaa1a03e8#32), -- mov x8, x26
  (1504, 0xb400031a#32), -- cbz x26, 0x242aa4 <.LBB125_66>
  (1508, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1512, 0xf90003e9#32), -- str x9, [sp]
  (1516, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1520, 0xaa0803e9#32), -- mov x9, x8
  (1524, 0xd280080a#32), -- mov x10, #0x40 // =64
  (1528, 0xb4000089#32), -- cbz x9, 0x242a6c <.Llower_arm_1052>
  (1532, 0xd100054a#32) -- sub x10, x10, #0x1
]

theorem chunk5_decodes :
    chunk5.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk6 : List (Nat × BitVec 32) := [
  (1536, 0xd341fd29#32), -- lsr x9, x9, #1
  (1540, 0xb5ffffc9#32), -- cbnz x9, 0x242a60 <.Llower_arm_1051>
  (1544, 0xaa0a03e8#32), -- mov x8, x10
  (1548, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1552, 0xf94003e9#32), -- ldr x9, [sp]
  (1556, 0x910043ff#32), -- add sp, sp, #0x10
  (1560, 0x5280080b#32), -- mov w11, #0x40 // =64
  (1564, 0x4b080168#32), -- sub w8, w11, w8
  (1568, 0xab08012b#32), -- adds x11, x9, x8
  (1572, 0x54000062#32), -- b.hs 0x242a94 <.Llower_arm_1053>
  (1576, 0xaa0a03ec#32), -- mov x12, x10
  (1580, 0x14000002#32), -- b 0x242a98 <.Llower_arm_1054>
  (1584, 0x9100054c#32), -- add x12, x10, #0x1
  (1588, 0x14000003#32), -- b 0x242aa4 <.LBB125_66>
  (1592, 0xaa1f03eb#32), -- mov x11, xzr
  (1596, 0xaa1f03ec#32), -- mov x12, xzr
  (1600, 0xf1000568#32), -- subs x8, x11, #0x1
  (1604, 0xaa1f03f3#32), -- mov x19, xzr
  (1608, 0xfa1f0189#32), -- sbcs x9, x12, xzr
  (1612, 0x9a8833e8#32), -- csel x8, xzr, x8, lo
  (1616, 0x9a8933e9#32), -- csel x9, xzr, x9, lo
  (1620, 0xeb1b0116#32), -- subs x22, x8, x27
  (1624, 0xda1c0135#32), -- sbc x21, x9, x28
  (1628, 0x14000006#32), -- b 0x242ad8 <.LBB125_68>
  (1632, 0xf94047e8#32), -- ldr x8, [sp, #0x88]
  (1636, 0x91004318#32), -- add x24, x24, #0x10
  (1640, 0x91000673#32), -- add x19, x19, #0x1
  (1644, 0xeb08031f#32), -- cmp x24, x8
  (1648, 0x54000cc0#32), -- b.eq 0x242c6c <.LBB125_80>
  (1652, 0xa9407717#32), -- ldp x23, x29, [x24]
  (1656, 0xb40002b7#32), -- cbz x23, 0x242b30 <.LBB125_73>
  (1660, 0xd10022ea#32), -- sub x10, x23, #0x8
  (1664, 0xaa1d03eb#32), -- mov x11, x29
  (1668, 0xb40005ab#32), -- cbz x11, 0x242b9c <.LBB125_75>
  (1672, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1676, 0xf90003e9#32), -- str x9, [sp]
  (1680, 0xaa0b03e9#32), -- mov x9, x11
  (1684, 0xd37df129#32), -- lsl x9, x9, #3
  (1688, 0x8b090149#32), -- add x9, x10, x9
  (1692, 0xf9400128#32), -- ldr x8, [x9]
  (1696, 0xf94003e9#32), -- ldr x9, [sp]
  (1700, 0x910043ff#32), -- add sp, sp, #0x10
  (1704, 0xaa0b03e9#32), -- mov x9, x11
  (1708, 0xd100056b#32), -- sub x11, x11, #0x1
  (1712, 0xb4fffea8#32), -- cbz x8, 0x242ae8 <.LBB125_70>
  (1716, 0xd37ae52a#32), -- lsl x10, x9, #6
  (1720, 0xd37afd2b#32), -- lsr x11, x9, #58
  (1724, 0xf1010149#32), -- subs x9, x10, #0x40
  (1728, 0x9280000a#32), -- mov x10, #-0x1 // =-1
  (1732, 0x9a0a016a#32), -- adc x10, x11, x10
  (1736, 0x14000007#32), -- b 0x242b48 <.LBB125_74>
  (1740, 0xaa1f03e9#32), -- mov x9, xzr
  (1744, 0xaa1f03ea#32), -- mov x10, xzr
  (1748, 0xaa1f03eb#32), -- mov x11, xzr
  (1752, 0xaa1f03ec#32), -- mov x12, xzr
  (1756, 0xaa1d03e8#32), -- mov x8, x29
  (1760, 0xb40002fd#32), -- cbz x29, 0x242ba0 <.LBB125_76>
  (1764, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1768, 0xf90003e9#32), -- str x9, [sp]
  (1772, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1776, 0xaa0803e9#32), -- mov x9, x8
  (1780, 0xd280080a#32), -- mov x10, #0x40 // =64
  (1784, 0xb4000089#32), -- cbz x9, 0x242b6c <.Llower_arm_1056>
  (1788, 0xd100054a#32) -- sub x10, x10, #0x1
]

theorem chunk6_decodes :
    chunk6.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk7 : List (Nat × BitVec 32) := [
  (1792, 0xd341fd29#32), -- lsr x9, x9, #1
  (1796, 0xb5ffffc9#32), -- cbnz x9, 0x242b60 <.Llower_arm_1055>
  (1800, 0xaa0a03e8#32), -- mov x8, x10
  (1804, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1808, 0xf94003e9#32), -- ldr x9, [sp]
  (1812, 0x910043ff#32), -- add sp, sp, #0x10
  (1816, 0x5280080b#32), -- mov w11, #0x40 // =64
  (1820, 0x4b080168#32), -- sub w8, w11, w8
  (1824, 0xab08012b#32), -- adds x11, x9, x8
  (1828, 0x54000062#32), -- b.hs 0x242b94 <.Llower_arm_1057>
  (1832, 0xaa0a03ec#32), -- mov x12, x10
  (1836, 0x14000002#32), -- b 0x242b98 <.Llower_arm_1058>
  (1840, 0x9100054c#32), -- add x12, x10, #0x1
  (1844, 0x14000002#32), -- b 0x242ba0 <.LBB125_76>
  (1848, 0xaa1f03ec#32), -- mov x12, xzr
  (1852, 0xf1000568#32), -- subs x8, x11, #0x1
  (1856, 0xfa1f018a#32), -- sbcs x10, x12, xzr
  (1860, 0x9a8833e9#32), -- csel x9, xzr, x8, lo
  (1864, 0x9a8a33e8#32), -- csel x8, xzr, x10, lo
  (1868, 0xeb16013f#32), -- cmp x9, x22
  (1872, 0xfa15011f#32), -- sbcs xzr, x8, x21
  (1876, 0x54fff863#32), -- b.lo 0x242ac4 <.LBB125_67>
  (1880, 0xeb160134#32), -- subs x20, x9, x22
  (1884, 0xf94043e0#32), -- ldr x0, [sp, #0x80]
  (1888, 0xaa1a03e1#32), -- mov x1, x26
  (1892, 0xda150119#32), -- sbc x25, x8, x21
  (1896, 0xaa1b03e2#32), -- mov x2, x27
  (1900, 0xaa1c03e3#32), -- mov x3, x28
  (1904, 0x52800024#32), -- mov w4, #0x1 // =1
  (1908, 0xaa1703e5#32), -- mov x5, x23
  (1912, 0xaa1d03e6#32), -- mov x6, x29
  (1916, 0xa90067f4#32), -- stp x20, x25, [sp]
  (1920, 0x940001e4#32), -- bl 0x243374 <_ZN13ssz_fv_native7indices12prefix_equal17h455af9025a76ffe0E>
  (1924, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1928, 0xf90003e9#32), -- str x9, [sp]
  (1932, 0x12000009#32), -- and w9, w0, #0x1
  (1936, 0x35000089#32), -- cbnz w9, 0x242c04 <.Llower_arm_1059>
  (1940, 0xf94003e9#32), -- ldr x9, [sp]
  (1944, 0x910043ff#32), -- add sp, sp, #0x10
  (1948, 0x14000004#32), -- b 0x242c10 <.Llower_arm_1060>
  (1952, 0xf94003e9#32), -- ldr x9, [sp]
  (1956, 0x910043ff#32), -- add sp, sp, #0x10
  (1960, 0x17ffff67#32), -- b 0x2429a8 <.LBB125_57>
  (1964, 0xf9403fe8#32), -- ldr x8, [sp, #0x78]
  (1968, 0xeb08027f#32), -- cmp x19, x8
  (1972, 0x54fff562#32), -- b.hs 0x242ac4 <.LBB125_67>
  (1976, 0xf94043e0#32), -- ldr x0, [sp, #0x80]
  (1980, 0x2a1f03e4#32), -- mov w4, wzr
  (1984, 0xaa1a03e1#32), -- mov x1, x26
  (1988, 0xaa1b03e2#32), -- mov x2, x27
  (1992, 0xaa1c03e3#32), -- mov x3, x28
  (1996, 0xaa1703e5#32), -- mov x5, x23
  (2000, 0xaa1d03e6#32), -- mov x6, x29
  (2004, 0xa90067f4#32), -- stp x20, x25, [sp]
  (2008, 0x940001ce#32), -- bl 0x243374 <_ZN13ssz_fv_native7indices12prefix_equal17h455af9025a76ffe0E>
  (2012, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2016, 0xf90003e9#32), -- str x9, [sp]
  (2020, 0x12000009#32), -- and w9, w0, #0x1
  (2024, 0x34000089#32), -- cbz w9, 0x242c5c <.Llower_arm_1061>
  (2028, 0xf94003e9#32), -- ldr x9, [sp]
  (2032, 0x910043ff#32), -- add sp, sp, #0x10
  (2036, 0x14000004#32), -- b 0x242c68 <.Llower_arm_1062>
  (2040, 0xf94003e9#32), -- ldr x9, [sp]
  (2044, 0x910043ff#32) -- add sp, sp, #0x10
]

theorem chunk7_decodes :
    chunk7.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk8 : List (Nat × BitVec 32) := [
  (2048, 0x17ffff98#32), -- b 0x242ac4 <.LBB125_67>
  (2052, 0x17ffff50#32), -- b 0x2429a8 <.LBB125_57>
  (2056, 0xf9402fe8#32), -- ldr x8, [sp, #0x58]
  (2060, 0xb100051f#32), -- cmn x8, #0x1
  (2064, 0x54002f20#32), -- b.eq 0x243258 <.LBB125_137>
  (2068, 0x91000508#32), -- add x8, x8, #0x1
  (2072, 0xf9002fe8#32), -- str x8, [sp, #0x58]
  (2076, 0x17ffff4a#32), -- b 0x2429a8 <.LBB125_57>
  (2080, 0xf9402fe8#32), -- ldr x8, [sp, #0x58]
  (2084, 0xb4002ba8#32), -- cbz x8, 0x2431fc <.LBB125_134>
  (2088, 0xd37cfd08#32), -- lsr x8, x8, #60
  (2092, 0xb50029c8#32), -- cbnz x8, 0x2431c8 <.LBB125_132>
  (2096, 0xf9402fe8#32), -- ldr x8, [sp, #0x58]
  (2100, 0xd37ced09#32), -- lsl x9, x8, #4
  (2104, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2108, 0xf90003ea#32), -- str x10, [sp]
  (2112, 0x9241012a#32), -- and x10, x9, #0x8000000000000000
  (2116, 0xb500008a#32), -- cbnz x10, 0x242cb8 <.Llower_arm_1063>
  (2120, 0xf94003ea#32), -- ldr x10, [sp]
  (2124, 0x910043ff#32), -- add sp, sp, #0x10
  (2128, 0x14000004#32), -- b 0x242cc4 <.Llower_arm_1064>
  (2132, 0xf94003ea#32), -- ldr x10, [sp]
  (2136, 0x910043ff#32), -- add sp, sp, #0x10
  (2140, 0x14000142#32), -- b 0x2431c8 <.LBB125_132>
  (2144, 0xf94001a8#32), -- ldr x8, [x13]
  (2148, 0xf94009aa#32), -- ldr x10, [x13, #0x10]
  (2152, 0xab08014b#32), -- adds x11, x10, x8
  (2156, 0x540027c2#32), -- b.hs 0x2431c8 <.LBB125_132>
  (2160, 0xb100217f#32), -- cmn x11, #0x8
  (2164, 0x54002788#32), -- b.hi 0x2431c8 <.LBB125_132>
  (2168, 0x91001d6c#32), -- add x12, x11, #0x7
  (2172, 0x927df18c#32), -- and x12, x12, #0xfffffffffffffff8
  (2176, 0xcb0b018b#32), -- sub x11, x12, x11
  (2180, 0xab0a016a#32), -- adds x10, x11, x10
  (2184, 0x540026e2#32), -- b.hs 0x2431c8 <.LBB125_132>
  (2188, 0xab090149#32), -- adds x9, x10, x9
  (2192, 0x540026a2#32), -- b.hs 0x2431c8 <.LBB125_132>
  (2196, 0xf94005ab#32), -- ldr x11, [x13, #0x8]
  (2200, 0xeb0b013f#32), -- cmp x9, x11
  (2204, 0x54002648#32), -- b.hi 0x2431c8 <.LBB125_132>
  (2208, 0xaa1f03f6#32), -- mov x22, xzr
  (2212, 0xaa1f03f3#32), -- mov x19, xzr
  (2216, 0xaa1f03f4#32), -- mov x20, xzr
  (2220, 0xaa1f03eb#32), -- mov x11, xzr
  (2224, 0x8b0a0115#32), -- add x21, x8, x10
  (2228, 0xf90009a9#32), -- str x9, [x13, #0x10]
  (2232, 0xf90037f5#32), -- str x21, [sp, #0x68]
  (2236, 0xf9003beb#32), -- str x11, [sp, #0x70]
  (2240, 0x1400001a#32), -- b 0x242d8c <.Llower_arm_1068>
  (2244, 0xaa1f03ef#32), -- mov x15, xzr
  (2248, 0xf10005cb#32), -- subs x11, x14, #0x1
  (2252, 0xfa1f01ec#32), -- sbcs x12, x15, xzr
  (2256, 0x9a8c33ec#32), -- csel x12, xzr, x12, lo
  (2260, 0x9a8b33eb#32), -- csel x11, xzr, x11, lo
  (2264, 0xca0c014c#32), -- eor x12, x10, x12
  (2268, 0xca0b012b#32), -- eor x11, x9, x11
  (2272, 0xaa0c016b#32), -- orr x11, x11, x12
  (2276, 0xf100017f#32), -- cmp x11, #0x0
  (2280, 0x54000060#32), -- b.eq 0x242d58 <.Llower_arm_1065>
  (2284, 0xaa1603f6#32), -- mov x22, x22
  (2288, 0x14000002#32), -- b 0x242d5c <.Llower_arm_1066>
  (2292, 0x910006d6#32), -- add x22, x22, #0x1
  (2296, 0x9a8a03f4#32), -- csel x20, xzr, x10, eq
  (2300, 0x9a8903f3#32) -- csel x19, xzr, x9, eq
]

theorem chunk8_decodes :
    chunk8.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk9 : List (Nat × BitVec 32) := [
  (2304, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2308, 0xf90003e9#32), -- str x9, [sp]
  (2312, 0x12000109#32), -- and w9, w8, #0x1
  (2316, 0x35000089#32), -- cbnz w9, 0x242d80 <.Llower_arm_1067>
  (2320, 0xf94003e9#32), -- ldr x9, [sp]
  (2324, 0x910043ff#32), -- add sp, sp, #0x10
  (2328, 0x14000004#32), -- b 0x242d8c <.Llower_arm_1068>
  (2332, 0xf94003e9#32), -- ldr x9, [sp]
  (2336, 0x910043ff#32), -- add sp, sp, #0x10
  (2340, 0x140000f7#32), -- b 0x243164 <.LBB125_126>
  (2344, 0xf9401fe8#32), -- ldr x8, [sp, #0x38]
  (2348, 0xf90043f4#32), -- str x20, [sp, #0x80]
  (2352, 0xeb0802df#32), -- cmp x22, x8
  (2356, 0x54002d82#32), -- b.hs 0x243348 <.LBB125_140>
  (2360, 0x8b161308#32), -- add x8, x24, x22, lsl #4
  (2364, 0xaa1303fb#32), -- mov x27, x19
  (2368, 0xf9003ff6#32), -- str x22, [sp, #0x78]
  (2372, 0xa9400901#32), -- ldp x1, x2, [x8]
  (2376, 0xb40002a1#32), -- cbz x1, 0x242e00 <.LBB125_100>
  (2380, 0xd1002029#32), -- sub x9, x1, #0x8
  (2384, 0xaa0203eb#32), -- mov x11, x2
  (2388, 0xb40005ab#32), -- cbz x11, 0x242e6c <.LBB125_102>
  (2392, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2396, 0xf90003ea#32), -- str x10, [sp]
  (2400, 0xaa0b03ea#32), -- mov x10, x11
  (2404, 0xd37df14a#32), -- lsl x10, x10, #3
  (2408, 0x8b0a012a#32), -- add x10, x9, x10
  (2412, 0xf9400148#32), -- ldr x8, [x10]
  (2416, 0xf94003ea#32), -- ldr x10, [sp]
  (2420, 0x910043ff#32), -- add sp, sp, #0x10
  (2424, 0xaa0b03ea#32), -- mov x10, x11
  (2428, 0xd100056b#32), -- sub x11, x11, #0x1
  (2432, 0xb4fffea8#32), -- cbz x8, 0x242db8 <.LBB125_97>
  (2436, 0xd37ae549#32), -- lsl x9, x10, #6
  (2440, 0xd37afd4a#32), -- lsr x10, x10, #58
  (2444, 0x9280000b#32), -- mov x11, #-0x1 // =-1
  (2448, 0xf1010129#32), -- subs x9, x9, #0x40
  (2452, 0x9a0b014a#32), -- adc x10, x10, x11
  (2456, 0x14000007#32), -- b 0x242e18 <.LBB125_101>
  (2460, 0xaa1f03e9#32), -- mov x9, xzr
  (2464, 0xaa1f03ea#32), -- mov x10, xzr
  (2468, 0xaa1f03eb#32), -- mov x11, xzr
  (2472, 0xaa1f03ec#32), -- mov x12, xzr
  (2476, 0xaa0203e8#32), -- mov x8, x2
  (2480, 0xb40002e2#32), -- cbz x2, 0x242e70 <.LBB125_103>
  (2484, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2488, 0xf90003e9#32), -- str x9, [sp]
  (2492, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2496, 0xaa0803e9#32), -- mov x9, x8
  (2500, 0xd280080a#32), -- mov x10, #0x40 // =64
  (2504, 0xb4000089#32), -- cbz x9, 0x242e3c <.Llower_arm_1070>
  (2508, 0xd100054a#32), -- sub x10, x10, #0x1
  (2512, 0xd341fd29#32), -- lsr x9, x9, #1
  (2516, 0xb5ffffc9#32), -- cbnz x9, 0x242e30 <.Llower_arm_1069>
  (2520, 0xaa0a03e8#32), -- mov x8, x10
  (2524, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (2528, 0xf94003e9#32), -- ldr x9, [sp]
  (2532, 0x910043ff#32), -- add sp, sp, #0x10
  (2536, 0x5280080b#32), -- mov w11, #0x40 // =64
  (2540, 0x4b080168#32), -- sub w8, w11, w8
  (2544, 0xab08012b#32), -- adds x11, x9, x8
  (2548, 0x54000062#32), -- b.hs 0x242e64 <.Llower_arm_1071>
  (2552, 0xaa0a03ec#32), -- mov x12, x10
  (2556, 0x14000002#32) -- b 0x242e68 <.Llower_arm_1072>
]

theorem chunk9_decodes :
    chunk9.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk10 : List (Nat × BitVec 32) := [
  (2560, 0x9100054c#32), -- add x12, x10, #0x1
  (2564, 0x14000002#32), -- b 0x242e70 <.LBB125_103>
  (2568, 0xaa1f03ec#32), -- mov x12, xzr
  (2572, 0xf1000568#32), -- subs x8, x11, #0x1
  (2576, 0xaa1f03f3#32), -- mov x19, xzr
  (2580, 0xaa1803f5#32), -- mov x21, x24
  (2584, 0xfa1f0189#32), -- sbcs x9, x12, xzr
  (2588, 0x9a8833e8#32), -- csel x8, xzr, x8, lo
  (2592, 0x9a8933e9#32), -- csel x9, xzr, x9, lo
  (2596, 0xeb1b0114#32), -- subs x20, x8, x27
  (2600, 0xf94043e8#32), -- ldr x8, [sp, #0x80]
  (2604, 0xda080136#32), -- sbc x22, x9, x8
  (2608, 0x14000006#32), -- b 0x242eac <.LBB125_105>
  (2612, 0xf94047e8#32), -- ldr x8, [sp, #0x88]
  (2616, 0x910042b5#32), -- add x21, x21, #0x10
  (2620, 0x91000673#32), -- add x19, x19, #0x1
  (2624, 0xeb0802bf#32), -- cmp x21, x8
  (2628, 0x54000d80#32), -- b.eq 0x243058 <.LBB125_118>
  (2632, 0xa9405eb8#32), -- ldp x24, x23, [x21]
  (2636, 0xb40002b8#32), -- cbz x24, 0x242f04 <.LBB125_110>
  (2640, 0xd1002309#32), -- sub x9, x24, #0x8
  (2644, 0xaa1703eb#32), -- mov x11, x23
  (2648, 0xb40005ab#32), -- cbz x11, 0x242f70 <.LBB125_112>
  (2652, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2656, 0xf90003ea#32), -- str x10, [sp]
  (2660, 0xaa0b03ea#32), -- mov x10, x11
  (2664, 0xd37df14a#32), -- lsl x10, x10, #3
  (2668, 0x8b0a012a#32), -- add x10, x9, x10
  (2672, 0xf9400148#32), -- ldr x8, [x10]
  (2676, 0xf94003ea#32), -- ldr x10, [sp]
  (2680, 0x910043ff#32), -- add sp, sp, #0x10
  (2684, 0xaa0b03ea#32), -- mov x10, x11
  (2688, 0xd100056b#32), -- sub x11, x11, #0x1
  (2692, 0xb4fffea8#32), -- cbz x8, 0x242ebc <.LBB125_107>
  (2696, 0xd37ae549#32), -- lsl x9, x10, #6
  (2700, 0xd37afd4a#32), -- lsr x10, x10, #58
  (2704, 0x9280000b#32), -- mov x11, #-0x1 // =-1
  (2708, 0xf1010129#32), -- subs x9, x9, #0x40
  (2712, 0x9a0b014a#32), -- adc x10, x10, x11
  (2716, 0x14000007#32), -- b 0x242f1c <.LBB125_111>
  (2720, 0xaa1f03e9#32), -- mov x9, xzr
  (2724, 0xaa1f03ea#32), -- mov x10, xzr
  (2728, 0xaa1f03eb#32), -- mov x11, xzr
  (2732, 0xaa1f03ec#32), -- mov x12, xzr
  (2736, 0xaa1703e8#32), -- mov x8, x23
  (2740, 0xb40002f7#32), -- cbz x23, 0x242f74 <.LBB125_113>
  (2744, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2748, 0xf90003e9#32), -- str x9, [sp]
  (2752, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2756, 0xaa0803e9#32), -- mov x9, x8
  (2760, 0xd280080a#32), -- mov x10, #0x40 // =64
  (2764, 0xb4000089#32), -- cbz x9, 0x242f40 <.Llower_arm_1074>
  (2768, 0xd100054a#32), -- sub x10, x10, #0x1
  (2772, 0xd341fd29#32), -- lsr x9, x9, #1
  (2776, 0xb5ffffc9#32), -- cbnz x9, 0x242f34 <.Llower_arm_1073>
  (2780, 0xaa0a03e8#32), -- mov x8, x10
  (2784, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (2788, 0xf94003e9#32), -- ldr x9, [sp]
  (2792, 0x910043ff#32), -- add sp, sp, #0x10
  (2796, 0x5280080b#32), -- mov w11, #0x40 // =64
  (2800, 0x4b080168#32), -- sub w8, w11, w8
  (2804, 0xab08012b#32), -- adds x11, x9, x8
  (2808, 0x54000062#32), -- b.hs 0x242f68 <.Llower_arm_1075>
  (2812, 0xaa0a03ec#32) -- mov x12, x10
]

theorem chunk10_decodes :
    chunk10.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk11 : List (Nat × BitVec 32) := [
  (2816, 0x14000002#32), -- b 0x242f6c <.Llower_arm_1076>
  (2820, 0x9100054c#32), -- add x12, x10, #0x1
  (2824, 0x14000002#32), -- b 0x242f74 <.LBB125_113>
  (2828, 0xaa1f03ec#32), -- mov x12, xzr
  (2832, 0xf1000568#32), -- subs x8, x11, #0x1
  (2836, 0xfa1f018a#32), -- sbcs x10, x12, xzr
  (2840, 0x9a8833e9#32), -- csel x9, xzr, x8, lo
  (2844, 0x9a8a33e8#32), -- csel x8, xzr, x10, lo
  (2848, 0xeb14013f#32), -- cmp x9, x20
  (2852, 0xfa16011f#32), -- sbcs xzr, x8, x22
  (2856, 0x54fff863#32), -- b.lo 0x242e98 <.LBB125_104>
  (2860, 0xeb140139#32), -- subs x25, x9, x20
  (2864, 0xf94043e3#32), -- ldr x3, [sp, #0x80]
  (2868, 0xaa0103fa#32), -- mov x26, x1
  (2872, 0xda16011d#32), -- sbc x29, x8, x22
  (2876, 0xaa0103e0#32), -- mov x0, x1
  (2880, 0xaa0203fc#32), -- mov x28, x2
  (2884, 0xaa0203e1#32), -- mov x1, x2
  (2888, 0xaa1b03e2#32), -- mov x2, x27
  (2892, 0x52800024#32), -- mov w4, #0x1 // =1
  (2896, 0xaa1803e5#32), -- mov x5, x24
  (2900, 0xaa1703e6#32), -- mov x6, x23
  (2904, 0xa90077f9#32), -- stp x25, x29, [sp]
  (2908, 0x940000ed#32), -- bl 0x243374 <_ZN13ssz_fv_native7indices12prefix_equal17h455af9025a76ffe0E>
  (2912, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2916, 0xf90003e9#32), -- str x9, [sp]
  (2920, 0x12000009#32), -- and w9, w0, #0x1
  (2924, 0x35000089#32), -- cbnz w9, 0x242fe0 <.Llower_arm_1077>
  (2928, 0xf94003e9#32), -- ldr x9, [sp]
  (2932, 0x910043ff#32), -- add sp, sp, #0x10
  (2936, 0x14000004#32), -- b 0x242fec <.Llower_arm_1078>
  (2940, 0xf94003e9#32), -- ldr x9, [sp]
  (2944, 0x910043ff#32), -- add sp, sp, #0x10
  (2948, 0x14000039#32), -- b 0x2430cc <.LBB125_123>
  (2952, 0xf9403fe8#32), -- ldr x8, [sp, #0x78]
  (2956, 0xaa1c03e2#32), -- mov x2, x28
  (2960, 0xaa1a03e1#32), -- mov x1, x26
  (2964, 0xeb08027f#32), -- cmp x19, x8
  (2968, 0x54fff4e2#32), -- b.hs 0x242e98 <.LBB125_104>
  (2972, 0xf94043e3#32), -- ldr x3, [sp, #0x80]
  (2976, 0x2a1f03e4#32), -- mov w4, wzr
  (2980, 0xaa0103e0#32), -- mov x0, x1
  (2984, 0xaa0203e1#32), -- mov x1, x2
  (2988, 0xaa1b03e2#32), -- mov x2, x27
  (2992, 0xaa1803e5#32), -- mov x5, x24
  (2996, 0xaa1703e6#32), -- mov x6, x23
  (3000, 0xa90077f9#32), -- stp x25, x29, [sp]
  (3004, 0x940000d5#32), -- bl 0x243374 <_ZN13ssz_fv_native7indices12prefix_equal17h455af9025a76ffe0E>
  (3008, 0xaa1a03e1#32), -- mov x1, x26
  (3012, 0xaa1c03e2#32), -- mov x2, x28
  (3016, 0x34fff360#32), -- cbz w0, 0x242e98 <.LBB125_104>
  (3020, 0x2a1f03e8#32), -- mov w8, wzr
  (3024, 0xf94033f8#32), -- ldr x24, [sp, #0x60]
  (3028, 0xa947abf6#32), -- ldp x22, x10, [sp, #0x78]
  (3032, 0xb1000769#32), -- adds x9, x27, #0x1
  (3036, 0x54000062#32), -- b.hs 0x24304c <.Llower_arm_1079>
  (3040, 0xaa0a03ea#32), -- mov x10, x10
  (3044, 0x14000002#32), -- b 0x243050 <.Llower_arm_1080>
  (3048, 0x9100054a#32), -- add x10, x10, #0x1
  (3052, 0xb5000161#32), -- cbnz x1, 0x24307c <.LBB125_119>
  (3056, 0x14000029#32), -- b 0x2430f8 <.LBB125_124>
  (3060, 0x52800028#32), -- mov w8, #0x1 // =1
  (3064, 0xf94033f8#32), -- ldr x24, [sp, #0x60]
  (3068, 0xa947abf6#32) -- ldp x22, x10, [sp, #0x78]
]

theorem chunk11_decodes :
    chunk11.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk12 : List (Nat × BitVec 32) := [
  (3072, 0xb1000769#32), -- adds x9, x27, #0x1
  (3076, 0x54000062#32), -- b.hs 0x243074 <.Llower_arm_1081>
  (3080, 0xaa0a03ea#32), -- mov x10, x10
  (3084, 0x14000002#32), -- b 0x243078 <.Llower_arm_1082>
  (3088, 0x9100054a#32), -- add x10, x10, #0x1
  (3092, 0xb4000401#32), -- cbz x1, 0x2430f8 <.LBB125_124>
  (3096, 0xd100202c#32), -- sub x12, x1, #0x8
  (3100, 0xaa0203ee#32), -- mov x14, x2
  (3104, 0xb4ffe52e#32), -- cbz x14, 0x242d28 <.LBB125_92>
  (3108, 0xd10043ff#32), -- sub sp, sp, #0x10
  (3112, 0xf90003e9#32), -- str x9, [sp]
  (3116, 0xaa0e03e9#32), -- mov x9, x14
  (3120, 0xd37df129#32), -- lsl x9, x9, #3
  (3124, 0x8b090189#32), -- add x9, x12, x9
  (3128, 0xf940012b#32), -- ldr x11, [x9]
  (3132, 0xf94003e9#32), -- ldr x9, [sp]
  (3136, 0x910043ff#32), -- add sp, sp, #0x10
  (3140, 0xaa0e03ed#32), -- mov x13, x14
  (3144, 0xd10005ce#32), -- sub x14, x14, #0x1
  (3148, 0xb4fffeab#32), -- cbz x11, 0x243084 <.LBB125_120>
  (3152, 0xd37ae5ac#32), -- lsl x12, x13, #6
  (3156, 0xd37afdad#32), -- lsr x13, x13, #58
  (3160, 0x9280000e#32), -- mov x14, #-0x1 // =-1
  (3164, 0xf101018c#32), -- subs x12, x12, #0x40
  (3168, 0x9a0e01ad#32), -- adc x13, x13, x14
  (3172, 0x14000012#32), -- b 0x243110 <.LBB125_125>
  (3176, 0xf94033f8#32), -- ldr x24, [sp, #0x60]
  (3180, 0x2a1f03e8#32), -- mov w8, wzr
  (3184, 0xaa1c03e2#32), -- mov x2, x28
  (3188, 0xaa1a03e1#32), -- mov x1, x26
  (3192, 0xa947abf6#32), -- ldp x22, x10, [sp, #0x78]
  (3196, 0xb1000769#32), -- adds x9, x27, #0x1
  (3200, 0x54000062#32), -- b.hs 0x2430f0 <.Llower_arm_1083>
  (3204, 0xaa0a03ea#32), -- mov x10, x10
  (3208, 0x14000002#32), -- b 0x2430f4 <.Llower_arm_1084>
  (3212, 0x9100054a#32), -- add x10, x10, #0x1
  (3216, 0xb5fffc5a#32), -- cbnz x26, 0x24307c <.LBB125_119>
  (3220, 0xaa1f03ec#32), -- mov x12, xzr
  (3224, 0xaa1f03ed#32), -- mov x13, xzr
  (3228, 0xaa1f03ee#32), -- mov x14, xzr
  (3232, 0xaa1f03ef#32), -- mov x15, xzr
  (3236, 0xaa0203eb#32), -- mov x11, x2
  (3240, 0xb4ffe102#32), -- cbz x2, 0x242d2c <.LBB125_93>
  (3244, 0xd10043ff#32), -- sub sp, sp, #0x10
  (3248, 0xf90003e9#32), -- str x9, [sp]
  (3252, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (3256, 0xaa0b03e9#32), -- mov x9, x11
  (3260, 0xd280080a#32), -- mov x10, #0x40 // =64
  (3264, 0xb4000089#32), -- cbz x9, 0x243134 <.Llower_arm_1086>
  (3268, 0xd100054a#32), -- sub x10, x10, #0x1
  (3272, 0xd341fd29#32), -- lsr x9, x9, #1
  (3276, 0xb5ffffc9#32), -- cbnz x9, 0x243128 <.Llower_arm_1085>
  (3280, 0xaa0a03eb#32), -- mov x11, x10
  (3284, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (3288, 0xf94003e9#32), -- ldr x9, [sp]
  (3292, 0x910043ff#32), -- add sp, sp, #0x10
  (3296, 0x5280080e#32), -- mov w14, #0x40 // =64
  (3300, 0x4b0b01cb#32), -- sub w11, w14, w11
  (3304, 0xab0b018e#32), -- adds x14, x12, x11
  (3308, 0x54000062#32), -- b.hs 0x24315c <.Llower_arm_1087>
  (3312, 0xaa0d03ef#32), -- mov x15, x13
  (3316, 0x14000002#32), -- b 0x243160 <.Llower_arm_1088>
  (3320, 0x910005af#32), -- add x15, x13, #0x1
  (3324, 0x17fffef3#32) -- b 0x242d2c <.LBB125_93>
]

theorem chunk12_decodes :
    chunk12.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk13 : List (Nat × BitVec 32) := [
  (3328, 0xf94043e5#32), -- ldr x5, [sp, #0x80]
  (3332, 0xf94017e6#32), -- ldr x6, [sp, #0x28]
  (3336, 0x910323e0#32), -- add x0, sp, #0xc8
  (3340, 0xaa1b03e4#32), -- mov x4, x27
  (3344, 0x97fffa01#32), -- bl 0x241978 <_ZN13ssz_fv_native7indices9shift_xor17h45a956e38b065bb1E>
  (3348, 0xb9410bf5#32), -- ldr w21, [sp, #0x108]
  (3352, 0x350005d5#32), -- cbnz w21, 0x243234 <.LBB125_136>
  (3356, 0xa946abf5#32), -- ldp x21, x10, [sp, #0x68]
  (3360, 0xf9402fec#32), -- ldr x12, [sp, #0x58]
  (3364, 0xa94cafe8#32), -- ldp x8, x11, [sp, #0xc8]
  (3368, 0x8b0a12a9#32), -- add x9, x21, x10, lsl #4
  (3372, 0x9100054a#32), -- add x10, x10, #0x1
  (3376, 0xeb0c015f#32), -- cmp x10, x12
  (3380, 0xa9002d28#32), -- stp x8, x11, [x9]
  (3384, 0xaa0a03eb#32), -- mov x11, x10
  (3388, 0x54ffdc01#32), -- b.ne 0x242d20 <.LBB125_91>
  (3392, 0xf9402fe8#32), -- ldr x8, [sp, #0x58]
  (3396, 0xf100051f#32), -- cmp x8, #0x1
  (3400, 0x54000bc1#32), -- b.ne 0x243324 <.LBB125_138>
  (3404, 0x52800033#32), -- mov w19, #0x1 // =1
  (3408, 0xf94013f7#32), -- ldr x23, [sp, #0x20]
  (3412, 0x14000013#32), -- b 0x243204 <.LBB125_135>
  (3416, 0xaa1f03e0#32), -- mov x0, xzr
  (3420, 0xaa1403e2#32), -- mov x2, x20
  (3424, 0x97ff6bdf#32), -- bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>
  (3428, 0x6f00e400#32), -- movi v0.2d, #0000000000000000
  (3432, 0xaa1f03f3#32), -- mov x19, xzr
  (3436, 0x52900015#32), -- mov w21, #0x8000 // =32768
  (3440, 0x52800034#32), -- mov w20, #0x1 // =1
  (3444, 0xad0503e0#32), -- stp q0, q0, [sp, #0xa0]
  (3448, 0x3d8027e0#32), -- str q0, [sp, #0x90]
  (3452, 0x910042e0#32), -- add x0, x23, #0x10
  (3456, 0x910243e1#32), -- add x1, sp, #0x90
  (3460, 0x52800602#32), -- mov w2, #0x30 // =48
  (3464, 0xa9004ef4#32), -- stp x20, x19, [x23]
  (3468, 0x940028b8#32), -- bl 0x24d4d0 <memcpy>
  (3472, 0x29085af5#32), -- stp w21, w22, [x23, #0x40]
  (3476, 0x17fffd9d#32), -- b 0x24286c <.LBB125_45>
  (3480, 0xaa1f03f3#32), -- mov x19, xzr
  (3484, 0x52800115#32), -- mov w21, #0x8 // =8
  (3488, 0xa9004ef5#32), -- stp x21, x19, [x23]
  (3492, 0xd10043ff#32), -- sub sp, sp, #0x10
  (3496, 0xf90003e9#32), -- str x9, [sp]
  (3500, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (3504, 0x910002e9#32), -- add x9, x23, #0x0
  (3508, 0x91010129#32), -- add x9, x9, #0x40
  (3512, 0x5280000a#32), -- mov w10, #0x0 // =0
  (3516, 0xb900012a#32), -- str w10, [x9]
  (3520, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (3524, 0xf94003e9#32), -- ldr x9, [sp]
  (3528, 0x910043ff#32), -- add sp, sp, #0x10
  (3532, 0x17fffd8f#32), -- b 0x24286c <.LBB125_45>
  (3536, 0xa94ccff4#32), -- ldp x20, x19, [sp, #0xc8]
  (3540, 0x910323e8#32), -- add x8, sp, #0xc8
  (3544, 0x910243e0#32), -- add x0, sp, #0x90
  (3548, 0x91004101#32), -- add x1, x8, #0x10
  (3552, 0x52800602#32), -- mov w2, #0x30 // =48
  (3556, 0x940028a2#32), -- bl 0x24d4d0 <memcpy>
  (3560, 0xb9410ff6#32), -- ldr w22, [sp, #0x10c]
  (3564, 0xf94013f7#32), -- ldr x23, [sp, #0x20]
  (3568, 0x17ffffe3#32), -- b 0x2431e0 <.LBB125_133>
  (3572, 0xf94013e9#32), -- ldr x9, [sp, #0x20]
  (3576, 0x52800028#32), -- mov w8, #0x1 // =1
  (3580, 0xd10043ff#32) -- sub sp, sp, #0x10
]

theorem chunk13_decodes :
    chunk13.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk14 : List (Nat × BitVec 32) := [
  (3584, 0xf90003ea#32), -- str x10, [sp]
  (3588, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (3592, 0x9100012a#32), -- add x10, x9, #0x0
  (3596, 0xf9000148#32), -- str x8, [x10]
  (3600, 0xd280000b#32), -- mov x11, #0x0 // =0
  (3604, 0xf900054b#32), -- str x11, [x10, #0x8]
  (3608, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (3612, 0xf94003ea#32), -- ldr x10, [sp]
  (3616, 0x910043ff#32), -- add sp, sp, #0x10
  (3620, 0x52900008#32), -- mov w8, #0x8000 // =32768
  (3624, 0xd10043ff#32), -- sub sp, sp, #0x10
  (3628, 0xf90003ea#32), -- str x10, [sp]
  (3632, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (3636, 0x9100012a#32), -- add x10, x9, #0x0
  (3640, 0x9100414a#32), -- add x10, x10, #0x10
  (3644, 0xd280000b#32), -- mov x11, #0x0 // =0
  (3648, 0xf900014b#32), -- str x11, [x10]
  (3652, 0xd280000b#32), -- mov x11, #0x0 // =0
  (3656, 0xf900054b#32), -- str x11, [x10, #0x8]
  (3660, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (3664, 0xf94003ea#32), -- ldr x10, [sp]
  (3668, 0x910043ff#32), -- add sp, sp, #0x10
  (3672, 0xd10043ff#32), -- sub sp, sp, #0x10
  (3676, 0xf90003ea#32), -- str x10, [sp]
  (3680, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (3684, 0x9100012a#32), -- add x10, x9, #0x0
  (3688, 0x9100814a#32), -- add x10, x10, #0x20
  (3692, 0xd280000b#32), -- mov x11, #0x0 // =0
  (3696, 0xf900014b#32), -- str x11, [x10]
  (3700, 0xd280000b#32), -- mov x11, #0x0 // =0
  (3704, 0xf900054b#32), -- str x11, [x10, #0x8]
  (3708, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (3712, 0xf94003ea#32), -- ldr x10, [sp]
  (3716, 0x910043ff#32), -- add sp, sp, #0x10
  (3720, 0xd10043ff#32), -- sub sp, sp, #0x10
  (3724, 0xf90003ea#32), -- str x10, [sp]
  (3728, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (3732, 0x9100012a#32), -- add x10, x9, #0x0
  (3736, 0x9100c14a#32), -- add x10, x10, #0x30
  (3740, 0xd280000b#32), -- mov x11, #0x0 // =0
  (3744, 0xf900014b#32), -- str x11, [x10]
  (3748, 0xd280000b#32), -- mov x11, #0x0 // =0
  (3752, 0xf900054b#32), -- str x11, [x10, #0x8]
  (3756, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (3760, 0xf94003ea#32), -- ldr x10, [sp]
  (3764, 0x910043ff#32), -- add sp, sp, #0x10
  (3768, 0xb9004128#32), -- str w8, [x9, #0x40]
  (3772, 0x17fffd53#32), -- b 0x24286c <.LBB125_45>
  (3776, 0xf9402fe8#32), -- ldr x8, [sp, #0x58]
  (3780, 0xf100551f#32), -- cmp x8, #0x15
  (3784, 0x54000182#32), -- b.hs 0x24335c <.LBB125_142>
  (3788, 0xf94037f5#32), -- ldr x21, [sp, #0x68]
  (3792, 0xf9402ff3#32), -- ldr x19, [sp, #0x58]
  (3796, 0xaa1503e0#32), -- mov x0, x21
  (3800, 0xaa1303e1#32), -- mov x1, x19
  (3804, 0x94000202#32), -- bl 0x243b48 <_ZN4core5slice4sort6shared9smallsort25insertion_sort_shift_left17hedcf71437a340f54E>
  (3808, 0x17ffff9c#32), -- b 0x2431b4 <.LBB125_130>
  (3812, 0xf9401fe1#32), -- ldr x1, [sp, #0x38]
  (3816, 0xaa1603e0#32), -- mov x0, x22
  (3820, 0x97ff6b88#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (3824, 0xf9401fe1#32), -- ldr x1, [sp, #0x38]
  (3828, 0x97ff6b86#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (3832, 0xf94037f5#32), -- ldr x21, [sp, #0x68]
  (3836, 0xf9402ff3#32) -- ldr x19, [sp, #0x58]
]

theorem chunk14_decodes :
    chunk14.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk15 : List (Nat × BitVec 32) := [
  (3840, 0xaa1503e0#32), -- mov x0, x21
  (3844, 0xaa1303e1#32), -- mov x1, x19
  (3848, 0x94000189#32), -- bl 0x243990 <_ZN4core5slice4sort8unstable7ipnsort17h2a30cf48fed7d7bfE>
  (3852, 0x17ffff91#32) -- b 0x2431b4 <.LBB125_130>
]

theorem chunk15_decodes :
    chunk15.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete linked function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 ++ chunk8 ++ chunk9 ++ chunk10 ++ chunk11 ++ chunk12 ++ chunk13 ++ chunk14 ++ chunk15

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

theorem chunk8_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk8 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk9_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk9 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk10_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk10 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk11_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk11 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk12_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk12 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk13_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk13 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk14_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk14 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem chunk15_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk15 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  aesop

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, chunk3_decodes, chunk4_decodes, chunk5_decodes, chunk6_decodes, chunk7_decodes, chunk8_decodes, chunk9_decodes, chunk10_decodes, chunk11_decodes, chunk12_decodes, chunk13_decodes, chunk14_decodes, chunk15_decodes, Bool.and_self]

theorem step_at (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (row : Nat × BitVec 32) (member : row ∈ program)
    (entry : read_pc s = base + BitVec.ofNat 64 row.1)
    (error : read_err s = .None) :
    stepi s = exec_inst (SszArm.Codec.Linked.decoded program all_decode row member) s :=
  SszArm.Codec.Linked.step_at program all_decode s base code row member entry error

end SszArm.Indices.Linked.HelperIndices
