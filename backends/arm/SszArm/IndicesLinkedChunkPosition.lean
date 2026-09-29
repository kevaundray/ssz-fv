import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.ChunkPosition

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN13ssz_fv_native7indices14chunk_position17he9da7fe78b73f603E. -/
def address : Nat := 2258116

def byteSize : Nat := 2172

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10503ff#32), -- sub sp, sp, #0x140
  (4, 0xa90f7bfd#32), -- stp x29, x30, [sp, #0xf0]
  (8, 0xa91067fa#32), -- stp x26, x25, [sp, #0x100]
  (12, 0xa9115ff8#32), -- stp x24, x23, [sp, #0x110]
  (16, 0xa91257f6#32), -- stp x22, x21, [sp, #0x120]
  (20, 0xa9134ff4#32), -- stp x20, x19, [sp, #0x130]
  (24, 0xaa0003f3#32), -- mov x19, x0
  (28, 0x910263e0#32), -- add x0, sp, #0x98
  (32, 0xaa0303f6#32), -- mov x22, x3
  (36, 0xaa0203f7#32), -- mov x23, x2
  (40, 0xaa0103f9#32), -- mov x25, x1
  (44, 0x94000214#32), -- bl 0x227d40 <_ZN13ssz_fv_native7indices12element_type17hc2546e08b1adae5eE>
  (48, 0xa949d3e8#32), -- ldp x8, x20, [sp, #0x98]
  (52, 0xb940dbe9#32), -- ldr w9, [sp, #0xd8]
  (56, 0xf94057f5#32), -- ldr x21, [sp, #0xa8]
  (60, 0x34000189#32), -- cbz w9, 0x227530 <.LBB57_2>
  (64, 0xa94bafea#32), -- ldp x10, x11, [sp, #0xb8]
  (68, 0xa900d674#32), -- stp x20, x21, [x19, #0x8]
  (72, 0xf9000268#32), -- str x8, [x19]
  (76, 0xa9022e6a#32), -- stp x10, x11, [x19, #0x20]
  (80, 0xa94cabec#32), -- ldp x12, x10, [sp, #0xc8]
  (84, 0xf9405beb#32), -- ldr x11, [sp, #0xb0]
  (88, 0xa9032a6c#32), -- stp x12, x10, [x19, #0x30]
  (92, 0xb940dfea#32), -- ldr w10, [sp, #0xdc]
  (96, 0xf9000e6b#32), -- str x11, [x19, #0x18]
  (100, 0x29082a69#32), -- stp w9, w10, [x19, #0x40]
  (104, 0x14000075#32), -- b 0x227700 <.LBB57_21>
  (108, 0xf100051f#32), -- cmp x8, #0x1
  (112, 0x54000080#32), -- b.eq 0x227544 <.LBB57_5>
  (116, 0xaa1f03f4#32), -- mov x20, xzr
  (120, 0xb50003e8#32), -- cbnz x8, 0x2275b8 <.LBB57_13>
  (124, 0x52800035#32), -- mov w21, #0x1 // =1
  (128, 0xf940033a#32), -- ldr x26, [x25]
  (132, 0xf94002e8#32), -- ldr x8, [x23]
  (136, 0xf1002b5f#32), -- cmp x26, #0xa
  (140, 0x540003e0#32), -- b.eq 0x2275cc <.LBB57_14>
  (144, 0xf1002f5f#32), -- cmp x26, #0xb
  (148, 0x54000701#32), -- b.ne 0x227638 <.LBB57_17>
  (152, 0xb5000708#32), -- cbnz x8, 0x22763c <.LBB57_18>
  (156, 0xa940a6e8#32), -- ldp x8, x9, [x23, #0x8]
  (160, 0xa940af2a#32), -- ldp x10, x11, [x25, #0x8]
  (164, 0xaa0903ec#32), -- mov x12, x9
  (168, 0xb4001888#32), -- cbz x8, 0x22787c <.LBB57_38>
  (172, 0xd100052d#32), -- sub x13, x9, #0x1
  (176, 0xb10005bf#32), -- cmn x13, #0x1
  (180, 0x540011a0#32), -- b.eq 0x2277ac <.LBB57_26>
  (184, 0xd10043ff#32), -- sub sp, sp, #0x10
  (188, 0xf90003e9#32), -- str x9, [sp]
  (192, 0xaa0d03e9#32), -- mov x9, x13
  (196, 0xd37df129#32), -- lsl x9, x9, #3
  (200, 0x8b090109#32), -- add x9, x8, x9
  (204, 0xf940012e#32), -- ldr x14, [x9]
  (208, 0xf94003e9#32), -- ldr x9, [sp]
  (212, 0x910043ff#32), -- add sp, sp, #0x10
  (216, 0xaa0d03ec#32), -- mov x12, x13
  (220, 0xd10005ad#32), -- sub x13, x13, #0x1
  (224, 0xb4fffe8e#32), -- cbz x14, 0x227574 <.LBB57_10>
  (228, 0x9100058c#32), -- add x12, x12, #0x1
  (232, 0xf100059f#32), -- cmp x12, #0x1
  (236, 0x54001000#32), -- b.eq 0x2277b0 <.LBB57_27>
  (240, 0x140000cc#32), -- b 0x2278e4 <.LBB57_44>
  (244, 0x52800415#32), -- mov w21, #0x20 // =32
  (248, 0xf940033a#32), -- ldr x26, [x25]
  (252, 0xf94002e8#32) -- ldr x8, [x23]
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0xf1002b5f#32), -- cmp x26, #0xa
  (260, 0x54fffc61#32), -- b.ne 0x227554 <.LBB57_6>
  (264, 0xb5000388#32), -- cbnz x8, 0x22763c <.LBB57_18>
  (268, 0xa940a6e8#32), -- ldp x8, x9, [x23, #0x8]
  (272, 0xd10043ff#32), -- sub sp, sp, #0x10
  (276, 0xf90003e9#32), -- str x9, [sp]
  (280, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (284, 0x91000269#32), -- add x9, x19, #0x0
  (288, 0x91004129#32), -- add x9, x9, #0x10
  (292, 0xd280000a#32), -- mov x10, #0x0 // =0
  (296, 0xf900012a#32), -- str x10, [x9]
  (300, 0xd280000a#32), -- mov x10, #0x0 // =0
  (304, 0xf900052a#32), -- str x10, [x9, #0x8]
  (308, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (312, 0xf94003e9#32), -- ldr x9, [sp]
  (316, 0x910043ff#32), -- add sp, sp, #0x10
  (320, 0xa9025674#32), -- stp x20, x21, [x19, #0x20]
  (324, 0xa9002668#32), -- stp x8, x9, [x19]
  (328, 0xd10043ff#32), -- sub sp, sp, #0x10
  (332, 0xf90003e9#32), -- str x9, [sp]
  (336, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (340, 0x91000269#32), -- add x9, x19, #0x0
  (344, 0x91010129#32), -- add x9, x9, #0x40
  (348, 0x5280000a#32), -- mov w10, #0x0 // =0
  (352, 0xb900012a#32), -- str w10, [x9]
  (356, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (360, 0xf94003e9#32), -- ldr x9, [sp]
  (364, 0x910043ff#32), -- add sp, sp, #0x10
  (368, 0x14000033#32), -- b 0x227700 <.LBB57_21>
  (372, 0xb4000728#32), -- cbz x8, 0x22771c <.LBB57_22>
  (376, 0x52800028#32), -- mov w8, #0x1 // =1
  (380, 0xd10043ff#32), -- sub sp, sp, #0x10
  (384, 0xf90003e9#32), -- str x9, [sp]
  (388, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (392, 0x91000269#32), -- add x9, x19, #0x0
  (396, 0x91004129#32), -- add x9, x9, #0x10
  (400, 0xd280000a#32), -- mov x10, #0x0 // =0
  (404, 0xf900012a#32), -- str x10, [x9]
  (408, 0xd280000a#32), -- mov x10, #0x0 // =0
  (412, 0xf900052a#32), -- str x10, [x9, #0x8]
  (416, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (420, 0xf94003e9#32), -- ldr x9, [sp]
  (424, 0x910043ff#32), -- add sp, sp, #0x10
  (428, 0xd10043ff#32), -- sub sp, sp, #0x10
  (432, 0xf90003e9#32), -- str x9, [sp]
  (436, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (440, 0x91000269#32), -- add x9, x19, #0x0
  (444, 0xf9000128#32), -- str x8, [x9]
  (448, 0xd280000a#32), -- mov x10, #0x0 // =0
  (452, 0xf900052a#32), -- str x10, [x9, #0x8]
  (456, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (460, 0xf94003e9#32), -- ldr x9, [sp]
  (464, 0x910043ff#32), -- add sp, sp, #0x10
  (468, 0x52800708#32), -- mov w8, #0x38 // =56
  (472, 0xd10043ff#32), -- sub sp, sp, #0x10
  (476, 0xf90003e9#32), -- str x9, [sp]
  (480, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (484, 0x91000269#32), -- add x9, x19, #0x0
  (488, 0x91008129#32), -- add x9, x9, #0x20
  (492, 0xd280000a#32), -- mov x10, #0x0 // =0
  (496, 0xf900012a#32), -- str x10, [x9]
  (500, 0xd280000a#32), -- mov x10, #0x0 // =0
  (504, 0xf900052a#32), -- str x10, [x9, #0x8]
  (508, 0xf94007ea#32) -- ldr x10, [sp, #0x8]
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xf94003e9#32), -- ldr x9, [sp]
  (516, 0x910043ff#32), -- add sp, sp, #0x10
  (520, 0xd10043ff#32), -- sub sp, sp, #0x10
  (524, 0xf90003e9#32), -- str x9, [sp]
  (528, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (532, 0x91000269#32), -- add x9, x19, #0x0
  (536, 0x9100c129#32), -- add x9, x9, #0x30
  (540, 0xd280000a#32), -- mov x10, #0x0 // =0
  (544, 0xf900012a#32), -- str x10, [x9]
  (548, 0xd280000a#32), -- mov x10, #0x0 // =0
  (552, 0xf900052a#32), -- str x10, [x9, #0x8]
  (556, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (560, 0xf94003e9#32), -- ldr x9, [sp]
  (564, 0x910043ff#32), -- add sp, sp, #0x10
  (568, 0xb9004268#32), -- str w8, [x19, #0x40]
  (572, 0xa9534ff4#32), -- ldp x20, x19, [sp, #0x130]
  (576, 0xa95257f6#32), -- ldp x22, x21, [sp, #0x120]
  (580, 0xa9515ff8#32), -- ldp x24, x23, [sp, #0x110]
  (584, 0xa95067fa#32), -- ldp x26, x25, [sp, #0x100]
  (588, 0xa94f7bfd#32), -- ldp x29, x30, [sp, #0xf0]
  (592, 0x910503ff#32), -- add sp, sp, #0x140
  (596, 0xd65f03c0#32), -- ret
  (600, 0xf100275f#32), -- cmp x26, #0x9
  (604, 0x54fff8e8#32), -- b.hi 0x22763c <.LBB57_18>
  (608, 0x52800028#32), -- mov w8, #0x1 // =1
  (612, 0xa940def8#32), -- ldp x24, x23, [x23, #0x8]
  (616, 0x9ada2108#32), -- lsl x8, x8, x26
  (620, 0x52803789#32), -- mov w9, #0x1bc // =444
  (624, 0xea09011f#32), -- tst x8, x9
  (628, 0x54000400#32), -- b.eq 0x2277b8 <.LBB57_28>
  (632, 0xa9408f22#32), -- ldp x2, x3, [x25, #0x8]
  (636, 0xaa1803e0#32), -- mov x0, x24
  (640, 0xaa1703e1#32), -- mov x1, x23
  (644, 0x97fff799#32), -- bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>
  (648, 0xd10043ff#32), -- sub sp, sp, #0x10
  (652, 0xf90003e9#32), -- str x9, [sp]
  (656, 0x12190009#32), -- and w9, w0, #0x80
  (660, 0x35000089#32), -- cbnz w9, 0x227768 <.Llower_arm_483>
  (664, 0xf94003e9#32), -- ldr x9, [sp]
  (668, 0x910043ff#32), -- add sp, sp, #0x10
  (672, 0x14000004#32), -- b 0x227774 <.Llower_arm_484>
  (676, 0xf94003e9#32), -- ldr x9, [sp]
  (680, 0x910043ff#32), -- add sp, sp, #0x10
  (684, 0x14000017#32), -- b 0x2277cc <.LBB57_29>
  (688, 0x52800028#32), -- mov w8, #0x1 // =1
  (692, 0xa9015e78#32), -- stp x24, x23, [x19, #0x10]
  (696, 0xd10043ff#32), -- sub sp, sp, #0x10
  (700, 0xf90003e9#32), -- str x9, [sp]
  (704, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (708, 0x91000269#32), -- add x9, x19, #0x0
  (712, 0xf9000128#32), -- str x8, [x9]
  (716, 0xd280000a#32), -- mov x10, #0x0 // =0
  (720, 0xf900052a#32), -- str x10, [x9, #0x8]
  (724, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (728, 0xf94003e9#32), -- ldr x9, [sp]
  (732, 0x910043ff#32), -- add sp, sp, #0x10
  (736, 0x52800768#32), -- mov w8, #0x3b // =59
  (740, 0x17ffffbd#32), -- b 0x22769c <.LBB57_19>
  (744, 0xb4000669#32), -- cbz x9, 0x227878 <.LBB57_37>
  (748, 0xf940010c#32), -- ldr x12, [x8]
  (752, 0x14000032#32), -- b 0x22787c <.LBB57_38>
  (756, 0x52800028#32), -- mov w8, #0x1 // =1
  (760, 0x52804809#32), -- mov w9, #0x240 // =576
  (764, 0x9ada2108#32) -- lsl x8, x8, x26
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0xea09011f#32), -- tst x8, x9
  (772, 0x54fff3a0#32), -- b.eq 0x22763c <.LBB57_18>
  (776, 0xd1001348#32), -- sub x8, x26, #0x4
  (780, 0xf1000d1f#32), -- cmp x8, #0x3
  (784, 0x540002a2#32), -- b.hs 0x227828 <.LBB57_32>
  (788, 0x910263e0#32), -- add x0, sp, #0x98
  (792, 0xaa1803e1#32), -- mov x1, x24
  (796, 0xaa1703e2#32), -- mov x2, x23
  (800, 0x52800104#32), -- mov w4, #0x8 // =8
  (804, 0xaa1f03e5#32), -- mov x5, xzr
  (808, 0xaa1603e6#32), -- mov x6, x22
  (812, 0x940006b1#32), -- bl 0x2292b4 <_ZN13ssz_fv_native3nat3Nat3shr17he988a53a952ee485E>
  (816, 0xb940dbf4#32), -- ldr w20, [sp, #0xd8]
  (820, 0x34000f34#32), -- cbz w20, 0x2279dc <.LBB57_46>
  (824, 0x910143e0#32), -- add x0, sp, #0x50
  (828, 0x910263e1#32), -- add x1, sp, #0x98
  (832, 0x52800802#32), -- mov w2, #0x40 // =64
  (836, 0x94009732#32), -- bl 0x24d4d0 <memcpy>
  (840, 0xb940dff5#32), -- ldr w21, [sp, #0xdc]
  (844, 0x910143e1#32), -- add x1, sp, #0x50
  (848, 0xaa1303e0#32), -- mov x0, x19
  (852, 0x52800802#32), -- mov w2, #0x40 // =64
  (856, 0x9400972d#32), -- bl 0x24d4d0 <memcpy>
  (860, 0x29085674#32), -- stp w20, w21, [x19, #0x40]
  (864, 0x17ffffb7#32), -- b 0x227700 <.LBB57_21>
  (868, 0xaa1503e8#32), -- mov x8, x21
  (872, 0xb4001214#32), -- cbz x20, 0x227a6c <.LBB57_50>
  (876, 0xd10006a9#32), -- sub x9, x21, #0x1
  (880, 0xb100053f#32), -- cmn x9, #0x1
  (884, 0x54001120#32), -- b.eq 0x227a5c <.LBB57_47>
  (888, 0xd10043ff#32), -- sub sp, sp, #0x10
  (892, 0xf90003eb#32), -- str x11, [sp]
  (896, 0xaa0903eb#32), -- mov x11, x9
  (900, 0xd37df16b#32), -- lsl x11, x11, #3
  (904, 0x8b0b028b#32), -- add x11, x20, x11
  (908, 0xf940016a#32), -- ldr x10, [x11]
  (912, 0xf94003eb#32), -- ldr x11, [sp]
  (916, 0x910043ff#32), -- add sp, sp, #0x10
  (920, 0xaa0903e8#32), -- mov x8, x9
  (924, 0xd1000529#32), -- sub x9, x9, #0x1
  (928, 0xb4fffe8a#32), -- cbz x10, 0x227834 <.LBB57_34>
  (932, 0x91000508#32), -- add x8, x8, #0x1
  (936, 0xf100051f#32), -- cmp x8, #0x1
  (940, 0x54000f80#32), -- b.eq 0x227a60 <.LBB57_48>
  (944, 0x140000b8#32), -- b 0x227b54 <.LBB57_55>
  (948, 0xaa1f03ec#32), -- mov x12, xzr
  (952, 0xb400034b#32), -- cbz x11, 0x2278e4 <.LBB57_44>
  (956, 0xaa1f03ed#32), -- mov x13, xzr
  (960, 0x14000004#32), -- b 0x227894 <.LBB57_41>
  (964, 0x910005ad#32), -- add x13, x13, #0x1
  (968, 0xeb0d017f#32), -- cmp x11, x13
  (972, 0x540002a0#32), -- b.eq 0x2278e4 <.LBB57_44>
  (976, 0xd10043ff#32), -- sub sp, sp, #0x10
  (980, 0xf90003e9#32), -- str x9, [sp]
  (984, 0xaa0d03e9#32), -- mov x9, x13
  (988, 0x8b090149#32), -- add x9, x10, x9
  (992, 0x3940012e#32), -- ldrb w14, [x9]
  (996, 0xf94003e9#32), -- ldr x9, [sp]
  (1000, 0x910043ff#32), -- add sp, sp, #0x10
  (1004, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1008, 0xf90003e9#32), -- str x9, [sp]
  (1012, 0x120001c9#32), -- and w9, w14, #0x1
  (1016, 0x34000089#32), -- cbz w9, 0x2278cc <.Llower_arm_485>
  (1020, 0xf94003e9#32) -- ldr x9, [sp]
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk4 : List (Nat × BitVec 32) := [
  (1024, 0x910043ff#32), -- add sp, sp, #0x10
  (1028, 0x14000004#32), -- b 0x2278d8 <.Llower_arm_486>
  (1032, 0xf94003e9#32), -- ldr x9, [sp]
  (1036, 0x910043ff#32), -- add sp, sp, #0x10
  (1040, 0x17ffffed#32), -- b 0x227888 <.LBB57_40>
  (1044, 0xb400052c#32), -- cbz x12, 0x22797c <.LBB57_45>
  (1048, 0xd100058c#32), -- sub x12, x12, #0x1
  (1052, 0x17ffffea#32), -- b 0x227888 <.LBB57_40>
  (1056, 0x5280002a#32), -- mov w10, #0x1 // =1
  (1060, 0xa9012668#32), -- stp x8, x9, [x19, #0x10]
  (1064, 0x52800728#32), -- mov w8, #0x39 // =57
  (1068, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1072, 0xf90003e9#32), -- str x9, [sp]
  (1076, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1080, 0x91000269#32), -- add x9, x19, #0x0
  (1084, 0x9100c129#32), -- add x9, x9, #0x30
  (1088, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1092, 0xf900012a#32), -- str x10, [x9]
  (1096, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1100, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1104, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1108, 0xf94003e9#32), -- ldr x9, [sp]
  (1112, 0x910043ff#32), -- add sp, sp, #0x10
  (1116, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1120, 0xf90003e9#32), -- str x9, [sp]
  (1124, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1128, 0x91000269#32), -- add x9, x19, #0x0
  (1132, 0x91008129#32), -- add x9, x9, #0x20
  (1136, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1140, 0xf900012a#32), -- str x10, [x9]
  (1144, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1148, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1152, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1156, 0xf94003e9#32), -- ldr x9, [sp]
  (1160, 0x910043ff#32), -- add sp, sp, #0x10
  (1164, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1168, 0xf90003e9#32), -- str x9, [sp]
  (1172, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (1176, 0x91000269#32), -- add x9, x19, #0x0
  (1180, 0xf900012a#32), -- str x10, [x9]
  (1184, 0xd280000b#32), -- mov x11, #0x0 // =0
  (1188, 0xf900052b#32), -- str x11, [x9, #0x8]
  (1192, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (1196, 0xf94003e9#32), -- ldr x9, [sp]
  (1200, 0x910043ff#32), -- add sp, sp, #0x10
  (1204, 0x17ffff61#32), -- b 0x2276fc <.LBB57_20>
  (1208, 0xa9025674#32), -- stp x20, x21, [x19, #0x20]
  (1212, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1216, 0xf90003e9#32), -- str x9, [sp]
  (1220, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1224, 0x91000269#32), -- add x9, x19, #0x0
  (1228, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1232, 0xf900012a#32), -- str x10, [x9]
  (1236, 0xf900052d#32), -- str x13, [x9, #0x8]
  (1240, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1244, 0xf94003e9#32), -- ldr x9, [sp]
  (1248, 0x910043ff#32), -- add sp, sp, #0x10
  (1252, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1256, 0xf90003e9#32), -- str x9, [sp]
  (1260, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1264, 0x91000269#32), -- add x9, x19, #0x0
  (1268, 0x91004129#32), -- add x9, x9, #0x10
  (1272, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1276, 0xf900012a#32) -- str x10, [x9]
]

theorem chunk4_decodes :
    chunk4.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk5 : List (Nat × BitVec 32) := [
  (1280, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1284, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1288, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1292, 0xf94003e9#32), -- ldr x9, [sp]
  (1296, 0x910043ff#32), -- add sp, sp, #0x10
  (1300, 0x17ffff0d#32), -- b 0x22760c <.LBB57_16>
  (1304, 0xa949a7e8#32), -- ldp x8, x9, [sp, #0x98]
  (1308, 0x910083e1#32), -- add x1, sp, #0x20
  (1312, 0xaa1303e0#32), -- mov x0, x19
  (1316, 0x52800602#32), -- mov w2, #0x30 // =48
  (1320, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1324, 0xf90003e9#32), -- str x9, [sp]
  (1328, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1332, 0x910043e9#32), -- add x9, sp, #0x10
  (1336, 0x9100c129#32), -- add x9, x9, #0x30
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
  (1380, 0x910043e9#32), -- add x9, sp, #0x10
  (1384, 0x91010129#32), -- add x9, x9, #0x40
  (1388, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1392, 0xf900012a#32), -- str x10, [x9]
  (1396, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1400, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1404, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1408, 0xf94003e9#32), -- ldr x9, [sp]
  (1412, 0x910043ff#32), -- add sp, sp, #0x10
  (1416, 0xa90527e8#32), -- stp x8, x9, [sp, #0x50]
  (1420, 0xa90227e8#32), -- stp x8, x9, [sp, #0x20]
  (1424, 0x9400969f#32), -- bl 0x24d4d0 <memcpy>
  (1428, 0x17fffeed#32), -- b 0x22760c <.LBB57_16>
  (1432, 0xb4000075#32), -- cbz x21, 0x227a68 <.LBB57_49>
  (1436, 0xf9400288#32), -- ldr x8, [x20]
  (1440, 0x14000002#32), -- b 0x227a6c <.LBB57_50>
  (1444, 0xaa1f03e8#32), -- mov x8, xzr
  (1448, 0xf100811f#32), -- cmp x8, #0x20
  (1452, 0x54000728#32), -- b.hi 0x227b54 <.LBB57_55>
  (1456, 0xd1000509#32), -- sub x9, x8, #0x1
  (1460, 0xca09010a#32), -- eor x10, x8, x9
  (1464, 0xeb09015f#32), -- cmp x10, x9
  (1468, 0x540006a9#32), -- b.ls 0x227b54 <.LBB57_55>
  (1472, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1476, 0xf90003e9#32), -- str x9, [sp]
  (1480, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1484, 0xaa0803e9#32), -- mov x9, x8
  (1488, 0x9200f12a#32), -- and x10, x9, #0x5555555555555555
  (1492, 0xd341fd29#32), -- lsr x9, x9, #1
  (1496, 0x9200f129#32), -- and x9, x9, #0x5555555555555555
  (1500, 0xaa0a0529#32), -- orr x9, x9, x10, lsl #1
  (1504, 0x9200e52a#32), -- and x10, x9, #0x3333333333333333
  (1508, 0xd342fd29#32), -- lsr x9, x9, #2
  (1512, 0x9200e529#32), -- and x9, x9, #0x3333333333333333
  (1516, 0xaa0a0929#32), -- orr x9, x9, x10, lsl #2
  (1520, 0x9200cd2a#32), -- and x10, x9, #0xf0f0f0f0f0f0f0f
  (1524, 0xd344fd29#32), -- lsr x9, x9, #4
  (1528, 0x9200cd29#32), -- and x9, x9, #0xf0f0f0f0f0f0f0f
  (1532, 0xaa0a1129#32) -- orr x9, x9, x10, lsl #4
]

theorem chunk5_decodes :
    chunk5.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk6 : List (Nat × BitVec 32) := [
  (1536, 0x92009d2a#32), -- and x10, x9, #0xff00ff00ff00ff
  (1540, 0xd348fd29#32), -- lsr x9, x9, #8
  (1544, 0x92009d29#32), -- and x9, x9, #0xff00ff00ff00ff
  (1548, 0xaa0a2129#32), -- orr x9, x9, x10, lsl #8
  (1552, 0x92003d2a#32), -- and x10, x9, #0xffff0000ffff
  (1556, 0xd350fd29#32), -- lsr x9, x9, #16
  (1560, 0x92003d29#32), -- and x9, x9, #0xffff0000ffff
  (1564, 0xaa0a4129#32), -- orr x9, x9, x10, lsl #16
  (1568, 0x92407d2a#32), -- and x10, x9, #0xffffffff
  (1572, 0xd360fd29#32), -- lsr x9, x9, #32
  (1576, 0x92407d29#32), -- and x9, x9, #0xffffffff
  (1580, 0xaa0a8129#32), -- orr x9, x9, x10, lsl #32
  (1584, 0xaa0903e8#32), -- mov x8, x9
  (1588, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1592, 0xf94003e9#32), -- ldr x9, [sp]
  (1596, 0x910043ff#32), -- add sp, sp, #0x10
  (1600, 0xaa1703f9#32), -- mov x25, x23
  (1604, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1608, 0xf90003e9#32), -- str x9, [sp]
  (1612, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1616, 0xaa0803e9#32), -- mov x9, x8
  (1620, 0xd280080a#32), -- mov x10, #0x40 // =64
  (1624, 0xb4000089#32), -- cbz x9, 0x227b2c <.Llower_arm_488>
  (1628, 0xd100054a#32), -- sub x10, x10, #0x1
  (1632, 0xd341fd29#32), -- lsr x9, x9, #1
  (1636, 0xb5ffffc9#32), -- cbnz x9, 0x227b20 <.Llower_arm_487>
  (1640, 0xaa0a03f5#32), -- mov x21, x10
  (1644, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1648, 0xf94003e9#32), -- ldr x9, [sp]
  (1652, 0x910043ff#32), -- add sp, sp, #0x10
  (1656, 0x528000a8#32), -- mov w8, #0x5 // =5
  (1660, 0x4b150114#32), -- sub w20, w8, w21
  (1664, 0xb40005d8#32), -- cbz x24, 0x227bfc <.LBB57_60>
  (1668, 0xb4000597#32), -- cbz x23, 0x227bf8 <.LBB57_59>
  (1672, 0xf9400319#32), -- ldr x25, [x24]
  (1676, 0x1400002b#32), -- b 0x227bfc <.LBB57_60>
  (1680, 0x910263e0#32), -- add x0, sp, #0x98
  (1684, 0xaa1803e1#32), -- mov x1, x24
  (1688, 0xaa1703e2#32), -- mov x2, x23
  (1692, 0xaa1403e3#32), -- mov x3, x20
  (1696, 0xaa1503e4#32), -- mov x4, x21
  (1700, 0xaa1603e5#32), -- mov x5, x22
  (1704, 0x910263fa#32), -- add x26, sp, #0x98
  (1708, 0x97fff343#32), -- bl 0x22487c <_ZN13ssz_fv_native3nat3Nat3mul17h5dc2c96f405496c8E>
  (1712, 0xa949dff8#32), -- ldp x24, x23, [sp, #0x98]
  (1716, 0xb940dbf9#32), -- ldr w25, [sp, #0xd8]
  (1720, 0x34000139#32), -- cbz w25, 0x227ba0 <.LBB57_57>
  (1724, 0x91004260#32), -- add x0, x19, #0x10
  (1728, 0x91004341#32), -- add x1, x26, #0x10
  (1732, 0x52800602#32), -- mov w2, #0x30 // =48
  (1736, 0x94009651#32), -- bl 0x24d4d0 <memcpy>
  (1740, 0xb940dfe8#32), -- ldr w8, [sp, #0xdc]
  (1744, 0xa9005e78#32), -- stp x24, x23, [x19]
  (1748, 0x29082279#32), -- stp w25, w8, [x19, #0x40]
  (1752, 0x17fffed9#32), -- b 0x227700 <.LBB57_21>
  (1756, 0x910143e0#32), -- add x0, sp, #0x50
  (1760, 0xaa1803e1#32), -- mov x1, x24
  (1764, 0xaa1703e2#32), -- mov x2, x23
  (1768, 0x52800403#32), -- mov w3, #0x20 // =32
  (1772, 0xaa1603e4#32), -- mov x4, x22
  (1776, 0x910143f9#32), -- add x25, sp, #0x50
  (1780, 0x97ffe438#32), -- bl 0x220c98 <_ZN13ssz_fv_native3nat3Nat13div_rem_small17he8c5c3bc7904fc5eE>
  (1784, 0xa94527e8#32), -- ldp x8, x9, [sp, #0x50]
  (1788, 0xb94093f8#32) -- ldr w24, [sp, #0x90]
]

theorem chunk6_decodes :
    chunk6.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk7 : List (Nat × BitVec 32) := [
  (1792, 0xf94033f7#32), -- ldr x23, [sp, #0x60]
  (1796, 0xa90227e8#32), -- stp x8, x9, [sp, #0x20]
  (1800, 0x34000838#32), -- cbz w24, 0x227cd0 <.LBB57_63>
  (1804, 0x91006260#32), -- add x0, x19, #0x18
  (1808, 0x91006321#32), -- add x1, x25, #0x18
  (1812, 0x52800502#32), -- mov w2, #0x28 // =40
  (1816, 0x9400963d#32), -- bl 0x24d4d0 <memcpy>
  (1820, 0xa94227e8#32), -- ldp x8, x9, [sp, #0x20]
  (1824, 0xf9000268#32), -- str x8, [x19]
  (1828, 0xb94097e8#32), -- ldr w8, [sp, #0x94]
  (1832, 0xa900de69#32), -- stp x9, x23, [x19, #0x8]
  (1836, 0x29082278#32), -- stp w24, w8, [x19, #0x40]
  (1840, 0x17fffec3#32), -- b 0x227700 <.LBB57_21>
  (1844, 0xaa1f03f9#32), -- mov x25, xzr
  (1848, 0x910263e0#32), -- add x0, sp, #0x98
  (1852, 0xaa1803e1#32), -- mov x1, x24
  (1856, 0xaa1703e2#32), -- mov x2, x23
  (1860, 0xaa1403e4#32), -- mov x4, x20
  (1864, 0xaa1f03e5#32), -- mov x5, xzr
  (1868, 0xaa1603e6#32), -- mov x6, x22
  (1872, 0x940005a8#32), -- bl 0x2292b4 <_ZN13ssz_fv_native3nat3Nat3shr17he988a53a952ee485E>
  (1876, 0xb940dbf6#32), -- ldr w22, [sp, #0xd8]
  (1880, 0x34000196#32), -- cbz w22, 0x227c4c <.LBB57_62>
  (1884, 0x910143e0#32), -- add x0, sp, #0x50
  (1888, 0x910263e1#32), -- add x1, sp, #0x98
  (1892, 0x52800802#32), -- mov w2, #0x40 // =64
  (1896, 0x94009629#32), -- bl 0x24d4d0 <memcpy>
  (1900, 0xb940dff4#32), -- ldr w20, [sp, #0xdc]
  (1904, 0x910143e1#32), -- add x1, sp, #0x50
  (1908, 0xaa1303e0#32), -- mov x0, x19
  (1912, 0x52800802#32), -- mov w2, #0x40 // =64
  (1916, 0x94009624#32), -- bl 0x24d4d0 <memcpy>
  (1920, 0x29085276#32), -- stp w22, w20, [x19, #0x40]
  (1924, 0x17fffeae#32), -- b 0x227700 <.LBB57_21>
  (1928, 0x92800009#32), -- mov x9, #-0x1 // =-1
  (1932, 0xa949abe8#32), -- ldp x8, x10, [sp, #0x98]
  (1936, 0x9ad42129#32), -- lsl x9, x9, x20
  (1940, 0xb9004276#32), -- str w22, [x19, #0x40]
  (1944, 0x8a290329#32), -- bic x9, x25, x9
  (1948, 0xa9052be8#32), -- stp x8, x10, [sp, #0x50]
  (1952, 0xa9002a68#32), -- stp x8, x10, [x19]
  (1956, 0x9ad52128#32), -- lsl x8, x9, x21
  (1960, 0x91000529#32), -- add x9, x9, #0x1
  (1964, 0x9ad52129#32), -- lsl x9, x9, x21
  (1968, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1972, 0xf90003e9#32), -- str x9, [sp]
  (1976, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1980, 0x91000269#32), -- add x9, x19, #0x0
  (1984, 0x91004129#32), -- add x9, x9, #0x10
  (1988, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1992, 0xf900012a#32), -- str x10, [x9]
  (1996, 0xf9000528#32), -- str x8, [x9, #0x8]
  (2000, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (2004, 0xf94003e9#32), -- ldr x9, [sp]
  (2008, 0x910043ff#32), -- add sp, sp, #0x10
  (2012, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2016, 0xf90003ea#32), -- str x10, [sp]
  (2020, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (2024, 0x9100026a#32), -- add x10, x19, #0x0
  (2028, 0x9100814a#32), -- add x10, x10, #0x20
  (2032, 0xd280000b#32), -- mov x11, #0x0 // =0
  (2036, 0xf900014b#32), -- str x11, [x10]
  (2040, 0xf9000549#32), -- str x9, [x10, #0x8]
  (2044, 0xf94007eb#32) -- ldr x11, [sp, #0x8]
]

theorem chunk7_decodes :
    chunk7.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk8 : List (Nat × BitVec 32) := [
  (2048, 0xf94003ea#32), -- ldr x10, [sp]
  (2052, 0x910043ff#32), -- add sp, sp, #0x10
  (2056, 0x17fffe8d#32), -- b 0x227700 <.LBB57_21>
  (2060, 0xa94227e8#32), -- ldp x8, x9, [sp, #0x20]
  (2064, 0x910263e0#32), -- add x0, sp, #0x98
  (2068, 0xaa1f03e1#32), -- mov x1, xzr
  (2072, 0xaa1703e2#32), -- mov x2, x23
  (2076, 0xaa1403e3#32), -- mov x3, x20
  (2080, 0xaa1503e4#32), -- mov x4, x21
  (2084, 0xaa1603e5#32), -- mov x5, x22
  (2088, 0xa90e27e8#32), -- stp x8, x9, [sp, #0xe0]
  (2092, 0x97ffeecf#32), -- bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>
  (2096, 0xb940dbf4#32), -- ldr w20, [sp, #0xd8]
  (2100, 0x35ffd834#32), -- cbnz w20, 0x2277fc <.LBB57_31>
  (2104, 0xa949a7e8#32), -- ldp x8, x9, [sp, #0x98]
  (2108, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2112, 0xf90003e9#32), -- str x9, [sp]
  (2116, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2120, 0x91000269#32), -- add x9, x19, #0x0
  (2124, 0x91004129#32), -- add x9, x9, #0x10
  (2128, 0xd280000a#32), -- mov x10, #0x0 // =0
  (2132, 0xf900012a#32), -- str x10, [x9]
  (2136, 0xf9000537#32), -- str x23, [x9, #0x8]
  (2140, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (2144, 0xf94003e9#32), -- ldr x9, [sp]
  (2148, 0x910043ff#32), -- add sp, sp, #0x10
  (2152, 0xa90527e8#32), -- stp x8, x9, [sp, #0x50]
  (2156, 0xa9022668#32), -- stp x8, x9, [x19, #0x20]
  (2160, 0xa94e23ea#32), -- ldp x10, x8, [sp, #0xe0]
  (2164, 0xa900226a#32), -- stp x10, x8, [x19]
  (2168, 0x17fffe34#32) -- b 0x22760c <.LBB57_16>
]

theorem chunk8_decodes :
    chunk8.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete linked function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 ++ chunk8

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

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, chunk3_decodes, chunk4_decodes, chunk5_decodes, chunk6_decodes, chunk7_decodes, chunk8_decodes, Bool.and_self]

theorem step_at (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (row : Nat × BitVec 32) (member : row ∈ program)
    (entry : read_pc s = base + BitVec.ofNat 64 row.1)
    (error : read_err s = .None) :
    stepi s = exec_inst (SszArm.Codec.Linked.decoded program all_decode row member) s :=
  SszArm.Codec.Linked.step_at program all_decode s base code row member entry error

end SszArm.Indices.Linked.ChunkPosition
