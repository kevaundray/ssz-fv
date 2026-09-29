import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.GeneralizedIndex

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN13ssz_fv_native7indices17generalized_index17h7859d2dc0e7dcce2E. -/
def address : Nat := 2411004

def byteSize : Nat := 2772

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10383ff#32), -- sub sp, sp, #0xe0
  (4, 0xf9004bfe#32), -- str x30, [sp, #0x90]
  (8, 0xa90a67fa#32), -- stp x26, x25, [sp, #0xa0]
  (12, 0xa90b5ff8#32), -- stp x24, x23, [sp, #0xb0]
  (16, 0xa90c57f6#32), -- stp x22, x21, [sp, #0xc0]
  (20, 0xa90d4ff4#32), -- stp x20, x19, [sp, #0xd0]
  (24, 0xaa0003f3#32), -- mov x19, x0
  (28, 0xb4000343#32), -- cbz x3, 0x24ca80 <.LBB158_3>
  (32, 0xaa0303f5#32), -- mov x21, x3
  (36, 0x9100a3e0#32), -- add x0, sp, #0x28
  (40, 0xaa0403e3#32), -- mov x3, x4
  (44, 0xaa0403f4#32), -- mov x20, x4
  (48, 0xaa0203f8#32), -- mov x24, x2
  (52, 0x97ff66cf#32), -- bl 0x22656c <_ZN13ssz_fv_native7indices12resolve_step17hc445f88b4eb19d18E>
  (56, 0xa9442be9#32), -- ldp x9, x10, [sp, #0x40]
  (60, 0xf94017f7#32), -- ldr x23, [sp, #0x28]
  (64, 0xa94323f6#32), -- ldp x22, x8, [sp, #0x30]
  (68, 0xa9002be9#32), -- stp x9, x10, [sp]
  (72, 0xa9452beb#32), -- ldp x11, x10, [sp, #0x50]
  (76, 0xb9406be9#32), -- ldr w9, [sp, #0x68]
  (80, 0xa9012beb#32), -- stp x11, x10, [sp, #0x10]
  (84, 0x34000509#32), -- cbz w9, 0x24caf0 <.LBB158_7>
  (88, 0xa940afea#32), -- ldp x10, x11, [sp, #0x8]
  (92, 0xf9400fec#32), -- ldr x12, [sp, #0x18]
  (96, 0xa9005a77#32), -- stp x23, x22, [x19]
  (100, 0xa9022e6a#32), -- stp x10, x11, [x19, #0x20]
  (104, 0xf94003ea#32), -- ldr x10, [sp]
  (108, 0xf94033eb#32), -- ldr x11, [sp, #0x60]
  (112, 0xa9012a68#32), -- stp x8, x10, [x19, #0x10]
  (116, 0xb9406fe8#32), -- ldr w8, [sp, #0x6c]
  (120, 0xa9032e6c#32), -- stp x12, x11, [x19, #0x30]
  (124, 0x29082269#32), -- stp w9, w8, [x19, #0x40]
  (128, 0x14000016#32), -- b 0x24cad4 <.LBB158_6>
  (132, 0x52800028#32), -- mov w8, #0x1 // =1
  (136, 0xd10043ff#32), -- sub sp, sp, #0x10
  (140, 0xf90003e9#32), -- str x9, [sp]
  (144, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (148, 0x91000269#32), -- add x9, x19, #0x0
  (152, 0xd280000a#32), -- mov x10, #0x0 // =0
  (156, 0xf900012a#32), -- str x10, [x9]
  (160, 0xf9000528#32), -- str x8, [x9, #0x8]
  (164, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (168, 0xf94003e9#32), -- ldr x9, [sp]
  (172, 0x910043ff#32), -- add sp, sp, #0x10
  (176, 0xd10043ff#32), -- sub sp, sp, #0x10
  (180, 0xf90003e9#32), -- str x9, [sp]
  (184, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (188, 0x91000269#32), -- add x9, x19, #0x0
  (192, 0x91010129#32), -- add x9, x9, #0x40
  (196, 0x5280000a#32), -- mov w10, #0x0 // =0
  (200, 0xb900012a#32), -- str w10, [x9]
  (204, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (208, 0xf94003e9#32), -- ldr x9, [sp]
  (212, 0x910043ff#32), -- add sp, sp, #0x10
  (216, 0xa94d4ff4#32), -- ldp x20, x19, [sp, #0xd0]
  (220, 0xf9404bfe#32), -- ldr x30, [sp, #0x90]
  (224, 0xa94c57f6#32), -- ldp x22, x21, [sp, #0xc0]
  (228, 0xa94b5ff8#32), -- ldp x24, x23, [sp, #0xb0]
  (232, 0xa94a67fa#32), -- ldp x26, x25, [sp, #0xa0]
  (236, 0x910383ff#32), -- add sp, sp, #0xe0
  (240, 0xd65f03c0#32), -- ret
  (244, 0xa9402be9#32), -- ldp x9, x10, [sp]
  (248, 0xf100351f#32), -- cmp x8, #0xd
  (252, 0xd10006a3#32) -- sub x3, x21, #0x1
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0xa9072be9#32), -- stp x9, x10, [sp, #0x70]
  (260, 0xa9412fe9#32), -- ldp x9, x11, [sp, #0x10]
  (264, 0xa9082fe9#32), -- stp x9, x11, [sp, #0x80]
  (268, 0x54000681#32), -- b.ne 0x24cbd8 <.LBB158_10>
  (272, 0xb40017c3#32), -- cbz x3, 0x24ce04 <.LBB158_29>
  (276, 0x52800028#32), -- mov w8, #0x1 // =1
  (280, 0xd10043ff#32), -- sub sp, sp, #0x10
  (284, 0xf90003e9#32), -- str x9, [sp]
  (288, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (292, 0x91000269#32), -- add x9, x19, #0x0
  (296, 0x91004129#32), -- add x9, x9, #0x10
  (300, 0xd280000a#32), -- mov x10, #0x0 // =0
  (304, 0xf900012a#32), -- str x10, [x9]
  (308, 0xd280000a#32), -- mov x10, #0x0 // =0
  (312, 0xf900052a#32), -- str x10, [x9, #0x8]
  (316, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (320, 0xf94003e9#32), -- ldr x9, [sp]
  (324, 0x910043ff#32), -- add sp, sp, #0x10
  (328, 0xd10043ff#32), -- sub sp, sp, #0x10
  (332, 0xf90003e9#32), -- str x9, [sp]
  (336, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (340, 0x91000269#32), -- add x9, x19, #0x0
  (344, 0xf9000128#32), -- str x8, [x9]
  (348, 0xd280000a#32), -- mov x10, #0x0 // =0
  (352, 0xf900052a#32), -- str x10, [x9, #0x8]
  (356, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (360, 0xf94003e9#32), -- ldr x9, [sp]
  (364, 0x910043ff#32), -- add sp, sp, #0x10
  (368, 0x528006a8#32), -- mov w8, #0x35 // =53
  (372, 0xd10043ff#32), -- sub sp, sp, #0x10
  (376, 0xf90003e9#32), -- str x9, [sp]
  (380, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (384, 0x91000269#32), -- add x9, x19, #0x0
  (388, 0x91008129#32), -- add x9, x9, #0x20
  (392, 0xd280000a#32), -- mov x10, #0x0 // =0
  (396, 0xf900012a#32), -- str x10, [x9]
  (400, 0xd280000a#32), -- mov x10, #0x0 // =0
  (404, 0xf900052a#32), -- str x10, [x9, #0x8]
  (408, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (412, 0xf94003e9#32), -- ldr x9, [sp]
  (416, 0x910043ff#32), -- add sp, sp, #0x10
  (420, 0xd10043ff#32), -- sub sp, sp, #0x10
  (424, 0xf90003e9#32), -- str x9, [sp]
  (428, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (432, 0x91000269#32), -- add x9, x19, #0x0
  (436, 0x9100c129#32), -- add x9, x9, #0x30
  (440, 0xd280000a#32), -- mov x10, #0x0 // =0
  (444, 0xf900012a#32), -- str x10, [x9]
  (448, 0xd280000a#32), -- mov x10, #0x0 // =0
  (452, 0xf900052a#32), -- str x10, [x9, #0x8]
  (456, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (460, 0xf94003e9#32), -- ldr x9, [sp]
  (464, 0x910043ff#32), -- add sp, sp, #0x10
  (468, 0xb9004268#32), -- str w8, [x19, #0x40]
  (472, 0x17ffffc0#32), -- b 0x24cad4 <.LBB158_6>
  (476, 0xa9472be9#32), -- ldp x9, x10, [sp, #0x70]
  (480, 0x9100a3e0#32), -- add x0, sp, #0x28
  (484, 0x910003e1#32), -- mov x1, sp
  (488, 0x91006302#32), -- add x2, x24, #0x18
  (492, 0xaa1403e4#32), -- mov x4, x20
  (496, 0x9100a3fa#32), -- add x26, sp, #0x28
  (500, 0xa90027e8#32), -- stp x8, x9, [sp]
  (504, 0xa94827e8#32), -- ldp x8, x9, [sp, #0x80]
  (508, 0xa90123ea#32) -- stp x10, x8, [sp, #0x10]
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xf90013e9#32), -- str x9, [sp, #0x20]
  (516, 0x97ffff7f#32), -- bl 0x24c9fc <_ZN13ssz_fv_native7indices17generalized_index17h7859d2dc0e7dcce2E>
  (520, 0xa942d7f8#32), -- ldp x24, x21, [sp, #0x28]
  (524, 0xb9406bf9#32), -- ldr w25, [sp, #0x68]
  (528, 0x34000139#32), -- cbz w25, 0x24cc30 <.LBB158_12>
  (532, 0x91004260#32), -- add x0, x19, #0x10
  (536, 0x91004341#32), -- add x1, x26, #0x10
  (540, 0x52800602#32), -- mov w2, #0x30 // =48
  (544, 0x9400022d#32), -- bl 0x24d4d0 <memcpy>
  (548, 0xb9406fe8#32), -- ldr w8, [sp, #0x6c]
  (552, 0xa9005678#32), -- stp x24, x21, [x19]
  (556, 0x29082279#32), -- stp w25, w8, [x19, #0x40]
  (560, 0x17ffffaa#32), -- b 0x24cad4 <.LBB158_6>
  (564, 0xb40001f7#32), -- cbz x23, 0x24cc6c <.LBB158_16>
  (568, 0xd10022e8#32), -- sub x8, x23, #0x8
  (572, 0xaa1603e9#32), -- mov x9, x22
  (576, 0xb40005c9#32), -- cbz x9, 0x24ccf4 <.LBB158_25>
  (580, 0xd10043ff#32), -- sub sp, sp, #0x10
  (584, 0xf90003eb#32), -- str x11, [sp]
  (588, 0xaa0903eb#32), -- mov x11, x9
  (592, 0xd37df16b#32), -- lsl x11, x11, #3
  (596, 0x8b0b010b#32), -- add x11, x8, x11
  (600, 0xf940016a#32), -- ldr x10, [x11]
  (604, 0xf94003eb#32), -- ldr x11, [sp]
  (608, 0x910043ff#32), -- add sp, sp, #0x10
  (612, 0xd1000529#32), -- sub x9, x9, #0x1
  (616, 0xb4fffeca#32), -- cbz x10, 0x24cc3c <.LBB158_14>
  (620, 0x14000002#32), -- b 0x24cc70 <.LBB158_17>
  (624, 0xb4000456#32), -- cbz x22, 0x24ccf4 <.LBB158_25>
  (628, 0xb40008d8#32), -- cbz x24, 0x24cd88 <.LBB158_26>
  (632, 0xd1002308#32), -- sub x8, x24, #0x8
  (636, 0xaa1503e9#32), -- mov x9, x21
  (640, 0xb4000c89#32), -- cbz x9, 0x24ce0c <.LBB158_30>
  (644, 0xd10043ff#32), -- sub sp, sp, #0x10
  (648, 0xf90003eb#32), -- str x11, [sp]
  (652, 0xaa0903eb#32), -- mov x11, x9
  (656, 0xd37df16b#32), -- lsl x11, x11, #3
  (660, 0x8b0b010b#32), -- add x11, x8, x11
  (664, 0xf940016a#32), -- ldr x10, [x11]
  (668, 0xf94003eb#32), -- ldr x11, [sp]
  (672, 0x910043ff#32), -- add sp, sp, #0x10
  (676, 0xd1000529#32), -- sub x9, x9, #0x1
  (680, 0xb4fffeca#32), -- cbz x10, 0x24cc7c <.LBB158_19>
  (684, 0xaa1503eb#32), -- mov x11, x21
  (688, 0xb4000acb#32), -- cbz x11, 0x24ce04 <.LBB158_29>
  (692, 0xd10043ff#32), -- sub sp, sp, #0x10
  (696, 0xf90003ea#32), -- str x10, [sp]
  (700, 0xaa0b03ea#32), -- mov x10, x11
  (704, 0xd37df14a#32), -- lsl x10, x10, #3
  (708, 0x8b0a010a#32), -- add x10, x8, x10
  (712, 0xf9400149#32), -- ldr x9, [x10]
  (716, 0xf94003ea#32), -- ldr x10, [sp]
  (720, 0x910043ff#32), -- add sp, sp, #0x10
  (724, 0xaa0b03ea#32), -- mov x10, x11
  (728, 0xd100056b#32), -- sub x11, x11, #0x1
  (732, 0xb4fffea9#32), -- cbz x9, 0x24ccac <.LBB158_22>
  (736, 0xd37ae548#32), -- lsl x8, x10, #6
  (740, 0xd37afd4a#32), -- lsr x10, x10, #58
  (744, 0x9280000b#32), -- mov x11, #-0x1 // =-1
  (748, 0xf1010108#32), -- subs x8, x8, #0x40
  (752, 0x9a0b014a#32), -- adc x10, x10, x11
  (756, 0x1400002a#32), -- b 0x24cd98 <.LBB158_28>
  (760, 0x52800028#32), -- mov w8, #0x1 // =1
  (764, 0xd10043ff#32) -- sub sp, sp, #0x10
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0xf90003e9#32), -- str x9, [sp]
  (772, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (776, 0x91000269#32), -- add x9, x19, #0x0
  (780, 0x9100c129#32), -- add x9, x9, #0x30
  (784, 0xd280000a#32), -- mov x10, #0x0 // =0
  (788, 0xf900012a#32), -- str x10, [x9]
  (792, 0xd280000a#32), -- mov x10, #0x0 // =0
  (796, 0xf900052a#32), -- str x10, [x9, #0x8]
  (800, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (804, 0xf94003e9#32), -- ldr x9, [sp]
  (808, 0x910043ff#32), -- add sp, sp, #0x10
  (812, 0xd10043ff#32), -- sub sp, sp, #0x10
  (816, 0xf90003e9#32), -- str x9, [sp]
  (820, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (824, 0x91000269#32), -- add x9, x19, #0x0
  (828, 0x91008129#32), -- add x9, x9, #0x20
  (832, 0xd280000a#32), -- mov x10, #0x0 // =0
  (836, 0xf900012a#32), -- str x10, [x9]
  (840, 0xd280000a#32), -- mov x10, #0x0 // =0
  (844, 0xf900052a#32), -- str x10, [x9, #0x8]
  (848, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (852, 0xf94003e9#32), -- ldr x9, [sp]
  (856, 0x910043ff#32), -- add sp, sp, #0x10
  (860, 0xd10043ff#32), -- sub sp, sp, #0x10
  (864, 0xf90003e9#32), -- str x9, [sp]
  (868, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (872, 0x91000269#32), -- add x9, x19, #0x0
  (876, 0xf9000128#32), -- str x8, [x9]
  (880, 0xd280000a#32), -- mov x10, #0x0 // =0
  (884, 0xf900052a#32), -- str x10, [x9, #0x8]
  (888, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (892, 0xf94003e9#32), -- ldr x9, [sp]
  (896, 0x910043ff#32), -- add sp, sp, #0x10
  (900, 0xa9015a77#32), -- stp x23, x22, [x19, #0x10]
  (904, 0x14000046#32), -- b 0x24ce9c <.LBB158_31>
  (908, 0xb4000435#32), -- cbz x21, 0x24ce0c <.LBB158_30>
  (912, 0xaa1f03e8#32), -- mov x8, xzr
  (916, 0xaa1f03ea#32), -- mov x10, xzr
  (920, 0xaa1503e9#32), -- mov x9, x21
  (924, 0xd10043ff#32), -- sub sp, sp, #0x10
  (928, 0xf90003ea#32), -- str x10, [sp]
  (932, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (936, 0xaa0903ea#32), -- mov x10, x9
  (940, 0xd280080b#32), -- mov x11, #0x40 // =64
  (944, 0xb400008a#32), -- cbz x10, 0x24cdbc <.Llower_arm_1408>
  (948, 0xd100056b#32), -- sub x11, x11, #0x1
  (952, 0xd341fd4a#32), -- lsr x10, x10, #1
  (956, 0xb5ffffca#32), -- cbnz x10, 0x24cdb0 <.Llower_arm_1407>
  (960, 0xaa0b03e9#32), -- mov x9, x11
  (964, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (968, 0xf94003ea#32), -- ldr x10, [sp]
  (972, 0x910043ff#32), -- add sp, sp, #0x10
  (976, 0x5280080b#32), -- mov w11, #0x40 // =64
  (980, 0x5280002c#32), -- mov w12, #0x1 // =1
  (984, 0x4b090169#32), -- sub w9, w11, w9
  (988, 0xab09010b#32), -- adds x11, x8, x9
  (992, 0x92800009#32), -- mov x9, #-0x1 // =-1
  (996, 0x54000062#32), -- b.hs 0x24cdec <.Llower_arm_1409>
  (1000, 0xaa0a03ea#32), -- mov x10, x10
  (1004, 0x14000002#32), -- b 0x24cdf0 <.Llower_arm_1410>
  (1008, 0x9100054a#32), -- add x10, x10, #0x1
  (1012, 0xf1000568#32), -- subs x8, x11, #0x1
  (1016, 0x9a090149#32), -- adc x9, x10, x9
  (1020, 0xeb0b019f#32) -- cmp x12, x11
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk4 : List (Nat × BitVec 32) := [
  (1024, 0xfa0a03ff#32), -- ngcs xzr, x10
  (1028, 0x54000543#32), -- b.lo 0x24cea8 <.LBB158_32>
  (1032, 0xa9005a77#32), -- stp x23, x22, [x19]
  (1036, 0x17ffff29#32), -- b 0x24caac <.LBB158_5>
  (1040, 0x52800028#32), -- mov w8, #0x1 // =1
  (1044, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1048, 0xf90003e9#32), -- str x9, [sp]
  (1052, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1056, 0x91000269#32), -- add x9, x19, #0x0
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
  (1104, 0x91000269#32), -- add x9, x19, #0x0
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
  (1152, 0x91000269#32), -- add x9, x19, #0x0
  (1156, 0xf9000128#32), -- str x8, [x9]
  (1160, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1164, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1168, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1172, 0xf94003e9#32), -- ldr x9, [sp]
  (1176, 0x910043ff#32), -- add sp, sp, #0x10
  (1180, 0xa9015678#32), -- stp x24, x21, [x19, #0x10]
  (1184, 0x528004e8#32), -- mov w8, #0x27 // =39
  (1188, 0xb9004268#32), -- str w8, [x19, #0x40]
  (1192, 0x17ffff0c#32), -- b 0x24cad4 <.LBB158_6>
  (1196, 0xb4000537#32), -- cbz x23, 0x24cf4c <.LBB158_42>
  (1200, 0xd10006cb#32), -- sub x11, x22, #0x1
  (1204, 0xb100057f#32), -- cmn x11, #0x1
  (1208, 0x54000240#32), -- b.eq 0x24cefc <.LBB158_38>
  (1212, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1216, 0xf90003e9#32), -- str x9, [sp]
  (1220, 0xaa0b03e9#32), -- mov x9, x11
  (1224, 0xd37df129#32), -- lsl x9, x9, #3
  (1228, 0x8b0902e9#32), -- add x9, x23, x9
  (1232, 0xf940012c#32), -- ldr x12, [x9]
  (1236, 0xf94003e9#32), -- ldr x9, [sp]
  (1240, 0x910043ff#32), -- add sp, sp, #0x10
  (1244, 0xaa0b03ea#32), -- mov x10, x11
  (1248, 0xd100056b#32), -- sub x11, x11, #0x1
  (1252, 0xb4fffe8c#32), -- cbz x12, 0x24ceb0 <.LBB158_34>
  (1256, 0x9100054a#32), -- add x10, x10, #0x1
  (1260, 0xf100055f#32), -- cmp x10, #0x1
  (1264, 0x54000081#32), -- b.ne 0x24cefc <.LBB158_38>
  (1268, 0xf94002ea#32), -- ldr x10, [x23]
  (1272, 0xf100055f#32), -- cmp x10, #0x1
  (1276, 0x54000340#32) -- b.eq 0x24cf60 <.LBB158_44>
]

theorem chunk4_decodes :
    chunk4.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk5 : List (Nat × BitVec 32) := [
  (1280, 0xd10022eb#32), -- sub x11, x23, #0x8
  (1284, 0xaa1603ed#32), -- mov x13, x22
  (1288, 0xb400032d#32), -- cbz x13, 0x24cf68 <.LBB158_45>
  (1292, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1296, 0xf90003e9#32), -- str x9, [sp]
  (1300, 0xaa0d03e9#32), -- mov x9, x13
  (1304, 0xd37df129#32), -- lsl x9, x9, #3
  (1308, 0x8b090169#32), -- add x9, x11, x9
  (1312, 0xf940012a#32), -- ldr x10, [x9]
  (1316, 0xf94003e9#32), -- ldr x9, [sp]
  (1320, 0x910043ff#32), -- add sp, sp, #0x10
  (1324, 0xaa0d03ec#32), -- mov x12, x13
  (1328, 0xd10005ad#32), -- sub x13, x13, #0x1
  (1332, 0xb4fffeaa#32), -- cbz x10, 0x24cf04 <.LBB158_39>
  (1336, 0xd37ae58b#32), -- lsl x11, x12, #6
  (1340, 0xd37afd8c#32), -- lsr x12, x12, #58
  (1344, 0x9280000d#32), -- mov x13, #-0x1 // =-1
  (1348, 0xf101016b#32), -- subs x11, x11, #0x40
  (1352, 0x9a0d018c#32), -- adc x12, x12, x13
  (1356, 0x1400000e#32), -- b 0x24cf80 <.LBB158_47>
  (1360, 0xaa0803ea#32), -- mov x10, x8
  (1364, 0xaa0903eb#32), -- mov x11, x9
  (1368, 0xb4000436#32), -- cbz x22, 0x24cfd8 <.LBB158_48>
  (1372, 0xf10006df#32), -- cmp x22, #0x1
  (1376, 0x540000c1#32), -- b.ne 0x24cf74 <.LBB158_46>
  (1380, 0xa9005678#32), -- stp x24, x21, [x19]
  (1384, 0x17fffed2#32), -- b 0x24caac <.LBB158_5>
  (1388, 0xaa0803ea#32), -- mov x10, x8
  (1392, 0xaa0903eb#32), -- mov x11, x9
  (1396, 0x1400001a#32), -- b 0x24cfd8 <.LBB158_48>
  (1400, 0xaa1f03eb#32), -- mov x11, xzr
  (1404, 0xaa1f03ec#32), -- mov x12, xzr
  (1408, 0xaa1603ea#32), -- mov x10, x22
  (1412, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1416, 0xf90003e9#32), -- str x9, [sp]
  (1420, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (1424, 0xaa0a03e9#32), -- mov x9, x10
  (1428, 0xd280080b#32), -- mov x11, #0x40 // =64
  (1432, 0xb4000089#32), -- cbz x9, 0x24cfa4 <.Llower_arm_1412>
  (1436, 0xd100056b#32), -- sub x11, x11, #0x1
  (1440, 0xd341fd29#32), -- lsr x9, x9, #1
  (1444, 0xb5ffffc9#32), -- cbnz x9, 0x24cf98 <.Llower_arm_1411>
  (1448, 0xaa0b03ea#32), -- mov x10, x11
  (1452, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (1456, 0xf94003e9#32), -- ldr x9, [sp]
  (1460, 0x910043ff#32), -- add sp, sp, #0x10
  (1464, 0x5280080d#32), -- mov w13, #0x40 // =64
  (1468, 0x4b0a01aa#32), -- sub w10, w13, w10
  (1472, 0xab0a016a#32), -- adds x10, x11, x10
  (1476, 0x54000062#32), -- b.hs 0x24cfcc <.Llower_arm_1413>
  (1480, 0xaa0c03eb#32), -- mov x11, x12
  (1484, 0x14000002#32), -- b 0x24cfd0 <.Llower_arm_1414>
  (1488, 0x9100058b#32), -- add x11, x12, #0x1
  (1492, 0xab08014a#32), -- adds x10, x10, x8
  (1496, 0x9a09016b#32), -- adc x11, x11, x9
  (1500, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1504, 0xf90003e9#32), -- str x9, [sp]
  (1508, 0xd346fd49#32), -- lsr x9, x10, #6
  (1512, 0xaa0be92c#32), -- orr x12, x9, x11, lsl #58
  (1516, 0xf94003e9#32), -- ldr x9, [sp]
  (1520, 0x910043ff#32), -- add sp, sp, #0x10
  (1524, 0xf240155f#32), -- tst x10, #0x3f
  (1528, 0xd346fd6a#32), -- lsr x10, x11, #6
  (1532, 0x54000061#32) -- b.ne 0x24d004 <.Llower_arm_1415>
]

theorem chunk5_decodes :
    chunk5.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk6 : List (Nat × BitVec 32) := [
  (1536, 0x5280000b#32), -- mov w11, #0x0 // =0
  (1540, 0x14000002#32), -- b 0x24d008 <.Llower_arm_1416>
  (1544, 0x5280002b#32), -- mov w11, #0x1 // =1
  (1548, 0xab0b018b#32), -- adds x11, x12, x11
  (1552, 0x54000062#32), -- b.hs 0x24d018 <.Llower_arm_1417>
  (1556, 0xaa0a03ea#32), -- mov x10, x10
  (1560, 0x14000002#32), -- b 0x24d01c <.Llower_arm_1418>
  (1564, 0x9100054a#32), -- add x10, x10, #0x1
  (1568, 0xb400062a#32), -- cbz x10, 0x24d0e0 <.LBB158_50>
  (1572, 0x52800028#32), -- mov w8, #0x1 // =1
  (1576, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1580, 0xf90003e9#32), -- str x9, [sp]
  (1584, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1588, 0x91000269#32), -- add x9, x19, #0x0
  (1592, 0x91004129#32), -- add x9, x9, #0x10
  (1596, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1600, 0xf900012a#32), -- str x10, [x9]
  (1604, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1608, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1612, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1616, 0xf94003e9#32), -- ldr x9, [sp]
  (1620, 0x910043ff#32), -- add sp, sp, #0x10
  (1624, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1628, 0xf90003e9#32), -- str x9, [sp]
  (1632, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1636, 0x91000269#32), -- add x9, x19, #0x0
  (1640, 0xf9000128#32), -- str x8, [x9]
  (1644, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1648, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1652, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1656, 0xf94003e9#32), -- ldr x9, [sp]
  (1660, 0x910043ff#32), -- add sp, sp, #0x10
  (1664, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1668, 0xf90003e9#32), -- str x9, [sp]
  (1672, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1676, 0x91000269#32), -- add x9, x19, #0x0
  (1680, 0x91008129#32), -- add x9, x9, #0x20
  (1684, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1688, 0xf900012a#32), -- str x10, [x9]
  (1692, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1696, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1700, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1704, 0xf94003e9#32), -- ldr x9, [sp]
  (1708, 0x910043ff#32), -- add sp, sp, #0x10
  (1712, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1716, 0xf90003e9#32), -- str x9, [sp]
  (1720, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1724, 0x91000269#32), -- add x9, x19, #0x0
  (1728, 0x9100c129#32), -- add x9, x9, #0x30
  (1732, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1736, 0xf900012a#32), -- str x10, [x9]
  (1740, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1744, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1748, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1752, 0xf94003e9#32), -- ldr x9, [sp]
  (1756, 0x910043ff#32), -- add sp, sp, #0x10
  (1760, 0x1400006c#32), -- b 0x24d28c <.LBB158_65>
  (1764, 0xb40001cb#32), -- cbz x11, 0x24d118 <.LBB158_54>
  (1768, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1772, 0xf90003ea#32), -- str x10, [sp]
  (1776, 0xd346fd0a#32), -- lsr x10, x8, #6
  (1780, 0xaa09e94c#32), -- orr x12, x10, x9, lsl #58
  (1784, 0xf94003ea#32), -- ldr x10, [sp]
  (1788, 0x910043ff#32) -- add sp, sp, #0x10
]

theorem chunk6_decodes :
    chunk6.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk7 : List (Nat × BitVec 32) := [
  (1792, 0x1200150d#32), -- and w13, w8, #0x3f
  (1796, 0xf100057f#32), -- cmp x11, #0x1
  (1800, 0x2a0d03ea#32), -- mov w10, w13
  (1804, 0x54000201#32), -- b.ne 0x24d148 <.LBB158_55>
  (1808, 0xb4000c6c#32), -- cbz x12, 0x24d298 <.LBB158_66>
  (1812, 0xaa1f03ea#32), -- mov x10, xzr
  (1816, 0x14000065#32), -- b 0x24d2a8 <.LBB158_70>
  (1820, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1824, 0xf90003e9#32), -- str x9, [sp]
  (1828, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (1832, 0x91000269#32), -- add x9, x19, #0x0
  (1836, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1840, 0xf900012a#32), -- str x10, [x9]
  (1844, 0xd280000a#32), -- mov x10, #0x0 // =0
  (1848, 0xf900052a#32), -- str x10, [x9, #0x8]
  (1852, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (1856, 0xf94003e9#32), -- ldr x9, [sp]
  (1860, 0x910043ff#32), -- add sp, sp, #0x10
  (1864, 0x17fffe5a#32), -- b 0x24caac <.LBB158_5>
  (1868, 0xd37dfd6e#32), -- lsr x14, x11, #61
  (1872, 0xb500042e#32), -- cbnz x14, 0x24d1d0 <.LBB158_64>
  (1876, 0xd37df16f#32), -- lsl x15, x11, #3
  (1880, 0xd10043ff#32), -- sub sp, sp, #0x10
  (1884, 0xf90003e9#32), -- str x9, [sp]
  (1888, 0x924101e9#32), -- and x9, x15, #0x8000000000000000
  (1892, 0xb5000089#32), -- cbnz x9, 0x24d170 <.Llower_arm_1419>
  (1896, 0xf94003e9#32), -- ldr x9, [sp]
  (1900, 0x910043ff#32), -- add sp, sp, #0x10
  (1904, 0x14000004#32), -- b 0x24d17c <.Llower_arm_1420>
  (1908, 0xf94003e9#32), -- ldr x9, [sp]
  (1912, 0x910043ff#32), -- add sp, sp, #0x10
  (1916, 0x14000016#32), -- b 0x24d1d0 <.LBB158_64>
  (1920, 0xf940028e#32), -- ldr x14, [x20]
  (1924, 0xf9400a90#32), -- ldr x16, [x20, #0x10]
  (1928, 0xab0e0211#32), -- adds x17, x16, x14
  (1932, 0x54000242#32), -- b.hs 0x24d1d0 <.LBB158_64>
  (1936, 0xb100223f#32), -- cmn x17, #0x8
  (1940, 0x54000208#32), -- b.hi 0x24d1d0 <.LBB158_64>
  (1944, 0x91001e32#32), -- add x18, x17, #0x7
  (1948, 0x927df252#32), -- and x18, x18, #0xfffffffffffffff8
  (1952, 0xcb110251#32), -- sub x17, x18, x17
  (1956, 0xab100230#32), -- adds x16, x17, x16
  (1960, 0x54000162#32), -- b.hs 0x24d1d0 <.LBB158_64>
  (1964, 0xab0f020f#32), -- adds x15, x16, x15
  (1968, 0x54000122#32), -- b.hs 0x24d1d0 <.LBB158_64>
  (1972, 0xf9400691#32), -- ldr x17, [x20, #0x8]
  (1976, 0xeb1101ff#32), -- cmp x15, x17
  (1980, 0x540000c8#32), -- b.hi 0x24d1d0 <.LBB158_64>
  (1984, 0x8b1001ce#32), -- add x14, x14, x16
  (1988, 0xf9000a8f#32), -- str x15, [x20, #0x10]
  (1992, 0xb400096c#32), -- cbz x12, 0x24d2f0 <.LBB158_74>
  (1996, 0xaa1f03f1#32), -- mov x17, xzr
  (2000, 0x14000051#32), -- b 0x24d310 <.LBB158_80>
  (2004, 0x52800028#32), -- mov w8, #0x1 // =1
  (2008, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2012, 0xf90003e9#32), -- str x9, [sp]
  (2016, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2020, 0x91000269#32), -- add x9, x19, #0x0
  (2024, 0x9100c129#32), -- add x9, x9, #0x30
  (2028, 0xd280000a#32), -- mov x10, #0x0 // =0
  (2032, 0xf900012a#32), -- str x10, [x9]
  (2036, 0xd280000a#32), -- mov x10, #0x0 // =0
  (2040, 0xf900052a#32), -- str x10, [x9, #0x8]
  (2044, 0xf94007ea#32) -- ldr x10, [sp, #0x8]
]

theorem chunk7_decodes :
    chunk7.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk8 : List (Nat × BitVec 32) := [
  (2048, 0xf94003e9#32), -- ldr x9, [sp]
  (2052, 0x910043ff#32), -- add sp, sp, #0x10
  (2056, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2060, 0xf90003e9#32), -- str x9, [sp]
  (2064, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2068, 0x91000269#32), -- add x9, x19, #0x0
  (2072, 0x91008129#32), -- add x9, x9, #0x20
  (2076, 0xd280000a#32), -- mov x10, #0x0 // =0
  (2080, 0xf900012a#32), -- str x10, [x9]
  (2084, 0xd280000a#32), -- mov x10, #0x0 // =0
  (2088, 0xf900052a#32), -- str x10, [x9, #0x8]
  (2092, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (2096, 0xf94003e9#32), -- ldr x9, [sp]
  (2100, 0x910043ff#32), -- add sp, sp, #0x10
  (2104, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2108, 0xf90003e9#32), -- str x9, [sp]
  (2112, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2116, 0x91000269#32), -- add x9, x19, #0x0
  (2120, 0x91004129#32), -- add x9, x9, #0x10
  (2124, 0xd280000a#32), -- mov x10, #0x0 // =0
  (2128, 0xf900012a#32), -- str x10, [x9]
  (2132, 0xd280000a#32), -- mov x10, #0x0 // =0
  (2136, 0xf900052a#32), -- str x10, [x9, #0x8]
  (2140, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (2144, 0xf94003e9#32), -- ldr x9, [sp]
  (2148, 0x910043ff#32), -- add sp, sp, #0x10
  (2152, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2156, 0xf90003e9#32), -- str x9, [sp]
  (2160, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (2164, 0x91000269#32), -- add x9, x19, #0x0
  (2168, 0xf9000128#32), -- str x8, [x9]
  (2172, 0xd280000a#32), -- mov x10, #0x0 // =0
  (2176, 0xf900052a#32), -- str x10, [x9, #0x8]
  (2180, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (2184, 0xf94003e9#32), -- ldr x9, [sp]
  (2188, 0x910043ff#32), -- add sp, sp, #0x10
  (2192, 0x52900008#32), -- mov w8, #0x8000 // =32768
  (2196, 0xb9004268#32), -- str w8, [x19, #0x40]
  (2200, 0x17fffe10#32), -- b 0x24cad4 <.LBB158_6>
  (2204, 0xb4000077#32), -- cbz x23, 0x24d2a4 <.LBB158_69>
  (2208, 0xb4000056#32), -- cbz x22, 0x24d2a4 <.LBB158_69>
  (2212, 0xf94002f6#32), -- ldr x22, [x23]
  (2216, 0x9aca22ca#32), -- lsl x10, x22, x10
  (2220, 0xb4000078#32), -- cbz x24, 0x24d2b4 <.LBB158_73>
  (2224, 0xb4000055#32), -- cbz x21, 0x24d2b4 <.LBB158_73>
  (2228, 0xf9400315#32), -- ldr x21, [x24]
  (2232, 0xf101011f#32), -- cmp x8, #0x40
  (2236, 0x5280080b#32), -- mov w11, #0x40 // =64
  (2240, 0x9a8b3108#32), -- csel x8, x8, x11, lo
  (2244, 0xf100013f#32), -- cmp x9, #0x0
  (2248, 0x92800009#32), -- mov x9, #-0x1 // =-1
  (2252, 0x1a8b0108#32), -- csel w8, w8, w11, eq
  (2256, 0x9ac8212b#32), -- lsl x11, x9, x8
  (2260, 0x7101011f#32), -- cmp w8, #0x40
  (2264, 0x54000060#32), -- b.eq 0x24d2e0 <.Llower_arm_1421>
  (2268, 0xaa2b03e8#32), -- mvn x8, x11
  (2272, 0x14000002#32), -- b 0x24d2e4 <.Llower_arm_1422>
  (2276, 0xaa0903e8#32), -- mov x8, x9
  (2280, 0x8a150108#32), -- and x8, x8, x21
  (2284, 0xaa0a0108#32), -- orr x8, x8, x10
  (2288, 0x17fffde6#32), -- b 0x24ca84 <.LBB158_4>
  (2292, 0xb4000097#32), -- cbz x23, 0x24d300 <.LBB158_77>
  (2296, 0xb40000b6#32), -- cbz x22, 0x24d308 <.LBB158_78>
  (2300, 0xf94002ef#32) -- ldr x15, [x23]
]

theorem chunk8_decodes :
    chunk8.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk9 : List (Nat × BitVec 32) := [
  (2304, 0x14000004#32), -- b 0x24d30c <.LBB158_79>
  (2308, 0xaa1603ef#32), -- mov x15, x22
  (2312, 0x14000002#32), -- b 0x24d30c <.LBB158_79>
  (2316, 0xaa1f03ef#32), -- mov x15, xzr
  (2320, 0x9aca21f1#32), -- lsl x17, x15, x10
  (2324, 0xb4000098#32), -- cbz x24, 0x24d320 <.LBB158_83>
  (2328, 0xb40000b5#32), -- cbz x21, 0x24d328 <.LBB158_84>
  (2332, 0xf9400312#32), -- ldr x18, [x24]
  (2336, 0x14000004#32), -- b 0x24d32c <.LBB158_85>
  (2340, 0xaa1503f2#32), -- mov x18, x21
  (2344, 0x14000002#32), -- b 0x24d32c <.LBB158_85>
  (2348, 0xaa1f03f2#32), -- mov x18, xzr
  (2352, 0xf101011f#32), -- cmp x8, #0x40
  (2356, 0x5280080f#32), -- mov w15, #0x40 // =64
  (2360, 0x92800010#32), -- mov x16, #-0x1 // =-1
  (2364, 0x9a8f3100#32), -- csel x0, x8, x15, lo
  (2368, 0xf100013f#32), -- cmp x9, #0x0
  (2372, 0x1a8f0000#32), -- csel w0, w0, w15, eq
  (2376, 0x9ac02201#32), -- lsl x1, x16, x0
  (2380, 0x7101001f#32), -- cmp w0, #0x40
  (2384, 0x54000060#32), -- b.eq 0x24d358 <.Llower_arm_1423>
  (2388, 0xaa2103e0#32), -- mvn x0, x1
  (2392, 0x14000002#32), -- b 0x24d35c <.Llower_arm_1424>
  (2396, 0xaa1003e0#32), -- mov x0, x16
  (2400, 0xcb0c0ee1#32), -- sub x1, x23, x12, lsl #3
  (2404, 0x8a120012#32), -- and x18, x0, x18
  (2408, 0x4b0803e0#32), -- neg w0, w8
  (2412, 0xaa110242#32), -- orr x2, x18, x17
  (2416, 0x9aca22d1#32), -- lsl x17, x22, x10
  (2420, 0x12001412#32), -- and w18, w0, #0x3f
  (2424, 0xf90001c2#32), -- str x2, [x14]
  (2428, 0xcb0c03e0#32), -- neg x0, x12
  (2432, 0x91002021#32), -- add x1, x1, #0x8
  (2436, 0x52800022#32), -- mov w2, #0x1 // =1
  (2440, 0x1400001f#32), -- b 0x24d400 <.LBB158_87>
  (2444, 0xd37afc45#32), -- lsr x5, x2, #58
  (2448, 0xeb021906#32), -- subs x6, x8, x2, lsl #6
  (2452, 0x91002021#32), -- add x1, x1, #0x8
  (2456, 0xfa050125#32), -- sbcs x5, x9, x5
  (2460, 0x9a8633e6#32), -- csel x6, xzr, x6, lo
  (2464, 0x9a8533e5#32), -- csel x5, xzr, x5, lo
  (2468, 0xf10100df#32), -- cmp x6, #0x40
  (2472, 0x9a8f30c6#32), -- csel x6, x6, x15, lo
  (2476, 0xf10000bf#32), -- cmp x5, #0x0
  (2480, 0x1a8f00c5#32), -- csel w5, w6, w15, eq
  (2484, 0x9ac52206#32), -- lsl x6, x16, x5
  (2488, 0x710100bf#32), -- cmp w5, #0x40
  (2492, 0x54000060#32), -- b.eq 0x24d3c4 <.Llower_arm_1425>
  (2496, 0xaa2603e5#32), -- mvn x5, x6
  (2500, 0x14000002#32), -- b 0x24d3c8 <.Llower_arm_1426>
  (2504, 0xaa1003e5#32), -- mov x5, x16
  (2508, 0x8a0400a4#32), -- and x4, x5, x4
  (2512, 0x91000445#32), -- add x5, x2, #0x1
  (2516, 0xaa030083#32), -- orr x3, x4, x3
  (2520, 0xeb05017f#32), -- cmp x11, x5
  (2524, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2528, 0xf90003e9#32), -- str x9, [sp]
  (2532, 0xaa0203e9#32), -- mov x9, x2
  (2536, 0xd37df129#32), -- lsl x9, x9, #3
  (2540, 0x8b0901c9#32), -- add x9, x14, x9
  (2544, 0xf9000123#32), -- str x3, [x9]
  (2548, 0xf94003e9#32), -- ldr x9, [sp]
  (2552, 0x910043ff#32), -- add sp, sp, #0x10
  (2556, 0xaa0503e2#32) -- mov x2, x5
]

theorem chunk9_decodes :
    chunk9.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk10 : List (Nat × BitVec 32) := [
  (2560, 0x54000660#32), -- b.eq 0x24d4c8 <.LBB158_105>
  (2564, 0xeb0c005f#32), -- cmp x2, x12
  (2568, 0x54000062#32), -- b.hs 0x24d410 <.LBB158_89>
  (2572, 0xaa1f03e3#32), -- mov x3, xzr
  (2576, 0x14000022#32), -- b 0x24d494 <.LBB158_102>
  (2580, 0x8b020004#32), -- add x4, x0, x2
  (2584, 0xb40000b7#32), -- cbz x23, 0x24d428 <.LBB158_92>
  (2588, 0xeb16009f#32), -- cmp x4, x22
  (2592, 0x54000162#32), -- b.hs 0x24d448 <.LBB158_95>
  (2596, 0xf9400023#32), -- ldr x3, [x1]
  (2600, 0x1400000a#32), -- b 0x24d44c <.LBB158_96>
  (2604, 0xf100009f#32), -- cmp x4, #0x0
  (2608, 0x9a9f0223#32), -- csel x3, x17, xzr, eq
  (2612, 0xb4000324#32), -- cbz x4, 0x24d494 <.LBB158_102>
  (2616, 0x3400030a#32), -- cbz w10, 0x24d494 <.LBB158_102>
  (2620, 0xf100049f#32), -- cmp x4, #0x1
  (2624, 0xaa1f03e3#32), -- mov x3, xzr
  (2628, 0x9a9f02c4#32), -- csel x4, x22, xzr, eq
  (2632, 0x14000012#32), -- b 0x24d48c <.LBB158_101>
  (2636, 0xaa1f03e3#32), -- mov x3, xzr
  (2640, 0x9acd2063#32), -- lsl x3, x3, x13
  (2644, 0xb4000224#32), -- cbz x4, 0x24d494 <.LBB158_102>
  (2648, 0x3400020a#32), -- cbz w10, 0x24d494 <.LBB158_102>
  (2652, 0x8b020004#32), -- add x4, x0, x2
  (2656, 0xd1000484#32), -- sub x4, x4, #0x1
  (2660, 0xeb16009f#32), -- cmp x4, x22
  (2664, 0x54000122#32), -- b.hs 0x24d488 <.LBB158_100>
  (2668, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2672, 0xf90003e9#32), -- str x9, [sp]
  (2676, 0x91000029#32), -- add x9, x1, #0x0
  (2680, 0xd1002129#32), -- sub x9, x9, #0x8
  (2684, 0xf9400124#32), -- ldr x4, [x9]
  (2688, 0xf94003e9#32), -- ldr x9, [sp]
  (2692, 0x910043ff#32), -- add sp, sp, #0x10
  (2696, 0x14000002#32), -- b 0x24d48c <.LBB158_101>
  (2700, 0xaa1f03e4#32), -- mov x4, xzr
  (2704, 0x9ad22484#32), -- lsr x4, x4, x18
  (2708, 0xaa030083#32), -- orr x3, x4, x3
  (2712, 0xaa1f03e4#32), -- mov x4, xzr
  (2716, 0xb4fff798#32), -- cbz x24, 0x24d388 <.LBB158_86>
  (2720, 0xeb15005f#32), -- cmp x2, x21
  (2724, 0x54fff742#32), -- b.hs 0x24d388 <.LBB158_86>
  (2728, 0xd10043ff#32), -- sub sp, sp, #0x10
  (2732, 0xf90003e9#32), -- str x9, [sp]
  (2736, 0xaa0203e9#32), -- mov x9, x2
  (2740, 0xd37df129#32), -- lsl x9, x9, #3
  (2744, 0x8b090309#32), -- add x9, x24, x9
  (2748, 0xf9400124#32), -- ldr x4, [x9]
  (2752, 0xf94003e9#32), -- ldr x9, [sp]
  (2756, 0x910043ff#32), -- add sp, sp, #0x10
  (2760, 0x17ffffb1#32), -- b 0x24d388 <.LBB158_86>
  (2764, 0xa9002e6e#32), -- stp x14, x11, [x19]
  (2768, 0x17fffd78#32) -- b 0x24caac <.LBB158_5>
]

theorem chunk10_decodes :
    chunk10.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete linked function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 ++ chunk8 ++ chunk9 ++ chunk10

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

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, chunk3_decodes, chunk4_decodes, chunk5_decodes, chunk6_decodes, chunk7_decodes, chunk8_decodes, chunk9_decodes, chunk10_decodes, Bool.and_self]

theorem step_at (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (row : Nat × BitVec 32) (member : row ∈ program)
    (entry : read_pc s = base + BitVec.ofNat 64 row.1)
    (error : read_err s = .None) :
    stepi s = exec_inst (SszArm.Codec.Linked.decoded program all_decode row member) s :=
  SszArm.Codec.Linked.step_at program all_decode s base code row member entry error

end SszArm.Indices.Linked.GeneralizedIndex
