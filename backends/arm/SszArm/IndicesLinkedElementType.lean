import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.ElementType

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN13ssz_fv_native7indices12element_type17hc2546e08b1adae5eE. -/
def address : Nat := 2260288

def byteSize : Nat := 980

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xa9bf4ffe#32), -- stp x30, x19, [sp, #-0x10]!
  (4, 0xf9400028#32), -- ldr x8, [x1]
  (8, 0xf9400049#32), -- ldr x9, [x2]
  (12, 0xf100191f#32), -- cmp x8, #0x6
  (16, 0xb40000e9#32), -- cbz x9, 0x227d6c <.LBB58_4>
  (20, 0x540000ed#32), -- b.le 0x227d70 <.LBB58_5>
  (24, 0xd1001d09#32), -- sub x9, x8, #0x7
  (28, 0xf100093f#32), -- cmp x9, #0x2
  (32, 0x54000782#32), -- b.hs 0x227e50 <.LBB58_11>
  (36, 0x52800308#32), -- mov w8, #0x18 // =24
  (40, 0x1400003d#32), -- b 0x227e5c <.LBB58_13>
  (44, 0x5400068c#32), -- b.gt 0x227e3c <.LBB58_9>
  (48, 0xd1001109#32), -- sub x9, x8, #0x4
  (52, 0xf1000d3f#32), -- cmp x9, #0x3
  (56, 0x540002c2#32), -- b.hs 0x227dd0 <.LBB58_7>
  (60, 0xd10043ff#32), -- sub sp, sp, #0x10
  (64, 0xf90003e9#32), -- str x9, [sp]
  (68, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (72, 0x91000009#32), -- add x9, x0, #0x0
  (76, 0xd280000a#32), -- mov x10, #0x0 // =0
  (80, 0xf900012a#32), -- str x10, [x9]
  (84, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (88, 0xf94003e9#32), -- ldr x9, [sp]
  (92, 0x910043ff#32), -- add sp, sp, #0x10
  (96, 0xd10043ff#32), -- sub sp, sp, #0x10
  (100, 0xf90003e9#32), -- str x9, [sp]
  (104, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (108, 0x91000009#32), -- add x9, x0, #0x0
  (112, 0x91010129#32), -- add x9, x9, #0x40
  (116, 0x5280000a#32), -- mov w10, #0x0 // =0
  (120, 0xb900012a#32), -- str w10, [x9]
  (124, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (128, 0xf94003e9#32), -- ldr x9, [sp]
  (132, 0x910043ff#32), -- add sp, sp, #0x10
  (136, 0xa8c14ffe#32), -- ldp x30, x19, [sp], #0x10
  (140, 0xd65f03c0#32), -- ret
  (144, 0xd1000908#32), -- sub x8, x8, #0x2
  (148, 0xf100091f#32), -- cmp x8, #0x2
  (152, 0x54000802#32), -- b.hs 0x227ed8 <.LBB58_17>
  (156, 0x52800028#32), -- mov w8, #0x1 // =1
  (160, 0xd10043ff#32), -- sub sp, sp, #0x10
  (164, 0xf90003e9#32), -- str x9, [sp]
  (168, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (172, 0x91000009#32), -- add x9, x0, #0x0
  (176, 0x91010129#32), -- add x9, x9, #0x40
  (180, 0x5280000a#32), -- mov w10, #0x0 // =0
  (184, 0xb900012a#32), -- str w10, [x9]
  (188, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (192, 0xf94003e9#32), -- ldr x9, [sp]
  (196, 0x910043ff#32), -- add sp, sp, #0x10
  (200, 0xd10043ff#32), -- sub sp, sp, #0x10
  (204, 0xf90003e9#32), -- str x9, [sp]
  (208, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (212, 0x91000009#32), -- add x9, x0, #0x0
  (216, 0xf9000128#32), -- str x8, [x9]
  (220, 0xd280000a#32), -- mov x10, #0x0 // =0
  (224, 0xf900052a#32), -- str x10, [x9, #0x8]
  (228, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (232, 0xf94003e9#32), -- ldr x9, [sp]
  (236, 0x910043ff#32), -- add sp, sp, #0x10
  (240, 0xf9000808#32), -- str x8, [x0, #0x10]
  (244, 0xa8c14ffe#32), -- ldp x30, x19, [sp], #0x10
  (248, 0xd65f03c0#32), -- ret
  (252, 0xf100251f#32) -- cmp x8, #0x9
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0x540003ac#32), -- b.gt 0x227eb4 <.LBB58_14>
  (260, 0xd1001d09#32), -- sub x9, x8, #0x7
  (264, 0xf100093f#32), -- cmp x9, #0x2
  (268, 0x54fff8c3#32), -- b.lo 0x227d64 <.LBB58_3>
  (272, 0xf100251f#32), -- cmp x8, #0x9
  (276, 0x54000421#32), -- b.ne 0x227ed8 <.LBB58_17>
  (280, 0x52800108#32), -- mov w8, #0x8 // =8
  (284, 0xd10043ff#32), -- sub sp, sp, #0x10
  (288, 0xf90003e9#32), -- str x9, [sp]
  (292, 0xaa0803e9#32), -- mov x9, x8
  (296, 0x8b090029#32), -- add x9, x1, x9
  (300, 0xf9400121#32), -- ldr x1, [x9]
  (304, 0xf94003e9#32), -- ldr x9, [sp]
  (308, 0x910043ff#32), -- add sp, sp, #0x10
  (312, 0x52800502#32), -- mov w2, #0x28 // =40
  (316, 0xaa0003f3#32), -- mov x19, x0
  (320, 0x94009594#32), -- bl 0x24d4d0 <memcpy>
  (324, 0xd10043ff#32), -- sub sp, sp, #0x10
  (328, 0xf90003e9#32), -- str x9, [sp]
  (332, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (336, 0x91000269#32), -- add x9, x19, #0x0
  (340, 0x91010129#32), -- add x9, x9, #0x40
  (344, 0x5280000a#32), -- mov w10, #0x0 // =0
  (348, 0xb900012a#32), -- str w10, [x9]
  (352, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (356, 0xf94003e9#32), -- ldr x9, [sp]
  (360, 0x910043ff#32), -- add sp, sp, #0x10
  (364, 0xa8c14ffe#32), -- ldp x30, x19, [sp], #0x10
  (368, 0xd65f03c0#32), -- ret
  (372, 0xf100291f#32), -- cmp x8, #0xa
  (376, 0x54000760#32), -- b.eq 0x227fa4 <.LBB58_18>
  (380, 0xf1002d1f#32), -- cmp x8, #0xb
  (384, 0x540000c1#32), -- b.ne 0x227ed8 <.LBB58_17>
  (388, 0x5280030a#32), -- mov w10, #0x18 // =24
  (392, 0xa940a049#32), -- ldp x9, x8, [x2, #0x8]
  (396, 0xaa0803eb#32), -- mov x11, x8
  (400, 0xb5000729#32), -- cbnz x9, 0x227fb4 <.LBB58_19>
  (404, 0x1400004c#32), -- b 0x228004 <.LBB58_25>
  (408, 0x52800028#32), -- mov w8, #0x1 // =1
  (412, 0xd10043ff#32), -- sub sp, sp, #0x10
  (416, 0xf90003e9#32), -- str x9, [sp]
  (420, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (424, 0x91000009#32), -- add x9, x0, #0x0
  (428, 0x91004129#32), -- add x9, x9, #0x10
  (432, 0xd280000a#32), -- mov x10, #0x0 // =0
  (436, 0xf900012a#32), -- str x10, [x9]
  (440, 0xd280000a#32), -- mov x10, #0x0 // =0
  (444, 0xf900052a#32), -- str x10, [x9, #0x8]
  (448, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (452, 0xf94003e9#32), -- ldr x9, [sp]
  (456, 0x910043ff#32), -- add sp, sp, #0x10
  (460, 0xd10043ff#32), -- sub sp, sp, #0x10
  (464, 0xf90003e9#32), -- str x9, [sp]
  (468, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (472, 0x91000009#32), -- add x9, x0, #0x0
  (476, 0xf9000128#32), -- str x8, [x9]
  (480, 0xd280000a#32), -- mov x10, #0x0 // =0
  (484, 0xf900052a#32), -- str x10, [x9, #0x8]
  (488, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (492, 0xf94003e9#32), -- ldr x9, [sp]
  (496, 0x910043ff#32), -- add sp, sp, #0x10
  (500, 0x52800708#32), -- mov w8, #0x38 // =56
  (504, 0xd10043ff#32), -- sub sp, sp, #0x10
  (508, 0xf90003e9#32) -- str x9, [sp]
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (516, 0x91000009#32), -- add x9, x0, #0x0
  (520, 0x91008129#32), -- add x9, x9, #0x20
  (524, 0xd280000a#32), -- mov x10, #0x0 // =0
  (528, 0xf900012a#32), -- str x10, [x9]
  (532, 0xd280000a#32), -- mov x10, #0x0 // =0
  (536, 0xf900052a#32), -- str x10, [x9, #0x8]
  (540, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (544, 0xf94003e9#32), -- ldr x9, [sp]
  (548, 0x910043ff#32), -- add sp, sp, #0x10
  (552, 0xd10043ff#32), -- sub sp, sp, #0x10
  (556, 0xf90003e9#32), -- str x9, [sp]
  (560, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (564, 0x91000009#32), -- add x9, x0, #0x0
  (568, 0x9100c129#32), -- add x9, x9, #0x30
  (572, 0xd280000a#32), -- mov x10, #0x0 // =0
  (576, 0xf900012a#32), -- str x10, [x9]
  (580, 0xd280000a#32), -- mov x10, #0x0 // =0
  (584, 0xf900052a#32), -- str x10, [x9, #0x8]
  (588, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (592, 0xf94003e9#32), -- ldr x9, [sp]
  (596, 0x910043ff#32), -- add sp, sp, #0x10
  (600, 0xb9004008#32), -- str w8, [x0, #0x40]
  (604, 0xa8c14ffe#32), -- ldp x30, x19, [sp], #0x10
  (608, 0xd65f03c0#32), -- ret
  (612, 0x5280010a#32), -- mov w10, #0x8 // =8
  (616, 0xa940a049#32), -- ldp x9, x8, [x2, #0x8]
  (620, 0xaa0803eb#32), -- mov x11, x8
  (624, 0xb40002a9#32), -- cbz x9, 0x228004 <.LBB58_25>
  (628, 0xd100050c#32), -- sub x12, x8, #0x1
  (632, 0xb100059f#32), -- cmn x12, #0x1
  (636, 0x54000200#32), -- b.eq 0x227ffc <.LBB58_23>
  (640, 0xd10043ff#32), -- sub sp, sp, #0x10
  (644, 0xf90003ea#32), -- str x10, [sp]
  (648, 0xaa0c03ea#32), -- mov x10, x12
  (652, 0xd37df14a#32), -- lsl x10, x10, #3
  (656, 0x8b0a012a#32), -- add x10, x9, x10
  (660, 0xf940014d#32), -- ldr x13, [x10]
  (664, 0xf94003ea#32), -- ldr x10, [sp]
  (668, 0x910043ff#32), -- add sp, sp, #0x10
  (672, 0xaa0c03eb#32), -- mov x11, x12
  (676, 0xd100058c#32), -- sub x12, x12, #0x1
  (680, 0xb4fffe8d#32), -- cbz x13, 0x227fb8 <.LBB58_20>
  (684, 0x9100056b#32), -- add x11, x11, #0x1
  (688, 0xf100057f#32), -- cmp x11, #0x1
  (692, 0x54000060#32), -- b.eq 0x228000 <.LBB58_24>
  (696, 0x1400001f#32), -- b 0x228074 <.LBB58_28>
  (700, 0xb4000328#32), -- cbz x8, 0x228060 <.LBB58_27>
  (704, 0xf940012b#32), -- ldr x11, [x9]
  (708, 0x8b0a002a#32), -- add x10, x1, x10
  (712, 0xf940054c#32), -- ldr x12, [x10, #0x8]
  (716, 0xeb0c017f#32), -- cmp x11, x12
  (720, 0x54000322#32), -- b.hs 0x228074 <.LBB58_28>
  (724, 0x52800308#32), -- mov w8, #0x18 // =24
  (728, 0xf9400149#32), -- ldr x9, [x10]
  (732, 0x9b082568#32), -- madd x8, x11, x8, x9
  (736, 0xf9400901#32), -- ldr x1, [x8, #0x10]
  (740, 0x52800502#32), -- mov w2, #0x28 // =40
  (744, 0xaa0003f3#32), -- mov x19, x0
  (748, 0x94009529#32), -- bl 0x24d4d0 <memcpy>
  (752, 0xd10043ff#32), -- sub sp, sp, #0x10
  (756, 0xf90003e9#32), -- str x9, [sp]
  (760, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (764, 0x91000269#32) -- add x9, x19, #0x0
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0x91010129#32), -- add x9, x9, #0x40
  (772, 0x5280000a#32), -- mov w10, #0x0 // =0
  (776, 0xb900012a#32), -- str w10, [x9]
  (780, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (784, 0xf94003e9#32), -- ldr x9, [sp]
  (788, 0x910043ff#32), -- add sp, sp, #0x10
  (792, 0xa8c14ffe#32), -- ldp x30, x19, [sp], #0x10
  (796, 0xd65f03c0#32), -- ret
  (800, 0xaa1f03eb#32), -- mov x11, xzr
  (804, 0x8b0a002a#32), -- add x10, x1, x10
  (808, 0xf940054c#32), -- ldr x12, [x10, #0x8]
  (812, 0xeb0c03ff#32), -- cmp xzr, x12
  (816, 0x54fffd23#32), -- b.lo 0x228014 <.LBB58_26>
  (820, 0x5280002a#32), -- mov w10, #0x1 // =1
  (824, 0xa9012009#32), -- stp x9, x8, [x0, #0x10]
  (828, 0x52800728#32), -- mov w8, #0x39 // =57
  (832, 0xd10043ff#32), -- sub sp, sp, #0x10
  (836, 0xf90003e9#32), -- str x9, [sp]
  (840, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (844, 0x91000009#32), -- add x9, x0, #0x0
  (848, 0xf900012a#32), -- str x10, [x9]
  (852, 0xd280000b#32), -- mov x11, #0x0 // =0
  (856, 0xf900052b#32), -- str x11, [x9, #0x8]
  (860, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (864, 0xf94003e9#32), -- ldr x9, [sp]
  (868, 0x910043ff#32), -- add sp, sp, #0x10
  (872, 0xd10043ff#32), -- sub sp, sp, #0x10
  (876, 0xf90003e9#32), -- str x9, [sp]
  (880, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (884, 0x91000009#32), -- add x9, x0, #0x0
  (888, 0x91008129#32), -- add x9, x9, #0x20
  (892, 0xd280000a#32), -- mov x10, #0x0 // =0
  (896, 0xf900012a#32), -- str x10, [x9]
  (900, 0xd280000a#32), -- mov x10, #0x0 // =0
  (904, 0xf900052a#32), -- str x10, [x9, #0x8]
  (908, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (912, 0xf94003e9#32), -- ldr x9, [sp]
  (916, 0x910043ff#32), -- add sp, sp, #0x10
  (920, 0xd10043ff#32), -- sub sp, sp, #0x10
  (924, 0xf90003e9#32), -- str x9, [sp]
  (928, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (932, 0x91000009#32), -- add x9, x0, #0x0
  (936, 0x9100c129#32), -- add x9, x9, #0x30
  (940, 0xd280000a#32), -- mov x10, #0x0 // =0
  (944, 0xf900012a#32), -- str x10, [x9]
  (948, 0xd280000a#32), -- mov x10, #0x0 // =0
  (952, 0xf900052a#32), -- str x10, [x9, #0x8]
  (956, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (960, 0xf94003e9#32), -- ldr x9, [sp]
  (964, 0x910043ff#32), -- add sp, sp, #0x10
  (968, 0xb9004008#32), -- str w8, [x0, #0x40]
  (972, 0xa8c14ffe#32), -- ldp x30, x19, [sp], #0x10
  (976, 0xd65f03c0#32) -- ret
]

theorem chunk3_decodes :
    chunk3.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete linked function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3

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

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, chunk3_decodes, Bool.and_self]

theorem step_at (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (row : Nat × BitVec 32) (member : row ∈ program)
    (entry : read_pc s = base + BitVec.ofNat 64 row.1)
    (error : read_err s = .None) :
    stepi s = exec_inst (SszArm.Codec.Linked.decoded program all_decode row member) s :=
  SszArm.Codec.Linked.step_at program all_decode s base code row member entry error

end SszArm.Indices.Linked.ElementType
