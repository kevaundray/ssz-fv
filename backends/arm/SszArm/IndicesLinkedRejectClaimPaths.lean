import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.RejectClaimPaths

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN13ssz_fv_native7indices18reject_claim_paths17hef042388294333e5E. -/
def address : Nat := 2385632

def byteSize : Nat := 940

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10283ff#32), -- sub sp, sp, #0xa0
  (4, 0xa9047bfd#32), -- stp x29, x30, [sp, #0x40]
  (8, 0xa9056ffc#32), -- stp x28, x27, [sp, #0x50]
  (12, 0xa90667fa#32), -- stp x26, x25, [sp, #0x60]
  (16, 0xa9075ff8#32), -- stp x24, x23, [sp, #0x70]
  (20, 0xa90857f6#32), -- stp x22, x21, [sp, #0x80]
  (24, 0xa9094ff4#32), -- stp x20, x19, [sp, #0x90]
  (28, 0xaa0303f6#32), -- mov x22, x3
  (32, 0xaa0003f3#32), -- mov x19, x0
  (36, 0x8b04106c#32), -- add x12, x3, x4, lsl #4
  (40, 0x8b021039#32), -- add x25, x1, x2, lsl #4
  (44, 0x5280080d#32), -- mov w13, #0x40 // =64
  (48, 0x5280002e#32), -- mov w14, #0x1 // =1
  (52, 0x9280001c#32), -- mov x28, #-0x1 // =-1
  (56, 0xa94052d5#32), -- ldp x21, x20, [x22]
  (60, 0xb4000415#32), -- cbz x21, 0x24679c <.LBB134_9>
  (64, 0xd10022a8#32), -- sub x8, x21, #0x8
  (68, 0xaa1403e9#32), -- mov x9, x20
  (72, 0xb40018a9#32), -- cbz x9, 0x246a3c <.LBB134_29>
  (76, 0xd10043ff#32), -- sub sp, sp, #0x10
  (80, 0xf90003eb#32), -- str x11, [sp]
  (84, 0xaa0903eb#32), -- mov x11, x9
  (88, 0xd37df16b#32), -- lsl x11, x11, #3
  (92, 0x8b0b010b#32), -- add x11, x8, x11
  (96, 0xf940016a#32), -- ldr x10, [x11]
  (100, 0xf94003eb#32), -- ldr x11, [sp]
  (104, 0x910043ff#32), -- add sp, sp, #0x10
  (108, 0xd1000529#32), -- sub x9, x9, #0x1
  (112, 0xb4fffeca#32), -- cbz x10, 0x246728 <.LBB134_3>
  (116, 0xaa1403eb#32), -- mov x11, x20
  (120, 0xb400116b#32), -- cbz x11, 0x246984 <.LBB134_26>
  (124, 0xd10043ff#32), -- sub sp, sp, #0x10
  (128, 0xf90003ea#32), -- str x10, [sp]
  (132, 0xaa0b03ea#32), -- mov x10, x11
  (136, 0xd37df14a#32), -- lsl x10, x10, #3
  (140, 0x8b0a010a#32), -- add x10, x8, x10
  (144, 0xf9400149#32), -- ldr x9, [x10]
  (148, 0xf94003ea#32), -- ldr x10, [sp]
  (152, 0x910043ff#32), -- add sp, sp, #0x10
  (156, 0xaa0b03ea#32), -- mov x10, x11
  (160, 0xd100056b#32), -- sub x11, x11, #0x1
  (164, 0xb4fffea9#32), -- cbz x9, 0x246758 <.LBB134_6>
  (168, 0xd37ae548#32), -- lsl x8, x10, #6
  (172, 0xd37afd4a#32), -- lsr x10, x10, #58
  (176, 0xf1010108#32), -- subs x8, x8, #0x40
  (180, 0x9a1c014a#32), -- adc x10, x10, x28
  (184, 0x14000005#32), -- b 0x2467ac <.LBB134_11>
  (188, 0xb40014f4#32), -- cbz x20, 0x246a38 <.LBB134_28>
  (192, 0xaa1f03e8#32), -- mov x8, xzr
  (196, 0xaa1f03ea#32), -- mov x10, xzr
  (200, 0xaa1403e9#32), -- mov x9, x20
  (204, 0xd10043ff#32), -- sub sp, sp, #0x10
  (208, 0xf90003ea#32), -- str x10, [sp]
  (212, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (216, 0xaa0903ea#32), -- mov x10, x9
  (220, 0xd280080b#32), -- mov x11, #0x40 // =64
  (224, 0xb400008a#32), -- cbz x10, 0x2467d0 <.Llower_arm_1276>
  (228, 0xd100056b#32), -- sub x11, x11, #0x1
  (232, 0xd341fd4a#32), -- lsr x10, x10, #1
  (236, 0xb5ffffca#32), -- cbnz x10, 0x2467c4 <.Llower_arm_1275>
  (240, 0xaa0b03e9#32), -- mov x9, x11
  (244, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (248, 0xf94003ea#32), -- ldr x10, [sp]
  (252, 0x910043ff#32) -- add sp, sp, #0x10
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0x4b0901a9#32), -- sub w9, w13, w9
  (260, 0xab09011d#32), -- adds x29, x8, x9
  (264, 0x54000062#32), -- b.hs 0x2467f4 <.Llower_arm_1277>
  (268, 0xaa0a03fb#32), -- mov x27, x10
  (272, 0x14000002#32), -- b 0x2467f8 <.Llower_arm_1278>
  (276, 0x9100055b#32), -- add x27, x10, #0x1
  (280, 0xeb1d01df#32), -- cmp x14, x29
  (284, 0xfa1b03ff#32), -- ngcs xzr, x27
  (288, 0x54000c22#32), -- b.hs 0x246984 <.LBB134_26>
  (292, 0xf10007b8#32), -- subs x24, x29, #0x1
  (296, 0x910042d6#32), -- add x22, x22, #0x10
  (300, 0xaa0103fa#32), -- mov x26, x1
  (304, 0x9a1c0377#32), -- adc x23, x27, x28
  (308, 0xa90107ec#32), -- stp x12, x1, [sp, #0x10]
  (312, 0x14000004#32), -- b 0x246828 <.LBB134_14>
  (316, 0x9100435a#32), -- add x26, x26, #0x10
  (320, 0xeb19035f#32), -- cmp x26, x25
  (324, 0x54000920#32), -- b.eq 0x246948 <.LBB134_24>
  (328, 0xa9401b45#32), -- ldp x5, x6, [x26]
  (332, 0xb4000285#32), -- cbz x5, 0x24687c <.LBB134_19>
  (336, 0xd10020a9#32), -- sub x9, x5, #0x8
  (340, 0xaa0603eb#32), -- mov x11, x6
  (344, 0xb4ffff2b#32), -- cbz x11, 0x24681c <.LBB134_13>
  (348, 0xd10043ff#32), -- sub sp, sp, #0x10
  (352, 0xf90003ea#32), -- str x10, [sp]
  (356, 0xaa0b03ea#32), -- mov x10, x11
  (360, 0xd37df14a#32), -- lsl x10, x10, #3
  (364, 0x8b0a012a#32), -- add x10, x9, x10
  (368, 0xf9400148#32), -- ldr x8, [x10]
  (372, 0xf94003ea#32), -- ldr x10, [sp]
  (376, 0x910043ff#32), -- add sp, sp, #0x10
  (380, 0xaa0b03ea#32), -- mov x10, x11
  (384, 0xd100056b#32), -- sub x11, x11, #0x1
  (388, 0xb4fffea8#32), -- cbz x8, 0x246838 <.LBB134_16>
  (392, 0xd37ae549#32), -- lsl x9, x10, #6
  (396, 0xd37afd4a#32), -- lsr x10, x10, #58
  (400, 0xf1010129#32), -- subs x9, x9, #0x40
  (404, 0x9a1c014a#32), -- adc x10, x10, x28
  (408, 0x14000005#32), -- b 0x24688c <.LBB134_21>
  (412, 0xb4fffd06#32), -- cbz x6, 0x24681c <.LBB134_13>
  (416, 0xaa1f03e9#32), -- mov x9, xzr
  (420, 0xaa1f03ea#32), -- mov x10, xzr
  (424, 0xaa0603e8#32), -- mov x8, x6
  (428, 0xd10043ff#32), -- sub sp, sp, #0x10
  (432, 0xf90003e9#32), -- str x9, [sp]
  (436, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (440, 0xaa0803e9#32), -- mov x9, x8
  (444, 0xd280080a#32), -- mov x10, #0x40 // =64
  (448, 0xb4000089#32), -- cbz x9, 0x2468b0 <.Llower_arm_1280>
  (452, 0xd100054a#32), -- sub x10, x10, #0x1
  (456, 0xd341fd29#32), -- lsr x9, x9, #1
  (460, 0xb5ffffc9#32), -- cbnz x9, 0x2468a4 <.Llower_arm_1279>
  (464, 0xaa0a03e8#32), -- mov x8, x10
  (468, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (472, 0xf94003e9#32), -- ldr x9, [sp]
  (476, 0x910043ff#32), -- add sp, sp, #0x10
  (480, 0x4b0801a8#32), -- sub w8, w13, w8
  (484, 0xab080128#32), -- adds x8, x9, x8
  (488, 0x54000062#32), -- b.hs 0x2468d4 <.Llower_arm_1281>
  (492, 0xaa0a03e9#32), -- mov x9, x10
  (496, 0x14000002#32), -- b 0x2468d8 <.Llower_arm_1282>
  (500, 0x91000549#32), -- add x9, x10, #0x1
  (504, 0xf100050a#32), -- subs x10, x8, #0x1
  (508, 0x9a1c012b#32) -- adc x11, x9, x28
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xf100091f#32), -- cmp x8, #0x2
  (516, 0xfa1f013f#32), -- sbcs xzr, x9, xzr
  (520, 0x54fff9a3#32), -- b.lo 0x24681c <.LBB134_13>
  (524, 0xeb18015f#32), -- cmp x10, x24
  (528, 0xfa17017f#32), -- sbcs xzr, x11, x23
  (532, 0x54fff942#32), -- b.hs 0x24681c <.LBB134_13>
  (536, 0xeb0803a2#32), -- subs x2, x29, x8
  (540, 0x2a1f03e4#32), -- mov w4, wzr
  (544, 0xaa1503e0#32), -- mov x0, x21
  (548, 0xda090363#32), -- sbc x3, x27, x9
  (552, 0xaa1403e1#32), -- mov x1, x20
  (556, 0xd10043ff#32), -- sub sp, sp, #0x10
  (560, 0xf90003e9#32), -- str x9, [sp]
  (564, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (568, 0x910043e9#32), -- add x9, sp, #0x10
  (572, 0xd280000a#32), -- mov x10, #0x0 // =0
  (576, 0xf900012a#32), -- str x10, [x9]
  (580, 0xd280000a#32), -- mov x10, #0x0 // =0
  (584, 0xf900052a#32), -- str x10, [x9, #0x8]
  (588, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (592, 0xf94003e9#32), -- ldr x9, [sp]
  (596, 0x910043ff#32), -- add sp, sp, #0x10
  (600, 0x97fff28f#32), -- bl 0x243374 <_ZN13ssz_fv_native7indices12prefix_equal17h455af9025a76ffe0E>
  (604, 0x5280080d#32), -- mov w13, #0x40 // =64
  (608, 0x34fff6e0#32), -- cbz w0, 0x24681c <.LBB134_13>
  (612, 0x14000016#32), -- b 0x24699c <.LBB134_27>
  (616, 0xa94107ec#32), -- ldp x12, x1, [sp, #0x10]
  (620, 0x5280002e#32), -- mov w14, #0x1 // =1
  (624, 0xeb0c02df#32), -- cmp x22, x12
  (628, 0x54ffee21#32), -- b.ne 0x246718 <.LBB134_1>
  (632, 0xd10043ff#32), -- sub sp, sp, #0x10
  (636, 0xf90003e9#32), -- str x9, [sp]
  (640, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (644, 0x91000269#32), -- add x9, x19, #0x0
  (648, 0x91010129#32), -- add x9, x9, #0x40
  (652, 0x5280000a#32), -- mov w10, #0x0 // =0
  (656, 0xb900012a#32), -- str w10, [x9]
  (660, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (664, 0xf94003e9#32), -- ldr x9, [sp]
  (668, 0x910043ff#32), -- add sp, sp, #0x10
  (672, 0x1400003b#32), -- b 0x246a6c <.LBB134_31>
  (676, 0x6f00e400#32), -- movi v0.2d, #0000000000000000
  (680, 0xaa1f03f4#32), -- mov x20, xzr
  (684, 0xaa1f03e8#32), -- mov x8, xzr
  (688, 0xaa1f03f5#32), -- mov x21, xzr
  (692, 0x52800509#32), -- mov w9, #0x28 // =40
  (696, 0x1400002c#32), -- b 0x246a48 <.LBB134_30>
  (700, 0x52800028#32), -- mov w8, #0x1 // =1
  (704, 0xa9015275#32), -- stp x21, x20, [x19, #0x10]
  (708, 0xd10043ff#32), -- sub sp, sp, #0x10
  (712, 0xf90003e9#32), -- str x9, [sp]
  (716, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (720, 0x91000269#32), -- add x9, x19, #0x0
  (724, 0xf9000128#32), -- str x8, [x9]
  (728, 0xd280000a#32), -- mov x10, #0x0 // =0
  (732, 0xf900052a#32), -- str x10, [x9, #0x8]
  (736, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (740, 0xf94003e9#32), -- ldr x9, [sp]
  (744, 0x910043ff#32), -- add sp, sp, #0x10
  (748, 0x52800568#32), -- mov w8, #0x2b // =43
  (752, 0xd10043ff#32), -- sub sp, sp, #0x10
  (756, 0xf90003e9#32), -- str x9, [sp]
  (760, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (764, 0x91000269#32) -- add x9, x19, #0x0
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0x91008129#32), -- add x9, x9, #0x20
  (772, 0xd280000a#32), -- mov x10, #0x0 // =0
  (776, 0xf900012a#32), -- str x10, [x9]
  (780, 0xd280000a#32), -- mov x10, #0x0 // =0
  (784, 0xf900052a#32), -- str x10, [x9, #0x8]
  (788, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (792, 0xf94003e9#32), -- ldr x9, [sp]
  (796, 0x910043ff#32), -- add sp, sp, #0x10
  (800, 0xd10043ff#32), -- sub sp, sp, #0x10
  (804, 0xf90003e9#32), -- str x9, [sp]
  (808, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (812, 0x91000269#32), -- add x9, x19, #0x0
  (816, 0x9100c129#32), -- add x9, x9, #0x30
  (820, 0xd280000a#32), -- mov x10, #0x0 // =0
  (824, 0xf900012a#32), -- str x10, [x9]
  (828, 0xd280000a#32), -- mov x10, #0x0 // =0
  (832, 0xf900052a#32), -- str x10, [x9, #0x8]
  (836, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (840, 0xf94003e9#32), -- ldr x9, [sp]
  (844, 0x910043ff#32), -- add sp, sp, #0x10
  (848, 0xb9004268#32), -- str w8, [x19, #0x40]
  (852, 0x1400000e#32), -- b 0x246a6c <.LBB134_31>
  (856, 0xaa1f03f5#32), -- mov x21, xzr
  (860, 0x6f00e400#32), -- movi v0.2d, #0000000000000000
  (864, 0xaa1f03e8#32), -- mov x8, xzr
  (868, 0x528004e9#32), -- mov w9, #0x27 // =39
  (872, 0xad0103e0#32), -- stp q0, q0, [sp, #0x20]
  (876, 0x5280002a#32), -- mov w10, #0x1 // =1
  (880, 0xa9015275#32), -- stp x21, x20, [x19, #0x10]
  (884, 0xa900226a#32), -- stp x10, x8, [x19]
  (888, 0xa9422be8#32), -- ldp x8, x10, [sp, #0x20]
  (892, 0xb9004269#32), -- str w9, [x19, #0x40]
  (896, 0xa9022a68#32), -- stp x8, x10, [x19, #0x20]
  (900, 0xa94323eb#32), -- ldp x11, x8, [sp, #0x30]
  (904, 0xa903226b#32), -- stp x11, x8, [x19, #0x30]
  (908, 0xa9494ff4#32), -- ldp x20, x19, [sp, #0x90]
  (912, 0xa94857f6#32), -- ldp x22, x21, [sp, #0x80]
  (916, 0xa9475ff8#32), -- ldp x24, x23, [sp, #0x70]
  (920, 0xa94667fa#32), -- ldp x26, x25, [sp, #0x60]
  (924, 0xa9456ffc#32), -- ldp x28, x27, [sp, #0x50]
  (928, 0xa9447bfd#32), -- ldp x29, x30, [sp, #0x40]
  (932, 0x910283ff#32), -- add sp, sp, #0xa0
  (936, 0xd65f03c0#32) -- ret
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

end SszArm.Indices.Linked.RejectClaimPaths
