import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.ChunkCount

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN13ssz_fv_native7indices11chunk_count17hd16e3dc1986da804E. -/
def address : Nat := 2261268

def byteSize : Nat := 964

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10243ff#32), -- sub sp, sp, #0x90
  (4, 0xf9002bfe#32), -- str x30, [sp, #0x50]
  (8, 0xa9065ff8#32), -- stp x24, x23, [sp, #0x60]
  (12, 0xa90757f6#32), -- stp x22, x21, [sp, #0x70]
  (16, 0xa9084ff4#32), -- stp x20, x19, [sp, #0x80]
  (20, 0xf9400028#32), -- ldr x8, [x1]
  (24, 0xaa0203f3#32), -- mov x19, x2
  (28, 0xf100191f#32), -- cmp x8, #0x6
  (32, 0x5400016c#32), -- b.gt 0x228160 <.LBB59_5>
  (36, 0xf1000909#32), -- subs x9, x8, #0x2
  (40, 0x54000203#32), -- b.lo 0x22817c <.LBB59_8>
  (44, 0xf100093f#32), -- cmp x9, #0x2
  (48, 0x54000323#32), -- b.lo 0x2281a8 <.LBB59_12>
  (52, 0xd1001108#32), -- sub x8, x8, #0x4
  (56, 0xf100091f#32), -- cmp x8, #0x2
  (60, 0x54000342#32), -- b.hs 0x2281b8 <.LBB59_14>
  (64, 0xa9408828#32), -- ldp x8, x2, [x1, #0x8]
  (68, 0x52800103#32), -- mov w3, #0x8 // =8
  (72, 0x140000bc#32), -- b 0x22844c <.LBB59_30>
  (76, 0xd1001d09#32), -- sub x9, x8, #0x7
  (80, 0xf100093f#32), -- cmp x9, #0x2
  (84, 0x540000e3#32), -- b.lo 0x228184 <.LBB59_9>
  (88, 0xf100291f#32), -- cmp x8, #0xa
  (92, 0x54000920#32), -- b.eq 0x228294 <.LBB59_15>
  (96, 0xf100311f#32), -- cmp x8, #0xc
  (100, 0x54000201#32), -- b.ne 0x2281b8 <.LBB59_14>
  (104, 0x52800028#32), -- mov w8, #0x1 // =1
  (108, 0x14000046#32), -- b 0x228298 <.LBB59_16>
  (112, 0xf9400c28#32), -- ldr x8, [x1, #0x18]
  (116, 0xf9400109#32), -- ldr x9, [x8]
  (120, 0xf100053f#32), -- cmp x9, #0x1
  (124, 0x54000b80#32), -- b.eq 0x228300 <.LBB59_17>
  (128, 0xaa1f03e3#32), -- mov x3, xzr
  (132, 0xb5000dc9#32), -- cbnz x9, 0x228350 <.LBB59_22>
  (136, 0x52800024#32), -- mov w4, #0x1 // =1
  (140, 0x52800028#32), -- mov w8, #0x1 // =1
  (144, 0x14000074#32), -- b 0x228374 <.LBB59_27>
  (148, 0xa9408828#32), -- ldp x8, x2, [x1, #0x8]
  (152, 0xaa0803e1#32), -- mov x1, x8
  (156, 0x528000a3#32), -- mov w3, #0x5 // =5
  (160, 0x140000a7#32), -- b 0x228450 <.LBB59_31>
  (164, 0x52800028#32), -- mov w8, #0x1 // =1
  (168, 0xd10043ff#32), -- sub sp, sp, #0x10
  (172, 0xf90003e9#32), -- str x9, [sp]
  (176, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (180, 0x91000009#32), -- add x9, x0, #0x0
  (184, 0x91004129#32), -- add x9, x9, #0x10
  (188, 0xd280000a#32), -- mov x10, #0x0 // =0
  (192, 0xf900012a#32), -- str x10, [x9]
  (196, 0xd280000a#32), -- mov x10, #0x0 // =0
  (200, 0xf900052a#32), -- str x10, [x9, #0x8]
  (204, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (208, 0xf94003e9#32), -- ldr x9, [sp]
  (212, 0x910043ff#32), -- add sp, sp, #0x10
  (216, 0xd10043ff#32), -- sub sp, sp, #0x10
  (220, 0xf90003e9#32), -- str x9, [sp]
  (224, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (228, 0x91000009#32), -- add x9, x0, #0x0
  (232, 0xf9000128#32), -- str x8, [x9]
  (236, 0xd280000a#32), -- mov x10, #0x0 // =0
  (240, 0xf900052a#32), -- str x10, [x9, #0x8]
  (244, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (248, 0xf94003e9#32), -- ldr x9, [sp]
  (252, 0x910043ff#32) -- add sp, sp, #0x10
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0x528006e8#32), -- mov w8, #0x37 // =55
  (260, 0xd10043ff#32), -- sub sp, sp, #0x10
  (264, 0xf90003e9#32), -- str x9, [sp]
  (268, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (272, 0x91000009#32), -- add x9, x0, #0x0
  (276, 0x91008129#32), -- add x9, x9, #0x20
  (280, 0xd280000a#32), -- mov x10, #0x0 // =0
  (284, 0xf900012a#32), -- str x10, [x9]
  (288, 0xd280000a#32), -- mov x10, #0x0 // =0
  (292, 0xf900052a#32), -- str x10, [x9, #0x8]
  (296, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (300, 0xf94003e9#32), -- ldr x9, [sp]
  (304, 0x910043ff#32), -- add sp, sp, #0x10
  (308, 0xd10043ff#32), -- sub sp, sp, #0x10
  (312, 0xf90003e9#32), -- str x9, [sp]
  (316, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (320, 0x91000009#32), -- add x9, x0, #0x0
  (324, 0x9100c129#32), -- add x9, x9, #0x30
  (328, 0xd280000a#32), -- mov x10, #0x0 // =0
  (332, 0xf900012a#32), -- str x10, [x9]
  (336, 0xd280000a#32), -- mov x10, #0x0 // =0
  (340, 0xf900052a#32), -- str x10, [x9, #0x8]
  (344, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (348, 0xf94003e9#32), -- ldr x9, [sp]
  (352, 0x910043ff#32), -- add sp, sp, #0x10
  (356, 0xb9004008#32), -- str w8, [x0, #0x40]
  (360, 0xa9484ff4#32), -- ldp x20, x19, [sp, #0x80]
  (364, 0xf9402bfe#32), -- ldr x30, [sp, #0x50]
  (368, 0xa94757f6#32), -- ldp x22, x21, [sp, #0x70]
  (372, 0xa9465ff8#32), -- ldp x24, x23, [sp, #0x60]
  (376, 0x910243ff#32), -- add sp, sp, #0x90
  (380, 0xd65f03c0#32), -- ret
  (384, 0xf9400828#32), -- ldr x8, [x1, #0x10]
  (388, 0xd10043ff#32), -- sub sp, sp, #0x10
  (392, 0xf90003e9#32), -- str x9, [sp]
  (396, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (400, 0x91000009#32), -- add x9, x0, #0x0
  (404, 0xd280000a#32), -- mov x10, #0x0 // =0
  (408, 0xf900012a#32), -- str x10, [x9]
  (412, 0xf9000528#32), -- str x8, [x9, #0x8]
  (416, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (420, 0xf94003e9#32), -- ldr x9, [sp]
  (424, 0x910043ff#32), -- add sp, sp, #0x10
  (428, 0xd10043ff#32), -- sub sp, sp, #0x10
  (432, 0xf90003e9#32), -- str x9, [sp]
  (436, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (440, 0x91000009#32), -- add x9, x0, #0x0
  (444, 0x91010129#32), -- add x9, x9, #0x40
  (448, 0x5280000a#32), -- mov w10, #0x0 // =0
  (452, 0xb900012a#32), -- str w10, [x9]
  (456, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (460, 0xf94003e9#32), -- ldr x9, [sp]
  (464, 0x910043ff#32), -- add sp, sp, #0x10
  (468, 0xa9484ff4#32), -- ldp x20, x19, [sp, #0x80]
  (472, 0xf9402bfe#32), -- ldr x30, [sp, #0x50]
  (476, 0xa94757f6#32), -- ldp x22, x21, [sp, #0x70]
  (480, 0xa9465ff8#32), -- ldp x24, x23, [sp, #0x60]
  (484, 0x910243ff#32), -- add sp, sp, #0x90
  (488, 0xd65f03c0#32), -- ret
  (492, 0xa9409103#32), -- ldp x3, x4, [x8, #0x8]
  (496, 0xb40002c3#32), -- cbz x3, 0x22835c <.LBB59_23>
  (500, 0xd1000489#32), -- sub x9, x4, #0x1
  (504, 0xb100053f#32), -- cmn x9, #0x1
  (508, 0x540002a0#32) -- b.eq 0x228364 <.LBB59_24>
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xd10043ff#32), -- sub sp, sp, #0x10
  (516, 0xf90003eb#32), -- str x11, [sp]
  (520, 0xaa0903eb#32), -- mov x11, x9
  (524, 0xd37df16b#32), -- lsl x11, x11, #3
  (528, 0x8b0b006b#32), -- add x11, x3, x11
  (532, 0xf940016a#32), -- ldr x10, [x11]
  (536, 0xf94003eb#32), -- ldr x11, [sp]
  (540, 0x910043ff#32), -- add sp, sp, #0x10
  (544, 0xaa0903e8#32), -- mov x8, x9
  (548, 0xd1000529#32), -- sub x9, x9, #0x1
  (552, 0xb4fffe8a#32), -- cbz x10, 0x22830c <.LBB59_19>
  (556, 0x91000508#32), -- add x8, x8, #0x1
  (560, 0xf100051f#32), -- cmp x8, #0x1
  (564, 0x54000100#32), -- b.eq 0x228368 <.LBB59_25>
  (568, 0x14000048#32), -- b 0x22846c <.LBB59_32>
  (572, 0x52800404#32), -- mov w4, #0x20 // =32
  (576, 0x52800408#32), -- mov w8, #0x20 // =32
  (580, 0x14000007#32), -- b 0x228374 <.LBB59_27>
  (584, 0xaa0403e8#32), -- mov x8, x4
  (588, 0x14000005#32), -- b 0x228374 <.LBB59_27>
  (592, 0xb4000064#32), -- cbz x4, 0x228370 <.LBB59_26>
  (596, 0xf9400068#32), -- ldr x8, [x3]
  (600, 0x14000002#32), -- b 0x228374 <.LBB59_27>
  (604, 0xaa1f03e8#32), -- mov x8, xzr
  (608, 0xf100811f#32), -- cmp x8, #0x20
  (612, 0x540007a8#32), -- b.hi 0x22846c <.LBB59_32>
  (616, 0xd1000509#32), -- sub x9, x8, #0x1
  (620, 0xca09010a#32), -- eor x10, x8, x9
  (624, 0xeb09015f#32), -- cmp x10, x9
  (628, 0x54000729#32), -- b.ls 0x22846c <.LBB59_32>
  (632, 0xd10043ff#32), -- sub sp, sp, #0x10
  (636, 0xf90003ea#32), -- str x10, [sp]
  (640, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (644, 0xaa0803ea#32), -- mov x10, x8
  (648, 0x9200f14b#32), -- and x11, x10, #0x5555555555555555
  (652, 0xd341fd4a#32), -- lsr x10, x10, #1
  (656, 0x9200f14a#32), -- and x10, x10, #0x5555555555555555
  (660, 0xaa0b054a#32), -- orr x10, x10, x11, lsl #1
  (664, 0x9200e54b#32), -- and x11, x10, #0x3333333333333333
  (668, 0xd342fd4a#32), -- lsr x10, x10, #2
  (672, 0x9200e54a#32), -- and x10, x10, #0x3333333333333333
  (676, 0xaa0b094a#32), -- orr x10, x10, x11, lsl #2
  (680, 0x9200cd4b#32), -- and x11, x10, #0xf0f0f0f0f0f0f0f
  (684, 0xd344fd4a#32), -- lsr x10, x10, #4
  (688, 0x9200cd4a#32), -- and x10, x10, #0xf0f0f0f0f0f0f0f
  (692, 0xaa0b114a#32), -- orr x10, x10, x11, lsl #4
  (696, 0x92009d4b#32), -- and x11, x10, #0xff00ff00ff00ff
  (700, 0xd348fd4a#32), -- lsr x10, x10, #8
  (704, 0x92009d4a#32), -- and x10, x10, #0xff00ff00ff00ff
  (708, 0xaa0b214a#32), -- orr x10, x10, x11, lsl #8
  (712, 0x92003d4b#32), -- and x11, x10, #0xffff0000ffff
  (716, 0xd350fd4a#32), -- lsr x10, x10, #16
  (720, 0x92003d4a#32), -- and x10, x10, #0xffff0000ffff
  (724, 0xaa0b414a#32), -- orr x10, x10, x11, lsl #16
  (728, 0x92407d4b#32), -- and x11, x10, #0xffffffff
  (732, 0xd360fd4a#32), -- lsr x10, x10, #32
  (736, 0x92407d4a#32), -- and x10, x10, #0xffffffff
  (740, 0xaa0b814a#32), -- orr x10, x10, x11, lsl #32
  (744, 0xaa0a03e9#32), -- mov x9, x10
  (748, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (752, 0xf94003ea#32), -- ldr x10, [sp]
  (756, 0x910043ff#32), -- add sp, sp, #0x10
  (760, 0xa9408828#32), -- ldp x8, x2, [x1, #0x8]
  (764, 0x528000aa#32) -- mov w10, #0x5 // =5
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk3 : List (Nat × BitVec 32) := [
  (768, 0xd10043ff#32), -- sub sp, sp, #0x10
  (772, 0xf90003ea#32), -- str x10, [sp]
  (776, 0xf90007eb#32), -- str x11, [sp, #0x8]
  (780, 0xaa0903ea#32), -- mov x10, x9
  (784, 0xd280080b#32), -- mov x11, #0x40 // =64
  (788, 0xb400008a#32), -- cbz x10, 0x228438 <.Llower_arm_490>
  (792, 0xd100056b#32), -- sub x11, x11, #0x1
  (796, 0xd341fd4a#32), -- lsr x10, x10, #1
  (800, 0xb5ffffca#32), -- cbnz x10, 0x22842c <.Llower_arm_489>
  (804, 0xaa0b03e9#32), -- mov x9, x11
  (808, 0xf94007eb#32), -- ldr x11, [sp, #0x8]
  (812, 0xf94003ea#32), -- ldr x10, [sp]
  (816, 0x910043ff#32), -- add sp, sp, #0x10
  (820, 0x4b090143#32), -- sub w3, w10, w9
  (824, 0xaa0803e1#32), -- mov x1, x8
  (828, 0xaa1303e4#32), -- mov x4, x19
  (832, 0xa9484ff4#32), -- ldp x20, x19, [sp, #0x80]
  (836, 0xa94757f6#32), -- ldp x22, x21, [sp, #0x70]
  (840, 0xf9402bfe#32), -- ldr x30, [sp, #0x50]
  (844, 0xa9465ff8#32), -- ldp x24, x23, [sp, #0x60]
  (848, 0x910243ff#32), -- add sp, sp, #0x90
  (852, 0x140001d3#32), -- b 0x228bb4 <_ZN13ssz_fv_native7indices10ceil_shift17hfe7605b69b9bc83bE>
  (856, 0xa9408828#32), -- ldp x8, x2, [x1, #0x8]
  (860, 0xaa0003f4#32), -- mov x20, x0
  (864, 0x910023e0#32), -- add x0, sp, #0x8
  (868, 0xaa1303e5#32), -- mov x5, x19
  (872, 0x910023f8#32), -- add x24, sp, #0x8
  (876, 0xaa0803e1#32), -- mov x1, x8
  (880, 0x97fff0fe#32), -- bl 0x22487c <_ZN13ssz_fv_native3nat3Nat3mul17h5dc2c96f405496c8E>
  (884, 0xa940d7f6#32), -- ldp x22, x21, [sp, #0x8]
  (888, 0xb9404bf7#32), -- ldr w23, [sp, #0x48]
  (892, 0x340001d7#32), -- cbz w23, 0x2284c8 <.LBB59_34>
  (896, 0x91004280#32), -- add x0, x20, #0x10
  (900, 0x91004301#32), -- add x1, x24, #0x10
  (904, 0x52800602#32), -- mov w2, #0x30 // =48
  (908, 0x9400940c#32), -- bl 0x24d4d0 <memcpy>
  (912, 0xb9404fe8#32), -- ldr w8, [sp, #0x4c]
  (916, 0xa9005696#32), -- stp x22, x21, [x20]
  (920, 0x29082297#32), -- stp w23, w8, [x20, #0x40]
  (924, 0xa9484ff4#32), -- ldp x20, x19, [sp, #0x80]
  (928, 0xf9402bfe#32), -- ldr x30, [sp, #0x50]
  (932, 0xa94757f6#32), -- ldp x22, x21, [sp, #0x70]
  (936, 0xa9465ff8#32), -- ldp x24, x23, [sp, #0x60]
  (940, 0x910243ff#32), -- add sp, sp, #0x90
  (944, 0xd65f03c0#32), -- ret
  (948, 0xaa1403e0#32), -- mov x0, x20
  (952, 0xaa1603e1#32), -- mov x1, x22
  (956, 0xaa1503e2#32), -- mov x2, x21
  (960, 0x17ffff37#32) -- b 0x2281b0 <.LBB59_13>
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

end SszArm.Indices.Linked.ChunkCount
