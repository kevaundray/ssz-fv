import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.SortInsertion

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN4core5slice4sort6shared9smallsort25insertion_sort_shift_left17hedcf71437a340f54E. -/
def address : Nat := 2374472

def byteSize : Nat := 732

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xa9bc67fe#32), -- stp x30, x25, [sp, #-0x40]!
  (4, 0xa9015ff8#32), -- stp x24, x23, [sp, #0x10]
  (8, 0xa90257f6#32), -- stp x22, x21, [sp, #0x20]
  (12, 0xa9034ff4#32), -- stp x20, x19, [sp, #0x30]
  (16, 0x8b011017#32), -- add x23, x0, x1, lsl #4
  (20, 0xaa0003f3#32), -- mov x19, x0
  (24, 0x52801ff6#32), -- mov w22, #0xff // =255
  (28, 0x91004008#32), -- add x8, x0, #0x10
  (32, 0xaa0003f9#32), -- mov x25, x0
  (36, 0x14000007#32), -- b 0x243b88 <.LBB128_4>
  (40, 0xaa1303e8#32), -- mov x8, x19
  (44, 0xa9005514#32), -- stp x20, x21, [x8]
  (48, 0x91004308#32), -- add x8, x24, #0x10
  (52, 0xaa1803f9#32), -- mov x25, x24
  (56, 0xeb17011f#32), -- cmp x8, x23
  (60, 0x54001460#32), -- b.eq 0x243e10 <.LBB128_41>
  (64, 0xa9415734#32), -- ldp x20, x21, [x25, #0x10]
  (68, 0xaa0803f8#32), -- mov x24, x8
  (72, 0xa9400720#32), -- ldp x0, x1, [x25]
  (76, 0xaa1403e2#32), -- mov x2, x20
  (80, 0xaa1503e3#32), -- mov x3, x21
  (84, 0x97ff8684#32), -- bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>
  (88, 0x6a2002df#32), -- bics wzr, w22, w0
  (92, 0x54fffea1#32), -- b.ne 0x243b78 <.LBB128_3>
  (96, 0xf10002bf#32), -- cmp x21, #0x0
  (100, 0xd100228a#32), -- sub x10, x20, #0x8
  (104, 0xaa1803eb#32), -- mov x11, x24
  (108, 0x54000061#32), -- b.ne 0x243bc0 <.Llower_arm_1111>
  (112, 0x52800009#32), -- mov w9, #0x0 // =0
  (116, 0x14000002#32), -- b 0x243bc4 <.Llower_arm_1112>
  (120, 0x52800029#32), -- mov w9, #0x1 // =1
  (124, 0x14000004#32), -- b 0x243bd4 <.LBB128_8>
  (128, 0xeb0f01bf#32), -- cmp x13, x15
  (132, 0xaa0803eb#32), -- mov x11, x8
  (136, 0x54fffd22#32), -- b.hs 0x243b74 <.LBB128_2>
  (140, 0xa940372c#32), -- ldp x12, x13, [x25]
  (144, 0xeb13033f#32), -- cmp x25, x19
  (148, 0xa900356c#32), -- stp x12, x13, [x11]
  (152, 0x54fffc80#32), -- b.eq 0x243b70 <.LBB128_1>
  (156, 0xaa1903e8#32), -- mov x8, x25
  (160, 0xa9ff2f2c#32), -- ldp x12, x11, [x25, #-0x10]!
  (164, 0xb400028c#32), -- cbz x12, 0x243c3c <.LBB128_15>
  (168, 0xd100218d#32), -- sub x13, x12, #0x8
  (172, 0xaa0b03ee#32), -- mov x14, x11
  (176, 0xb40001ae#32), -- cbz x14, 0x243c2c <.LBB128_14>
  (180, 0xd10043ff#32), -- sub sp, sp, #0x10
  (184, 0xf90003e9#32), -- str x9, [sp]
  (188, 0xaa0e03e9#32), -- mov x9, x14
  (192, 0xd37df129#32), -- lsl x9, x9, #3
  (196, 0x8b0901a9#32), -- add x9, x13, x9
  (200, 0xf9400130#32), -- ldr x16, [x9]
  (204, 0xf94003e9#32), -- ldr x9, [sp]
  (208, 0x910043ff#32), -- add sp, sp, #0x10
  (212, 0xd10005cf#32), -- sub x15, x14, #0x1
  (216, 0xaa0f03ee#32), -- mov x14, x15
  (220, 0xb4fffeb0#32), -- cbz x16, 0x243bf8 <.LBB128_11>
  (224, 0x910005ee#32), -- add x14, x15, #0x1
  (228, 0xaa0903ef#32), -- mov x15, x9
  (232, 0xaa1503ed#32), -- mov x13, x21
  (236, 0xb5000154#32), -- cbnz x20, 0x243c5c <.LBB128_16>
  (240, 0x14000016#32), -- b 0x243c90 <.LBB128_19>
  (244, 0xf100017f#32), -- cmp x11, #0x0
  (248, 0x54000061#32), -- b.ne 0x243c4c <.Llower_arm_1113>
  (252, 0x5280000e#32) -- mov w14, #0x0 // =0
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0x14000002#32), -- b 0x243c50 <.Llower_arm_1114>
  (260, 0x5280002e#32), -- mov w14, #0x1 // =1
  (264, 0xaa0903ef#32), -- mov x15, x9
  (268, 0xaa1503ed#32), -- mov x13, x21
  (272, 0xb40001d4#32), -- cbz x20, 0x243c90 <.LBB128_19>
  (276, 0xb400020d#32), -- cbz x13, 0x243c9c <.LBB128_20>
  (280, 0xd10043ff#32), -- sub sp, sp, #0x10
  (284, 0xf90003e9#32), -- str x9, [sp]
  (288, 0xaa0d03e9#32), -- mov x9, x13
  (292, 0xd37df129#32), -- lsl x9, x9, #3
  (296, 0x8b090149#32), -- add x9, x10, x9
  (300, 0xf9400130#32), -- ldr x16, [x9]
  (304, 0xf94003e9#32), -- ldr x9, [sp]
  (308, 0x910043ff#32), -- add sp, sp, #0x10
  (312, 0xd10005af#32), -- sub x15, x13, #0x1
  (316, 0xaa0f03ed#32), -- mov x13, x15
  (320, 0xb4fffeb0#32), -- cbz x16, 0x243c5c <.LBB128_16>
  (324, 0x910005ef#32), -- add x15, x15, #0x1
  (328, 0xeb0f01df#32), -- cmp x14, x15
  (332, 0x54fff9c1#32), -- b.ne 0x243bcc <.LBB128_7>
  (336, 0x14000003#32), -- b 0x243ca4 <.LBB128_21>
  (340, 0xeb1f01df#32), -- cmp x14, xzr
  (344, 0x54fff961#32), -- b.ne 0x243bcc <.LBB128_7>
  (348, 0xb40007cc#32), -- cbz x12, 0x243d9c <.LBB128_33>
  (352, 0xd10005ce#32), -- sub x14, x14, #0x1
  (356, 0xb50001b4#32), -- cbnz x20, 0x243ce0 <.LBB128_24>
  (360, 0x14000030#32), -- b 0x243d70 <.LBB128_30>
  (364, 0xd10043ff#32), -- sub sp, sp, #0x10
  (368, 0xf90003e9#32), -- str x9, [sp]
  (372, 0xaa0e03e9#32), -- mov x9, x14
  (376, 0xd37df129#32), -- lsl x9, x9, #3
  (380, 0x8b090289#32), -- add x9, x20, x9
  (384, 0xf940012f#32), -- ldr x15, [x9]
  (388, 0xf94003e9#32), -- ldr x9, [sp]
  (392, 0x910043ff#32), -- add sp, sp, #0x10
  (396, 0xeb0f01bf#32), -- cmp x13, x15
  (400, 0xd10005ce#32), -- sub x14, x14, #0x1
  (404, 0x54fff761#32), -- b.ne 0x243bc8 <.LBB128_6>
  (408, 0xb10005df#32), -- cmn x14, #0x1
  (412, 0x54fff480#32), -- b.eq 0x243b74 <.LBB128_2>
  (416, 0xeb0b01df#32), -- cmp x14, x11
  (420, 0x54000182#32), -- b.hs 0x243d1c <.LBB128_27>
  (424, 0xd10043ff#32), -- sub sp, sp, #0x10
  (428, 0xf90003e9#32), -- str x9, [sp]
  (432, 0xaa0e03e9#32), -- mov x9, x14
  (436, 0xd37df129#32), -- lsl x9, x9, #3
  (440, 0x8b090189#32), -- add x9, x12, x9
  (444, 0xf940012d#32), -- ldr x13, [x9]
  (448, 0xf94003e9#32), -- ldr x9, [sp]
  (452, 0x910043ff#32), -- add sp, sp, #0x10
  (456, 0xeb1501df#32), -- cmp x14, x21
  (460, 0x54fffd03#32), -- b.lo 0x243cb4 <.LBB128_23>
  (464, 0x14000004#32), -- b 0x243d28 <.LBB128_28>
  (468, 0xaa1f03ed#32), -- mov x13, xzr
  (472, 0xeb1501df#32), -- cmp x14, x21
  (476, 0x54fffc83#32), -- b.lo 0x243cb4 <.LBB128_23>
  (480, 0xaa1f03ef#32), -- mov x15, xzr
  (484, 0xeb1f01bf#32), -- cmp x13, xzr
  (488, 0xd10005ce#32), -- sub x14, x14, #0x1
  (492, 0x54fffd60#32), -- b.eq 0x243ce0 <.LBB128_24>
  (496, 0x17ffffa4#32), -- b 0x243bc8 <.LBB128_6>
  (500, 0xd10043ff#32), -- sub sp, sp, #0x10
  (504, 0xf90003e9#32), -- str x9, [sp]
  (508, 0xaa0e03e9#32) -- mov x9, x14
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xd37df129#32), -- lsl x9, x9, #3
  (516, 0x8b090189#32), -- add x9, x12, x9
  (520, 0xf940012d#32), -- ldr x13, [x9]
  (524, 0xf94003e9#32), -- ldr x9, [sp]
  (528, 0x910043ff#32), -- add sp, sp, #0x10
  (532, 0xf10001df#32), -- cmp x14, #0x0
  (536, 0xd10005ce#32), -- sub x14, x14, #0x1
  (540, 0x9a9f02af#32), -- csel x15, x21, xzr, eq
  (544, 0xeb0f01bf#32), -- cmp x13, x15
  (548, 0x54fff2e1#32), -- b.ne 0x243bc8 <.LBB128_6>
  (552, 0xb10005df#32), -- cmn x14, #0x1
  (556, 0x54fff000#32), -- b.eq 0x243b74 <.LBB128_2>
  (560, 0xeb0b01df#32), -- cmp x14, x11
  (564, 0x54fffe03#32), -- b.lo 0x243d3c <.LBB128_29>
  (568, 0xaa1f03ed#32), -- mov x13, xzr
  (572, 0xf10001df#32), -- cmp x14, #0x0
  (576, 0xd10005ce#32), -- sub x14, x14, #0x1
  (580, 0x9a9f02af#32), -- csel x15, x21, xzr, eq
  (584, 0xeb0f03ff#32), -- cmp xzr, x15
  (588, 0x54fffee0#32), -- b.eq 0x243d70 <.LBB128_30>
  (592, 0x17ffff8c#32), -- b 0x243bc8 <.LBB128_6>
  (596, 0xb40002d4#32), -- cbz x20, 0x243df4 <.LBB128_39>
  (600, 0xd10005cc#32), -- sub x12, x14, #0x1
  (604, 0x14000004#32), -- b 0x243db4 <.LBB128_36>
  (608, 0xeb0f01bf#32), -- cmp x13, x15
  (612, 0xd100058c#32), -- sub x12, x12, #0x1
  (616, 0x54fff0c1#32), -- b.ne 0x243bc8 <.LBB128_6>
  (620, 0xb100059f#32), -- cmn x12, #0x1
  (624, 0x54ffede0#32), -- b.eq 0x243b74 <.LBB128_2>
  (628, 0xf100019f#32), -- cmp x12, #0x0
  (632, 0xaa1f03ef#32), -- mov x15, xzr
  (636, 0x9a9f016d#32), -- csel x13, x11, xzr, eq
  (640, 0xeb15019f#32), -- cmp x12, x21
  (644, 0x54fffee2#32), -- b.hs 0x243da8 <.LBB128_35>
  (648, 0xd10043ff#32), -- sub sp, sp, #0x10
  (652, 0xf90003e9#32), -- str x9, [sp]
  (656, 0xaa0c03e9#32), -- mov x9, x12
  (660, 0xd37df129#32), -- lsl x9, x9, #3
  (664, 0x8b090289#32), -- add x9, x20, x9
  (668, 0xf940012f#32), -- ldr x15, [x9]
  (672, 0xf94003e9#32), -- ldr x9, [sp]
  (676, 0x910043ff#32), -- add sp, sp, #0x10
  (680, 0x17ffffee#32), -- b 0x243da8 <.LBB128_35>
  (684, 0xb4ffec0e#32), -- cbz x14, 0x243b74 <.LBB128_2>
  (688, 0xf10005ce#32), -- subs x14, x14, #0x1
  (692, 0x9a9f016d#32), -- csel x13, x11, xzr, eq
  (696, 0x9a9f02af#32), -- csel x15, x21, xzr, eq
  (700, 0xeb0f01bf#32), -- cmp x13, x15
  (704, 0x54ffff60#32), -- b.eq 0x243df4 <.LBB128_39>
  (708, 0x17ffff6f#32), -- b 0x243bc8 <.LBB128_6>
  (712, 0xa9434ff4#32), -- ldp x20, x19, [sp, #0x30]
  (716, 0xa94257f6#32), -- ldp x22, x21, [sp, #0x20]
  (720, 0xa9415ff8#32), -- ldp x24, x23, [sp, #0x10]
  (724, 0xa8c467fe#32), -- ldp x30, x25, [sp], #0x40
  (728, 0xd65f03c0#32) -- ret
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete linked function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2

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

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, Bool.and_self]

theorem step_at (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (row : Nat × BitVec 32) (member : row ∈ program)
    (entry : read_pc s = base + BitVec.ofNat 64 row.1)
    (error : read_err s = .None) :
    stepi s = exec_inst (SszArm.Codec.Linked.decoded program all_decode row member) s :=
  SszArm.Codec.Linked.step_at program all_decode s base code row member entry error

end SszArm.Indices.Linked.SortInsertion
