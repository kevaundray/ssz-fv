import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.DecodeStructValues

/-- Actual ELF entry address of _ZN13ssz_fv_native5arena5Arena10slice_with17h0ed27805c5c943ffE. -/
def address : Nat := 2327644

def byteSize : Nat := 640

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10583ff#32), -- sub sp, sp, #0x160
  (4, 0xa9107bfd#32), -- stp x29, x30, [sp, #0x100]
  (8, 0xa9116ffc#32), -- stp x28, x27, [sp, #0x110]
  (12, 0xa91267fa#32), -- stp x26, x25, [sp, #0x120]
  (16, 0xa9135ff8#32), -- stp x24, x23, [sp, #0x130]
  (20, 0xa91457f6#32), -- stp x22, x21, [sp, #0x140]
  (24, 0xa9154ff4#32), -- stp x20, x19, [sp, #0x150]
  (28, 0xaa0203f4#32), -- mov x20, x2
  (32, 0xb4000d62#32), -- cbz x2, 0x238628 <.LBB105_17>
  (36, 0x8b140688#32), -- add x8, x20, x20, lsl #1
  (40, 0xd37ced0a#32), -- lsl x10, x8, #4
  (44, 0xd10043ff#32), -- sub sp, sp, #0x10
  (48, 0xf90003e9#32), -- str x9, [sp]
  (52, 0x92410149#32), -- and x9, x10, #0x8000000000000000
  (56, 0xb5000089#32), -- cbnz x9, 0x2384a4 <.Llower_arm_737>
  (60, 0xf94003e9#32), -- ldr x9, [sp]
  (64, 0x910043ff#32), -- add sp, sp, #0x10
  (68, 0x14000004#32), -- b 0x2384b0 <.Llower_arm_738>
  (72, 0xf94003e9#32), -- ldr x9, [sp]
  (76, 0x910043ff#32), -- add sp, sp, #0x10
  (80, 0x14000051#32), -- b 0x2385f0 <.LBB105_15>
  (84, 0xf9400029#32), -- ldr x9, [x1]
  (88, 0xf940082b#32), -- ldr x11, [x1, #0x10]
  (92, 0xaa0103f5#32), -- mov x21, x1
  (96, 0xab09016c#32), -- adds x12, x11, x9
  (100, 0x54000982#32), -- b.hs 0x2385f0 <.LBB105_15>
  (104, 0xb100419f#32), -- cmn x12, #0x10
  (108, 0x54000948#32), -- b.hi 0x2385f0 <.LBB105_15>
  (112, 0x91003d88#32), -- add x8, x12, #0xf
  (116, 0x927ced08#32), -- and x8, x8, #0xfffffffffffffff0
  (120, 0xcb0c010c#32), -- sub x12, x8, x12
  (124, 0xab0b018b#32), -- adds x11, x12, x11
  (128, 0x540008a2#32), -- b.hs 0x2385f0 <.LBB105_15>
  (132, 0xab0a016a#32), -- adds x10, x11, x10
  (136, 0x54000862#32), -- b.hs 0x2385f0 <.LBB105_15>
  (140, 0xf94006ac#32), -- ldr x12, [x21, #0x8]
  (144, 0xeb0c015f#32), -- cmp x10, x12
  (148, 0x54000808#32), -- b.hi 0x2385f0 <.LBB105_15>
  (152, 0x8b0b0129#32), -- add x9, x9, x11
  (156, 0xf9000aaa#32), -- str x10, [x21, #0x10]
  (160, 0xaa1f03fb#32), -- mov x27, xzr
  (164, 0xa90103e9#32), -- stp x9, x0, [sp, #0x10]
  (168, 0xa9405869#32), -- ldp x9, x22, [x3]
  (172, 0xa9415c6a#32), -- ldp x10, x23, [x3, #0x10]
  (176, 0x91002119#32), -- add x25, x8, #0x8
  (180, 0xa942607d#32), -- ldp x29, x24, [x3, #0x20]
  (184, 0x9100813c#32), -- add x28, x9, #0x20
  (188, 0x9100415a#32), -- add x26, x10, #0x10
  (192, 0xeb1b02df#32), -- cmp x22, x27
  (196, 0x54000d20#32), -- b.eq 0x2386c4 <.LBB105_24>
  (200, 0xeb1b02ff#32), -- cmp x23, x27
  (204, 0x54000d40#32), -- b.eq 0x2386d0 <.LBB105_25>
  (208, 0xa97f8788#32), -- ldp x8, x1, [x28, #-0x8]
  (212, 0xeb080023#32), -- subs x3, x1, x8
  (216, 0x54000c23#32), -- b.lo 0x2386b8 <.LBB105_23>
  (220, 0xeb18003f#32), -- cmp x1, x24
  (224, 0x54000be8#32), -- b.hi 0x2386b8 <.LBB105_23>
  (228, 0xf8418741#32), -- ldr x1, [x26], #0x18
  (232, 0x910203e0#32), -- add x0, sp, #0x80
  (236, 0x8b0803a2#32), -- add x2, x29, x8
  (240, 0xaa1503e4#32), -- mov x4, x21
  (244, 0x97ffee14#32), -- bl 0x233da0 <_ZN13ssz_fv_native5codec11deserialize17h539c5ca52740cbedE>
  (248, 0xb94083e8#32), -- ldr w8, [sp, #0x80]
  (252, 0xd10043ff#32) -- sub sp, sp, #0x10
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0xf90003e9#32), -- str x9, [sp]
  (260, 0x12000109#32), -- and w9, w8, #0x1
  (264, 0x35000089#32), -- cbnz w9, 0x238574 <.Llower_arm_739>
  (268, 0xf94003e9#32), -- ldr x9, [sp]
  (272, 0x910043ff#32), -- add sp, sp, #0x10
  (276, 0x14000004#32), -- b 0x238580 <.Llower_arm_740>
  (280, 0xf94003e9#32), -- ldr x9, [sp]
  (284, 0x910043ff#32), -- add sp, sp, #0x10
  (288, 0x1400003f#32), -- b 0x238678 <.LBB105_20>
  (292, 0x910203e8#32), -- add x8, sp, #0x80
  (296, 0xf9404bf3#32), -- ldr x19, [sp, #0x90]
  (300, 0x910143e0#32), -- add x0, sp, #0x50
  (304, 0x91006101#32), -- add x1, x8, #0x18
  (308, 0x52800502#32), -- mov w2, #0x28               // =40
  (312, 0x9100077b#32), -- add x27, x27, #0x1
  (316, 0x940053ce#32), -- bl 0x24d4d0 <memcpy>
  (320, 0x910363e0#32), -- add x0, sp, #0xd8
  (324, 0x910143e1#32), -- add x1, sp, #0x50
  (328, 0x52800502#32), -- mov w2, #0x28               // =40
  (332, 0x940053ca#32), -- bl 0x24d4d0 <memcpy>
  (336, 0x910363e1#32), -- add x1, sp, #0xd8
  (340, 0xaa1903e0#32), -- mov x0, x25
  (344, 0x52800502#32), -- mov w2, #0x28               // =40
  (348, 0xd10043ff#32), -- sub sp, sp, #0x10
  (352, 0xf90003e9#32), -- str x9, [sp]
  (356, 0x91000329#32), -- add x9, x25, #0x0
  (360, 0xd1002129#32), -- sub x9, x9, #0x8
  (364, 0xf9000133#32), -- str x19, [x9]
  (368, 0xf94003e9#32), -- ldr x9, [sp]
  (372, 0x910043ff#32), -- add sp, sp, #0x10
  (376, 0x940053bf#32), -- bl 0x24d4d0 <memcpy>
  (380, 0xeb1b029f#32), -- cmp x20, x27
  (384, 0x9100c339#32), -- add x25, x25, #0x30
  (388, 0x9100a39c#32), -- add x28, x28, #0x28
  (392, 0x54fff9c1#32), -- b.ne 0x23851c <.LBB105_8>
  (396, 0xa94103f7#32), -- ldp x23, x0, [sp, #0x10]
  (400, 0x14000010#32), -- b 0x23862c <.LBB105_18>
  (404, 0x6f00e400#32), -- movi v0.2d, #0000000000000000
  (408, 0xaa1f03f4#32), -- mov x20, xzr
  (412, 0x52900015#32), -- mov w21, #0x8000            // =32768
  (416, 0x52800037#32), -- mov w23, #0x1               // =1
  (420, 0xad0183e0#32), -- stp q0, q0, [sp, #0x30]
  (424, 0x3d800be0#32), -- str q0, [sp, #0x20]
  (428, 0xaa0003f3#32), -- mov x19, x0
  (432, 0x91004000#32), -- add x0, x0, #0x10
  (436, 0x910083e1#32), -- add x1, sp, #0x20
  (440, 0x52800602#32), -- mov w2, #0x30               // =48
  (444, 0x940053ae#32), -- bl 0x24d4d0 <memcpy>
  (448, 0xa9005277#32), -- stp x23, x20, [x19]
  (452, 0x29085a75#32), -- stp w21, w22, [x19, #0x40]
  (456, 0x1400000d#32), -- b 0x238658 <.LBB105_19>
  (460, 0x52800217#32), -- mov w23, #0x10              // =16
  (464, 0xa9005017#32), -- stp x23, x20, [x0]
  (468, 0xd10043ff#32), -- sub sp, sp, #0x10
  (472, 0xf90003e9#32), -- str x9, [sp]
  (476, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (480, 0x91000009#32), -- add x9, x0, #0x0
  (484, 0x91010129#32), -- add x9, x9, #0x40
  (488, 0x5280000a#32), -- mov w10, #0x0               // =0
  (492, 0xb900012a#32), -- str w10, [x9]
  (496, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (500, 0xf94003e9#32), -- ldr x9, [sp]
  (504, 0x910043ff#32), -- add sp, sp, #0x10
  (508, 0xa9554ff4#32) -- ldp x20, x19, [sp, #0x150]
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xa95457f6#32), -- ldp x22, x21, [sp, #0x140]
  (516, 0xa9535ff8#32), -- ldp x24, x23, [sp, #0x130]
  (520, 0xa95267fa#32), -- ldp x26, x25, [sp, #0x120]
  (524, 0xa9516ffc#32), -- ldp x28, x27, [sp, #0x110]
  (528, 0xa9507bfd#32), -- ldp x29, x30, [sp, #0x100]
  (532, 0x910583ff#32), -- add sp, sp, #0x160
  (536, 0xd65f03c0#32), -- ret
  (540, 0xa948d3f7#32), -- ldp x23, x20, [sp, #0x88]
  (544, 0x910203e8#32), -- add x8, sp, #0x80
  (548, 0x910143e0#32), -- add x0, sp, #0x50
  (552, 0x91006101#32), -- add x1, x8, #0x18
  (556, 0x52800602#32), -- mov w2, #0x30               // =48
  (560, 0x94005391#32), -- bl 0x24d4d0 <memcpy>
  (564, 0x29595bf5#32), -- ldp w21, w22, [sp, #0xc8]
  (568, 0x910083e0#32), -- add x0, sp, #0x20
  (572, 0x910143e1#32), -- add x1, sp, #0x50
  (576, 0x52800602#32), -- mov w2, #0x30               // =48
  (580, 0x9400538c#32), -- bl 0x24d4d0 <memcpy>
  (584, 0x34000075#32), -- cbz w21, 0x2386b0 <.LBB105_22>
  (588, 0xf9400fe0#32), -- ldr x0, [sp, #0x18]
  (592, 0x17ffffd7#32), -- b 0x238608 <.LBB105_16>
  (596, 0xf9400fe0#32), -- ldr x0, [sp, #0x18]
  (600, 0x17ffffde#32), -- b 0x23862c <.LBB105_18>
  (604, 0xaa0803e0#32), -- mov x0, x8
  (608, 0xaa1803e2#32), -- mov x2, x24
  (612, 0x97ff96a0#32), -- bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>
  (616, 0xaa1603e0#32), -- mov x0, x22
  (620, 0xaa1603e1#32), -- mov x1, x22
  (624, 0x97ff96a9#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (628, 0xaa1703e0#32), -- mov x0, x23
  (632, 0xaa1703e1#32), -- mov x1, x23
  (636, 0x97ff96a6#32) -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
]

theorem chunk2_decodes :
    chunk2.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1 ++ chunk2

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

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, chunk2_decodes, Bool.and_self]

end SszArm.Codec.Linked.DecodeStructValues
