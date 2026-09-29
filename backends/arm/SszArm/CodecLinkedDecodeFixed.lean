import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.DecodeFixed

/-- Actual ELF entry address of _ZN13ssz_fv_native5codec12decode_fixed17hd268ce61b5ac9b5fE. -/
def address : Nat := 2321936

def byteSize : Nat := 688

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10543ff#32), -- sub sp, sp, #0x150
  (4, 0xa90f7bfd#32), -- stp x29, x30, [sp, #0xf0]
  (8, 0xa9106ffc#32), -- stp x28, x27, [sp, #0x100]
  (12, 0xa91167fa#32), -- stp x26, x25, [sp, #0x110]
  (16, 0xa9125ff8#32), -- stp x24, x23, [sp, #0x120]
  (20, 0xa91357f6#32), -- stp x22, x21, [sp, #0x130]
  (24, 0xa9144ff4#32), -- stp x20, x19, [sp, #0x140]
  (28, 0xaa0203fc#32), -- mov x28, x2
  (32, 0xaa0003f3#32), -- mov x19, x0
  (36, 0xb40010a2#32), -- cbz x2, 0x237048 <.LBB99_16>
  (40, 0x52800608#32), -- mov w8, #0x30               // =48
  (44, 0xd100c3ff#32), -- sub sp, sp, #0x30
  (48, 0xf90003e9#32), -- str x9, [sp]
  (52, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (56, 0xf9000beb#32), -- str x11, [sp, #0x10]
  (60, 0xf9000fec#32), -- str x12, [sp, #0x18]
  (64, 0xf90013ed#32), -- str x13, [sp, #0x20]
  (68, 0xf90017ee#32), -- str x14, [sp, #0x28]
  (72, 0x2a1c03e9#32), -- mov w9, w28
  (76, 0xd360ff8a#32), -- lsr x10, x28, #32
  (80, 0x2a0803eb#32), -- mov w11, w8
  (84, 0xd360fd0c#32), -- lsr x12, x8, #32
  (88, 0x9b0b7d2d#32), -- mul x13, x9, x11
  (92, 0xd360fdad#32), -- lsr x13, x13, #32
  (96, 0x9b0b354d#32), -- madd x13, x10, x11, x13
  (100, 0xd360fdab#32), -- lsr x11, x13, #32
  (104, 0x2a0d03ee#32), -- mov w14, w13
  (108, 0x9b0c392e#32), -- madd x14, x9, x12, x14
  (112, 0xd360fdce#32), -- lsr x14, x14, #32
  (116, 0x9b0c2d4d#32), -- madd x13, x10, x12, x11
  (120, 0x8b0e01ad#32), -- add x13, x13, x14
  (124, 0xaa0d03e8#32), -- mov x8, x13
  (128, 0xf94017ee#32), -- ldr x14, [sp, #0x28]
  (132, 0xf94013ed#32), -- ldr x13, [sp, #0x20]
  (136, 0xf9400fec#32), -- ldr x12, [sp, #0x18]
  (140, 0xf9400beb#32), -- ldr x11, [sp, #0x10]
  (144, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (148, 0xf94003e9#32), -- ldr x9, [sp]
  (152, 0x9100c3ff#32), -- add sp, sp, #0x30
  (156, 0xeb0803ff#32), -- cmp xzr, x8
  (160, 0x54000b01#32), -- b.ne 0x237010 <.LBB99_14>
  (164, 0x8b1c0788#32), -- add x8, x28, x28, lsl #1
  (168, 0xd37ced09#32), -- lsl x9, x8, #4
  (172, 0xd10043ff#32), -- sub sp, sp, #0x10
  (176, 0xf90003ea#32), -- str x10, [sp]
  (180, 0x9241012a#32), -- and x10, x9, #0x8000000000000000
  (184, 0xb500008a#32), -- cbnz x10, 0x236ed8 <.Llower_arm_721>
  (188, 0xf94003ea#32), -- ldr x10, [sp]
  (192, 0x910043ff#32), -- add sp, sp, #0x10
  (196, 0x14000004#32), -- b 0x236ee4 <.Llower_arm_722>
  (200, 0xf94003ea#32), -- ldr x10, [sp]
  (204, 0x910043ff#32), -- add sp, sp, #0x10
  (208, 0x1400004c#32), -- b 0x237010 <.LBB99_14>
  (212, 0xf94000c8#32), -- ldr x8, [x6]
  (216, 0xf94008cb#32), -- ldr x11, [x6, #0x10]
  (220, 0xaa0603f6#32), -- mov x22, x6
  (224, 0xab08016c#32), -- adds x12, x11, x8
  (228, 0x540008e2#32), -- b.hs 0x237010 <.LBB99_14>
  (232, 0xb100419f#32), -- cmn x12, #0x10
  (236, 0x540008a8#32), -- b.hi 0x237010 <.LBB99_14>
  (240, 0x91003d8a#32), -- add x10, x12, #0xf
  (244, 0x927ced4a#32), -- and x10, x10, #0xfffffffffffffff0
  (248, 0xcb0c014c#32), -- sub x12, x10, x12
  (252, 0xab0b018b#32) -- adds x11, x12, x11
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0x54000802#32), -- b.hs 0x237010 <.LBB99_14>
  (260, 0xab090169#32), -- adds x9, x11, x9
  (264, 0x540007c2#32), -- b.hs 0x237010 <.LBB99_14>
  (268, 0xf94006cc#32), -- ldr x12, [x22, #0x8]
  (272, 0xeb0c013f#32), -- cmp x9, x12
  (276, 0x54000768#32), -- b.hi 0x237010 <.LBB99_14>
  (280, 0xaa0503f5#32), -- mov x21, x5
  (284, 0xaa0403f7#32), -- mov x23, x4
  (288, 0xaa0303f8#32), -- mov x24, x3
  (292, 0xaa0103f9#32), -- mov x25, x1
  (296, 0xaa1f03fa#32), -- mov x26, xzr
  (300, 0x8b0b0108#32), -- add x8, x8, x11
  (304, 0x9100215b#32), -- add x27, x10, #0x8
  (308, 0xaa1c03f4#32), -- mov x20, x28
  (312, 0xf9000ac9#32), -- str x9, [x22, #0x10]
  (316, 0xf90007e8#32), -- str x8, [sp, #0x8]
  (320, 0xab1a0301#32), -- adds x1, x24, x26
  (324, 0x54000b02#32), -- b.hs 0x2370b4 <.LBB99_20>
  (328, 0xeb15003f#32), -- cmp x1, x21
  (332, 0x54000ac8#32), -- b.hi 0x2370b4 <.LBB99_20>
  (336, 0x9101c3e0#32), -- add x0, sp, #0x70
  (340, 0x8b1a02e2#32), -- add x2, x23, x26
  (344, 0xaa1903e1#32), -- mov x1, x25
  (348, 0xaa1803e3#32), -- mov x3, x24
  (352, 0xaa1603e4#32), -- mov x4, x22
  (356, 0x97fff38b#32), -- bl 0x233da0 <_ZN13ssz_fv_native5codec11deserialize17h539c5ca52740cbedE>
  (360, 0xb94073e8#32), -- ldr w8, [sp, #0x70]
  (364, 0xd10043ff#32), -- sub sp, sp, #0x10
  (368, 0xf90003e9#32), -- str x9, [sp]
  (372, 0x12000109#32), -- and w9, w8, #0x1
  (376, 0x35000089#32), -- cbnz w9, 0x236f98 <.Llower_arm_723>
  (380, 0xf94003e9#32), -- ldr x9, [sp]
  (384, 0x910043ff#32), -- add sp, sp, #0x10
  (388, 0x14000004#32), -- b 0x236fa4 <.Llower_arm_724>
  (392, 0xf94003e9#32), -- ldr x9, [sp]
  (396, 0x910043ff#32), -- add sp, sp, #0x10
  (400, 0x14000038#32), -- b 0x237080 <.LBB99_19>
  (404, 0x9101c3e8#32), -- add x8, sp, #0x70
  (408, 0xf94043fd#32), -- ldr x29, [sp, #0x80]
  (412, 0x910103e0#32), -- add x0, sp, #0x40
  (416, 0x91006101#32), -- add x1, x8, #0x18
  (420, 0x52800502#32), -- mov w2, #0x28               // =40
  (424, 0x94005946#32), -- bl 0x24d4d0 <memcpy>
  (428, 0x910323e0#32), -- add x0, sp, #0xc8
  (432, 0x910103e1#32), -- add x1, sp, #0x40
  (436, 0x52800502#32), -- mov w2, #0x28               // =40
  (440, 0x94005942#32), -- bl 0x24d4d0 <memcpy>
  (444, 0x910323e1#32), -- add x1, sp, #0xc8
  (448, 0xaa1b03e0#32), -- mov x0, x27
  (452, 0x52800502#32), -- mov w2, #0x28               // =40
  (456, 0xd10043ff#32), -- sub sp, sp, #0x10
  (460, 0xf90003e9#32), -- str x9, [sp]
  (464, 0x91000369#32), -- add x9, x27, #0x0
  (468, 0xd1002129#32), -- sub x9, x9, #0x8
  (472, 0xf900013d#32), -- str x29, [x9]
  (476, 0xf94003e9#32), -- ldr x9, [sp]
  (480, 0x910043ff#32), -- add sp, sp, #0x10
  (484, 0x94005937#32), -- bl 0x24d4d0 <memcpy>
  (488, 0xf1000694#32), -- subs x20, x20, #0x1
  (492, 0x9100c37b#32), -- add x27, x27, #0x30
  (496, 0x8b18035a#32), -- add x26, x26, x24
  (500, 0x54fffa61#32), -- b.ne 0x236f50 <.LBB99_9>
  (504, 0xf94007f6#32), -- ldr x22, [sp, #0x8]
  (508, 0x14000010#32) -- b 0x23704c <.LBB99_17>
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0x6f00e400#32), -- movi v0.2d, #0000000000000000
  (516, 0xaa1f03fc#32), -- mov x28, xzr
  (520, 0x52900014#32), -- mov w20, #0x8000            // =32768
  (524, 0x52800036#32), -- mov w22, #0x1               // =1
  (528, 0xad0103e0#32), -- stp q0, q0, [sp, #0x20]
  (532, 0x3d8007e0#32), -- str q0, [sp, #0x10]
  (536, 0x91006260#32), -- add x0, x19, #0x18
  (540, 0x910043e1#32), -- add x1, sp, #0x10
  (544, 0x52800602#32), -- mov w2, #0x30               // =48
  (548, 0x94005927#32), -- bl 0x24d4d0 <memcpy>
  (552, 0x52800028#32), -- mov w8, #0x1                // =1
  (556, 0xa900f276#32), -- stp x22, x28, [x19, #0x8]
  (560, 0x29095674#32), -- stp w20, w21, [x19, #0x48]
  (564, 0x14000006#32), -- b 0x23705c <.LBB99_18>
  (568, 0x52800216#32), -- mov w22, #0x10              // =16
  (572, 0x52800089#32), -- mov w9, #0x4                // =4
  (576, 0xaa1f03e8#32), -- mov x8, xzr
  (580, 0xa901f276#32), -- stp x22, x28, [x19, #0x18]
  (584, 0x39004269#32), -- strb w9, [x19, #0x10]
  (588, 0xf9000268#32), -- str x8, [x19]
  (592, 0xa9544ff4#32), -- ldp x20, x19, [sp, #0x140]
  (596, 0xa95357f6#32), -- ldp x22, x21, [sp, #0x130]
  (600, 0xa9525ff8#32), -- ldp x24, x23, [sp, #0x120]
  (604, 0xa95167fa#32), -- ldp x26, x25, [sp, #0x110]
  (608, 0xa9506ffc#32), -- ldp x28, x27, [sp, #0x100]
  (612, 0xa94f7bfd#32), -- ldp x29, x30, [sp, #0xf0]
  (616, 0x910543ff#32), -- add sp, sp, #0x150
  (620, 0xd65f03c0#32), -- ret
  (624, 0xa947f3f6#32), -- ldp x22, x28, [sp, #0x78]
  (628, 0x9101c3e8#32), -- add x8, sp, #0x70
  (632, 0x910103e0#32), -- add x0, sp, #0x40
  (636, 0x91006101#32), -- add x1, x8, #0x18
  (640, 0x52800602#32), -- mov w2, #0x30               // =48
  (644, 0x9400590f#32), -- bl 0x24d4d0 <memcpy>
  (648, 0x295757f4#32), -- ldp w20, w21, [sp, #0xb8]
  (652, 0x910043e0#32), -- add x0, sp, #0x10
  (656, 0x910103e1#32), -- add x1, sp, #0x40
  (660, 0x52800602#32), -- mov w2, #0x30               // =48
  (664, 0x9400590a#32), -- bl 0x24d4d0 <memcpy>
  (668, 0x35fffbf4#32), -- cbnz w20, 0x237028 <.LBB99_15>
  (672, 0x17ffffe7#32), -- b 0x23704c <.LBB99_17>
  (676, 0xaa1a03e0#32), -- mov x0, x26
  (680, 0xaa1503e2#32), -- mov x2, x21
  (684, 0x97ff9c21#32) -- bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>
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

end SszArm.Codec.Linked.DecodeFixed
