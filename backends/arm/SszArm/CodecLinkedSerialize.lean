import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.Serialize

/-- Actual ELF entry address of _ZN13ssz_fv_native5codec9serialize17h0d728b7a742b35d3E. -/
def address : Nat := 2328536

def byteSize : Nat := 692

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10243ff#32), -- sub sp, sp, #0x90
  (4, 0xa9065ffe#32), -- stp x30, x23, [sp, #0x60]
  (8, 0xa90757f6#32), -- stp x22, x21, [sp, #0x70]
  (12, 0xa9084ff4#32), -- stp x20, x19, [sp, #0x80]
  (16, 0xaa0403f7#32), -- mov x23, x4
  (20, 0xaa0303f4#32), -- mov x20, x3
  (24, 0xaa0003f3#32), -- mov x19, x0
  (28, 0x910063e0#32), -- add x0, sp, #0x18
  (32, 0xaa0503e3#32), -- mov x3, x5
  (36, 0x52800024#32), -- mov w4, #0x1                // =1
  (40, 0xaa0203f5#32), -- mov x21, x2
  (44, 0xaa0103f6#32), -- mov x22, x1
  (48, 0x97ffdabd#32), -- bl 0x22f2fc <_ZN13ssz_fv_native5codec7measure17h6f170d30c3984362E>
  (52, 0xa941b3eb#32), -- ldp x11, x12, [sp, #0x18]
  (56, 0xb9405be9#32), -- ldr w9, [sp, #0x58]
  (60, 0xa94297e8#32), -- ldp x8, x5, [sp, #0x28]
  (64, 0xf9401fea#32), -- ldr x10, [sp, #0x38]
  (68, 0xa900b3eb#32), -- stp x11, x12, [sp, #0x8]
  (72, 0x34000209#32), -- cbz w9, 0x238860 <.LBB107_2>
  (76, 0xa94433eb#32), -- ldp x11, x12, [sp, #0x40]
  (80, 0xf9402bed#32), -- ldr x13, [sp, #0x50]
  (84, 0xa9011668#32), -- stp x8, x5, [x19, #0x10]
  (88, 0xb9405fe8#32), -- ldr w8, [sp, #0x5c]
  (92, 0xf9001e6d#32), -- str x13, [x19, #0x38]
  (96, 0xa902b26b#32), -- stp x11, x12, [x19, #0x28]
  (100, 0xa940b3eb#32), -- ldp x11, x12, [sp, #0x8]
  (104, 0xf900126a#32), -- str x10, [x19, #0x20]
  (108, 0x29082269#32), -- stp w9, w8, [x19, #0x40]
  (112, 0xa900326b#32), -- stp x11, x12, [x19]
  (116, 0xa9484ff4#32), -- ldp x20, x19, [sp, #0x80]
  (120, 0xa94757f6#32), -- ldp x22, x21, [sp, #0x70]
  (124, 0xa9465ffe#32), -- ldp x30, x23, [sp, #0x60]
  (128, 0x910243ff#32), -- add sp, sp, #0x90
  (132, 0xd65f03c0#32), -- ret
  (136, 0xa940afe9#32), -- ldp x9, x11, [sp, #0x8]
  (140, 0xa90297e8#32), -- stp x8, x5, [sp, #0x28]
  (144, 0xf9001fea#32), -- str x10, [sp, #0x38]
  (148, 0xa901afe9#32), -- stp x9, x11, [sp, #0x18]
  (152, 0xb4000888#32), -- cbz x8, 0x238980 <.LBB107_10>
  (156, 0xd10004aa#32), -- sub x10, x5, #0x1
  (160, 0xb100055f#32), -- cmn x10, #0x1
  (164, 0x540007e0#32), -- b.eq 0x238978 <.LBB107_8>
  (168, 0xd10043ff#32), -- sub sp, sp, #0x10
  (172, 0xf90003e9#32), -- str x9, [sp]
  (176, 0xaa0a03e9#32), -- mov x9, x10
  (180, 0xd37df129#32), -- lsl x9, x9, #3
  (184, 0x8b090109#32), -- add x9, x8, x9
  (188, 0xf940012b#32), -- ldr x11, [x9]
  (192, 0xf94003e9#32), -- ldr x9, [sp]
  (196, 0x910043ff#32), -- add sp, sp, #0x10
  (200, 0xaa0a03e9#32), -- mov x9, x10
  (204, 0xd100054a#32), -- sub x10, x10, #0x1
  (208, 0xb4fffe8b#32), -- cbz x11, 0x238878 <.LBB107_4>
  (212, 0x91000529#32), -- add x9, x9, #0x1
  (216, 0xf100053f#32), -- cmp x9, #0x1
  (220, 0x54000640#32), -- b.eq 0x23897c <.LBB107_9>
  (224, 0x52800028#32), -- mov w8, #0x1                // =1
  (228, 0xd10043ff#32), -- sub sp, sp, #0x10
  (232, 0xf90003e9#32), -- str x9, [sp]
  (236, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (240, 0x91000269#32), -- add x9, x19, #0x0
  (244, 0x9100c129#32), -- add x9, x9, #0x30
  (248, 0xd280000a#32), -- mov x10, #0x0               // =0
  (252, 0xf900012a#32) -- str x10, [x9]
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0xd280000a#32), -- mov x10, #0x0               // =0
  (260, 0xf900052a#32), -- str x10, [x9, #0x8]
  (264, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (268, 0xf94003e9#32), -- ldr x9, [sp]
  (272, 0x910043ff#32), -- add sp, sp, #0x10
  (276, 0xd10043ff#32), -- sub sp, sp, #0x10
  (280, 0xf90003e9#32), -- str x9, [sp]
  (284, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (288, 0x91000269#32), -- add x9, x19, #0x0
  (292, 0x91008129#32), -- add x9, x9, #0x20
  (296, 0xd280000a#32), -- mov x10, #0x0               // =0
  (300, 0xf900012a#32), -- str x10, [x9]
  (304, 0xd280000a#32), -- mov x10, #0x0               // =0
  (308, 0xf900052a#32), -- str x10, [x9, #0x8]
  (312, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (316, 0xf94003e9#32), -- ldr x9, [sp]
  (320, 0x910043ff#32), -- add sp, sp, #0x10
  (324, 0xd10043ff#32), -- sub sp, sp, #0x10
  (328, 0xf90003e9#32), -- str x9, [sp]
  (332, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (336, 0x91000269#32), -- add x9, x19, #0x0
  (340, 0x91004129#32), -- add x9, x9, #0x10
  (344, 0xd280000a#32), -- mov x10, #0x0               // =0
  (348, 0xf900012a#32), -- str x10, [x9]
  (352, 0xd280000a#32), -- mov x10, #0x0               // =0
  (356, 0xf900052a#32), -- str x10, [x9, #0x8]
  (360, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (364, 0xf94003e9#32), -- ldr x9, [sp]
  (368, 0x910043ff#32), -- add sp, sp, #0x10
  (372, 0xd10043ff#32), -- sub sp, sp, #0x10
  (376, 0xf90003e9#32), -- str x9, [sp]
  (380, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (384, 0x91000269#32), -- add x9, x19, #0x0
  (388, 0xf9000128#32), -- str x8, [x9]
  (392, 0xd280000a#32), -- mov x10, #0x0               // =0
  (396, 0xf900052a#32), -- str x10, [x9, #0x8]
  (400, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (404, 0xf94003e9#32), -- ldr x9, [sp]
  (408, 0x910043ff#32), -- add sp, sp, #0x10
  (412, 0x14000034#32), -- b 0x238a44 <.LBB107_12>
  (416, 0xb4000745#32), -- cbz x5, 0x238a60 <.LBB107_13>
  (420, 0xf9400105#32), -- ldr x5, [x8]
  (424, 0xeb0502ff#32), -- cmp x23, x5
  (428, 0x540006e2#32), -- b.hs 0x238a60 <.LBB107_13>
  (432, 0x52800028#32), -- mov w8, #0x1                // =1
  (436, 0xd10043ff#32), -- sub sp, sp, #0x10
  (440, 0xf90003e9#32), -- str x9, [sp]
  (444, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (448, 0x91000269#32), -- add x9, x19, #0x0
  (452, 0x91004129#32), -- add x9, x9, #0x10
  (456, 0xd280000a#32), -- mov x10, #0x0               // =0
  (460, 0xf900012a#32), -- str x10, [x9]
  (464, 0xd280000a#32), -- mov x10, #0x0               // =0
  (468, 0xf900052a#32), -- str x10, [x9, #0x8]
  (472, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (476, 0xf94003e9#32), -- ldr x9, [sp]
  (480, 0x910043ff#32), -- add sp, sp, #0x10
  (484, 0xd10043ff#32), -- sub sp, sp, #0x10
  (488, 0xf90003e9#32), -- str x9, [sp]
  (492, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (496, 0x91000269#32), -- add x9, x19, #0x0
  (500, 0xf9000128#32), -- str x8, [x9]
  (504, 0xd280000a#32), -- mov x10, #0x0               // =0
  (508, 0xf900052a#32) -- str x10, [x9, #0x8]
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk2 : List (Nat × BitVec 32) := [
  (512, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (516, 0xf94003e9#32), -- ldr x9, [sp]
  (520, 0x910043ff#32), -- add sp, sp, #0x10
  (524, 0xd10043ff#32), -- sub sp, sp, #0x10
  (528, 0xf90003e9#32), -- str x9, [sp]
  (532, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (536, 0x91000269#32), -- add x9, x19, #0x0
  (540, 0x91008129#32), -- add x9, x9, #0x20
  (544, 0xd280000a#32), -- mov x10, #0x0               // =0
  (548, 0xf900012a#32), -- str x10, [x9]
  (552, 0xd280000a#32), -- mov x10, #0x0               // =0
  (556, 0xf900052a#32), -- str x10, [x9, #0x8]
  (560, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (564, 0xf94003e9#32), -- ldr x9, [sp]
  (568, 0x910043ff#32), -- add sp, sp, #0x10
  (572, 0xd10043ff#32), -- sub sp, sp, #0x10
  (576, 0xf90003e9#32), -- str x9, [sp]
  (580, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (584, 0x91000269#32), -- add x9, x19, #0x0
  (588, 0x9100c129#32), -- add x9, x9, #0x30
  (592, 0xd280000a#32), -- mov x10, #0x0               // =0
  (596, 0xf900012a#32), -- str x10, [x9]
  (600, 0xd280000a#32), -- mov x10, #0x0               // =0
  (604, 0xf900052a#32), -- str x10, [x9, #0x8]
  (608, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (612, 0xf94003e9#32), -- ldr x9, [sp]
  (616, 0x910043ff#32), -- add sp, sp, #0x10
  (620, 0x52900028#32), -- mov w8, #0x8001             // =32769
  (624, 0xb9004268#32), -- str w8, [x19, #0x40]
  (628, 0xa9484ff4#32), -- ldp x20, x19, [sp, #0x80]
  (632, 0xa94757f6#32), -- ldp x22, x21, [sp, #0x70]
  (636, 0xa9465ffe#32), -- ldp x30, x23, [sp, #0x60]
  (640, 0x910243ff#32), -- add sp, sp, #0x90
  (644, 0xd65f03c0#32), -- ret
  (648, 0x910063e3#32), -- add x3, sp, #0x18
  (652, 0xaa1303e0#32), -- mov x0, x19
  (656, 0xaa1603e1#32), -- mov x1, x22
  (660, 0xaa1503e2#32), -- mov x2, x21
  (664, 0xaa1403e4#32), -- mov x4, x20
  (668, 0x97ffde62#32), -- bl 0x2303fc <_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE>
  (672, 0xa9484ff4#32), -- ldp x20, x19, [sp, #0x80]
  (676, 0xa94757f6#32), -- ldp x22, x21, [sp, #0x70]
  (680, 0xa9465ffe#32), -- ldp x30, x23, [sp, #0x60]
  (684, 0x910243ff#32), -- add sp, sp, #0x90
  (688, 0xd65f03c0#32) -- ret
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

end SszArm.Codec.Linked.Serialize
