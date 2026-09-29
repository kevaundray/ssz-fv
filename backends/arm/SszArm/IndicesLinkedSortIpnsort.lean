import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.SortIpnsort

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN4core5slice4sort8unstable7ipnsort17h2a30cf48fed7d7bfE. -/
def address : Nat := 2374032

def byteSize : Nat := 440

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10143ff#32), -- sub sp, sp, #0x50
  (4, 0xf90003fe#32), -- str x30, [sp]
  (8, 0xa90167fa#32), -- stp x26, x25, [sp, #0x10]
  (12, 0xa9025ff8#32), -- stp x24, x23, [sp, #0x20]
  (16, 0xa90357f6#32), -- stp x22, x21, [sp, #0x30]
  (20, 0xa9044ff4#32), -- stp x20, x19, [sp, #0x40]
  (24, 0xaa0003f3#32), -- mov x19, x0
  (28, 0xa9410c02#32), -- ldp x2, x3, [x0, #0x10]
  (32, 0xf9400408#32), -- ldr x8, [x0, #0x8]
  (36, 0xf9400000#32), -- ldr x0, [x0]
  (40, 0xaa0103f4#32), -- mov x20, x1
  (44, 0xaa0803e1#32), -- mov x1, x8
  (48, 0xaa0203f6#32), -- mov x22, x2
  (52, 0xaa0303f7#32), -- mov x23, x3
  (56, 0x97ff86f9#32), -- bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>
  (60, 0x52801ff8#32), -- mov w24, #0xff // =255
  (64, 0x2a0003f5#32), -- mov w21, w0
  (68, 0x9100a27a#32), -- add x26, x19, #0x28
  (72, 0x52800059#32), -- mov w25, #0x2 // =2
  (76, 0xaa1703e1#32), -- mov x1, x23
  (80, 0x6a20031f#32), -- bics wzr, w24, w0
  (84, 0x540001e0#32), -- b.eq 0x243a20 <.LBB127_4>
  (88, 0xaa1603e0#32), -- mov x0, x22
  (92, 0xa97fdf56#32), -- ldp x22, x23, [x26, #-0x8]
  (96, 0xaa1603e2#32), -- mov x2, x22
  (100, 0xaa1703e3#32), -- mov x3, x23
  (104, 0x97ff86ed#32), -- bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>
  (108, 0x6a20031f#32), -- bics wzr, w24, w0
  (112, 0x540002c0#32), -- b.eq 0x243a58 <.LBB127_7>
  (116, 0x91000739#32), -- add x25, x25, #0x1
  (120, 0x9100435a#32), -- add x26, x26, #0x10
  (124, 0xaa1703e1#32), -- mov x1, x23
  (128, 0xeb19029f#32), -- cmp x20, x25
  (132, 0xaa1603e0#32), -- mov x0, x22
  (136, 0x54fffea1#32), -- b.ne 0x2439ec <.LBB127_2>
  (140, 0x14000011#32), -- b 0x243a60 <.LBB127_8>
  (144, 0xaa1603e0#32), -- mov x0, x22
  (148, 0xa97fdf56#32), -- ldp x22, x23, [x26, #-0x8]
  (152, 0xaa1603e2#32), -- mov x2, x22
  (156, 0xaa1703e3#32), -- mov x3, x23
  (160, 0x97ff86df#32), -- bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>
  (164, 0x6a20031f#32), -- bics wzr, w24, w0
  (168, 0x54000101#32), -- b.ne 0x243a58 <.LBB127_7>
  (172, 0x91000739#32), -- add x25, x25, #0x1
  (176, 0x9100435a#32), -- add x26, x26, #0x10
  (180, 0xaa1703e1#32), -- mov x1, x23
  (184, 0xeb19029f#32), -- cmp x20, x25
  (188, 0xaa1603e0#32), -- mov x0, x22
  (192, 0x54fffea1#32), -- b.ne 0x243a24 <.LBB127_5>
  (196, 0x14000003#32), -- b 0x243a60 <.LBB127_8>
  (200, 0xeb14033f#32), -- cmp x25, x20
  (204, 0x54000441#32), -- b.ne 0x243ae4 <.LBB127_12>
  (208, 0x52801fe8#32), -- mov w8, #0xff // =255
  (212, 0x6a35011f#32), -- bics wzr, w8, w21
  (216, 0x54000321#32), -- b.ne 0x243acc <.LBB127_11>
  (220, 0x8b14126a#32), -- add x10, x19, x20, lsl #4
  (224, 0xd341fe88#32), -- lsr x8, x20, #1
  (228, 0x91002269#32), -- add x9, x19, #0x8
  (232, 0xd100214a#32), -- sub x10, x10, #0x8
  (236, 0xa97fb94b#32), -- ldp x11, x14, [x10, #-0x8]
  (240, 0xd1000508#32), -- sub x8, x8, #0x1
  (244, 0xa97fb52c#32), -- ldp x12, x13, [x9, #-0x8]
  (248, 0xd10043ff#32), -- sub sp, sp, #0x10
  (252, 0xf90003ea#32) -- str x10, [sp]
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0x9100012a#32), -- add x10, x9, #0x0
  (260, 0xd100214a#32), -- sub x10, x10, #0x8
  (264, 0xf900014b#32), -- str x11, [x10]
  (268, 0xf94003ea#32), -- ldr x10, [sp]
  (272, 0x910043ff#32), -- add sp, sp, #0x10
  (276, 0xd10043ff#32), -- sub sp, sp, #0x10
  (280, 0xf90003e9#32), -- str x9, [sp]
  (284, 0x91000149#32), -- add x9, x10, #0x0
  (288, 0xd1002129#32), -- sub x9, x9, #0x8
  (292, 0xf900012c#32), -- str x12, [x9]
  (296, 0xf94003e9#32), -- ldr x9, [sp]
  (300, 0x910043ff#32), -- add sp, sp, #0x10
  (304, 0xf801052e#32), -- str x14, [x9], #0x10
  (308, 0xf81f054d#32), -- str x13, [x10], #-0x10
  (312, 0xb5fffda8#32), -- cbnz x8, 0x243a7c <.LBB127_10>
  (316, 0xa9444ff4#32), -- ldp x20, x19, [sp, #0x40]
  (320, 0xa94357f6#32), -- ldp x22, x21, [sp, #0x30]
  (324, 0xa9425ff8#32), -- ldp x24, x23, [sp, #0x20]
  (328, 0xa94167fa#32), -- ldp x26, x25, [sp, #0x10]
  (332, 0xf84507fe#32), -- ldr x30, [sp], #0x50
  (336, 0xd65f03c0#32), -- ret
  (340, 0xb2400288#32), -- orr x8, x20, #0x1
  (344, 0xaa1303e0#32), -- mov x0, x19
  (348, 0xaa1403e1#32), -- mov x1, x20
  (352, 0xd10043ff#32), -- sub sp, sp, #0x10
  (356, 0xf90003e9#32), -- str x9, [sp]
  (360, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (364, 0xaa0803e9#32), -- mov x9, x8
  (368, 0xd280080a#32), -- mov x10, #0x40 // =64
  (372, 0xb4000089#32), -- cbz x9, 0x243b14 <.Llower_arm_1110>
  (376, 0xd100054a#32), -- sub x10, x10, #0x1
  (380, 0xd341fd29#32), -- lsr x9, x9, #1
  (384, 0xb5ffffc9#32), -- cbnz x9, 0x243b08 <.Llower_arm_1109>
  (388, 0xaa0a03e8#32), -- mov x8, x10
  (392, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (396, 0xf94003e9#32), -- ldr x9, [sp]
  (400, 0x910043ff#32), -- add sp, sp, #0x10
  (404, 0xa9444ff4#32), -- ldp x20, x19, [sp, #0x40]
  (408, 0x531f7908#32), -- lsl w8, w8, #1
  (412, 0xa94357f6#32), -- ldp x22, x21, [sp, #0x30]
  (416, 0xa9425ff8#32), -- ldp x24, x23, [sp, #0x20]
  (420, 0xaa1f03e2#32), -- mov x2, xzr
  (424, 0xa94167fa#32), -- ldp x26, x25, [sp, #0x10]
  (428, 0x521f1503#32), -- eor w3, w8, #0x7e
  (432, 0xf84507fe#32), -- ldr x30, [sp], #0x50
  (436, 0x140000b8#32) -- b 0x243e24 <_ZN4core5slice4sort8unstable9quicksort9quicksort17h97a1f9ca3b379186E>
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete linked function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1

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

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, Bool.and_self]

theorem step_at (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (row : Nat × BitVec 32) (member : row ∈ program)
    (entry : read_pc s = base + BitVec.ofNat 64 row.1)
    (error : read_err s = .None) :
    stepi s = exec_inst (SszArm.Codec.Linked.decoded program all_decode row member) s :=
  SszArm.Codec.Linked.step_at program all_decode s base code row member entry error

end SszArm.Indices.Linked.SortIpnsort
