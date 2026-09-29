import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.PlanSingleton

/-- Actual ELF entry address of _ZN13ssz_fv_native5arena5Arena10slice_with17h0d5d48f70484df3cE. -/
def address : Nat := 2299872

def byteSize : Nat := 376

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10083ff#32), -- sub sp, sp, #0x20
  (4, 0xf90003fe#32), -- str x30, [sp]
  (8, 0xa9014ff4#32), -- stp x20, x19, [sp, #0x10]
  (12, 0xf9400028#32), -- ldr x8, [x1]
  (16, 0xf9400829#32), -- ldr x9, [x1, #0x10]
  (20, 0xaa0003f3#32), -- mov x19, x0
  (24, 0xab08012a#32), -- adds x10, x9, x8
  (28, 0x54000462#32), -- b.hs 0x231888 <.LBB88_6>
  (32, 0xb100215f#32), -- cmn x10, #0x8
  (36, 0x54000428#32), -- b.hi 0x231888 <.LBB88_6>
  (40, 0x91001d4b#32), -- add x11, x10, #0x7
  (44, 0x927df16b#32), -- and x11, x11, #0xfffffffffffffff8
  (48, 0xcb0a016a#32), -- sub x10, x11, x10
  (52, 0xab090149#32), -- adds x9, x10, x9
  (56, 0x54000382#32), -- b.hs 0x231888 <.LBB88_6>
  (60, 0xb100a53f#32), -- cmn x9, #0x29
  (64, 0x54000348#32), -- b.hi 0x231888 <.LBB88_6>
  (68, 0xf940042b#32), -- ldr x11, [x1, #0x8]
  (72, 0x9100a12a#32), -- add x10, x9, #0x28
  (76, 0xeb0b015f#32), -- cmp x10, x11
  (80, 0x540002c8#32), -- b.hi 0x231888 <.LBB88_6>
  (84, 0x8b090114#32), -- add x20, x8, x9
  (88, 0xf900082a#32), -- str x10, [x1, #0x10]
  (92, 0xaa0203e1#32), -- mov x1, x2
  (96, 0xaa1403e0#32), -- mov x0, x20
  (100, 0x52800502#32), -- mov w2, #0x28               // =40
  (104, 0x94006f22#32), -- bl 0x24d4d0 <memcpy>
  (108, 0x52800028#32), -- mov w8, #0x1                // =1
  (112, 0xa9002274#32), -- stp x20, x8, [x19]
  (116, 0xd10043ff#32), -- sub sp, sp, #0x10
  (120, 0xf90003e9#32), -- str x9, [sp]
  (124, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (128, 0x91000269#32), -- add x9, x19, #0x0
  (132, 0x91010129#32), -- add x9, x9, #0x40
  (136, 0x5280000a#32), -- mov w10, #0x0               // =0
  (140, 0xb900012a#32), -- str w10, [x9]
  (144, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (148, 0xf94003e9#32), -- ldr x9, [sp]
  (152, 0x910043ff#32), -- add sp, sp, #0x10
  (156, 0xa9414ff4#32), -- ldp x20, x19, [sp, #0x10]
  (160, 0xf84207fe#32), -- ldr x30, [sp], #0x20
  (164, 0xd65f03c0#32), -- ret
  (168, 0xd10043ff#32), -- sub sp, sp, #0x10
  (172, 0xf90003e9#32), -- str x9, [sp]
  (176, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (180, 0x91000269#32), -- add x9, x19, #0x0
  (184, 0x9100c129#32), -- add x9, x9, #0x30
  (188, 0xd280000a#32), -- mov x10, #0x0               // =0
  (192, 0xf900012a#32), -- str x10, [x9]
  (196, 0xd280000a#32), -- mov x10, #0x0               // =0
  (200, 0xf900052a#32), -- str x10, [x9, #0x8]
  (204, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (208, 0xf94003e9#32), -- ldr x9, [sp]
  (212, 0x910043ff#32), -- add sp, sp, #0x10
  (216, 0x52900009#32), -- mov w9, #0x8000             // =32768
  (220, 0xd10043ff#32), -- sub sp, sp, #0x10
  (224, 0xf90003e9#32), -- str x9, [sp]
  (228, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (232, 0x91000269#32), -- add x9, x19, #0x0
  (236, 0x91008129#32), -- add x9, x9, #0x20
  (240, 0xd280000a#32), -- mov x10, #0x0               // =0
  (244, 0xf900012a#32), -- str x10, [x9]
  (248, 0xd280000a#32), -- mov x10, #0x0               // =0
  (252, 0xf900052a#32) -- str x10, [x9, #0x8]
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

def chunk1 : List (Nat × BitVec 32) := [
  (256, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (260, 0xf94003e9#32), -- ldr x9, [sp]
  (264, 0x910043ff#32), -- add sp, sp, #0x10
  (268, 0x52800034#32), -- mov w20, #0x1               // =1
  (272, 0xd10043ff#32), -- sub sp, sp, #0x10
  (276, 0xf90003e9#32), -- str x9, [sp]
  (280, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (284, 0x91000269#32), -- add x9, x19, #0x0
  (288, 0x91004129#32), -- add x9, x9, #0x10
  (292, 0xd280000a#32), -- mov x10, #0x0               // =0
  (296, 0xf900012a#32), -- str x10, [x9]
  (300, 0xd280000a#32), -- mov x10, #0x0               // =0
  (304, 0xf900052a#32), -- str x10, [x9, #0x8]
  (308, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (312, 0xf94003e9#32), -- ldr x9, [sp]
  (316, 0x910043ff#32), -- add sp, sp, #0x10
  (320, 0xd10043ff#32), -- sub sp, sp, #0x10
  (324, 0xf90003e9#32), -- str x9, [sp]
  (328, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (332, 0x91000269#32), -- add x9, x19, #0x0
  (336, 0xf9000134#32), -- str x20, [x9]
  (340, 0xd280000a#32), -- mov x10, #0x0               // =0
  (344, 0xf900052a#32), -- str x10, [x9, #0x8]
  (348, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (352, 0xf94003e9#32), -- ldr x9, [sp]
  (356, 0x910043ff#32), -- add sp, sp, #0x10
  (360, 0xb9004269#32), -- str w9, [x19, #0x40]
  (364, 0xa9414ff4#32), -- ldp x20, x19, [sp, #0x10]
  (368, 0xf84207fe#32), -- ldr x30, [sp], #0x20
  (372, 0xd65f03c0#32) -- ret
]

theorem chunk1_decodes :
    chunk1.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0 ++ chunk1

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

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, chunk1_decodes, Bool.and_self]

end SszArm.Codec.Linked.PlanSingleton
