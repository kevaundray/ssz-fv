import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.IsFixed

/-- Actual ELF entry address of _ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E. -/
def address : Nat := 2297968

def byteSize : Nat := 204

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10083ff#32), -- sub sp, sp, #0x20
  (4, 0xf90003fe#32), -- str x30, [sp]
  (8, 0xa9014ff4#32), -- stp x20, x19, [sp, #0x10]
  (12, 0xf9400008#32), -- ldr x8, [x0]
  (16, 0xf1001d1f#32), -- cmp x8, #0x7
  (20, 0x540000a1#32), -- b.ne 0x231098 <.LBB86_2>
  (24, 0xf9400c00#32), -- ldr x0, [x0, #0x18]
  (28, 0xf9400008#32), -- ldr x8, [x0]
  (32, 0xf1001d1f#32), -- cmp x8, #0x7
  (36, 0x54ffffa0#32), -- b.eq 0x231088 <.LBB86_1>
  (40, 0xf1000d1f#32), -- cmp x8, #0x3
  (44, 0x5400006c#32), -- b.gt 0x2310a8 <.LBB86_4>
  (48, 0x54000463#32), -- b.lo 0x23112c <.LBB86_13>
  (52, 0x1400001e#32), -- b 0x23111c <.Llower_arm_638>
  (56, 0xf100111f#32), -- cmp x8, #0x4
  (60, 0x54000400#32), -- b.eq 0x23112c <.LBB86_13>
  (64, 0xf100291f#32), -- cmp x8, #0xa
  (68, 0x540000a0#32), -- b.eq 0x2310c8 <.LBB86_8>
  (72, 0xf1002d1f#32), -- cmp x8, #0xb
  (76, 0x54000301#32), -- b.ne 0x23111c <.Llower_arm_638>
  (80, 0x52800308#32), -- mov w8, #0x18               // =24
  (84, 0x14000002#32), -- b 0x2310cc <.LBB86_9>
  (88, 0x52800108#32), -- mov w8, #0x8                // =8
  (92, 0x8b080008#32), -- add x8, x0, x8
  (96, 0xa9402508#32), -- ldp x8, x9, [x8]
  (100, 0x8b090529#32), -- add x9, x9, x9, lsl #1
  (104, 0xd37df133#32), -- lsl x19, x9, #3
  (108, 0xb4000293#32), -- cbz x19, 0x23112c <.LBB86_13>
  (112, 0xf9400900#32), -- ldr x0, [x8, #0x10]
  (116, 0x91006114#32), -- add x20, x8, #0x18
  (120, 0x97ffffe2#32), -- bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>
  (124, 0xd1006273#32), -- sub x19, x19, #0x18
  (128, 0xaa1403e8#32), -- mov x8, x20
  (132, 0xd10043ff#32), -- sub sp, sp, #0x10
  (136, 0xf90003e9#32), -- str x9, [sp]
  (140, 0x12000009#32), -- and w9, w0, #0x1
  (144, 0x35000089#32), -- cbnz w9, 0x231110 <.Llower_arm_637>
  (148, 0xf94003e9#32), -- ldr x9, [sp]
  (152, 0x910043ff#32), -- add sp, sp, #0x10
  (156, 0x14000004#32), -- b 0x23111c <.Llower_arm_638>
  (160, 0xf94003e9#32), -- ldr x9, [sp]
  (164, 0x910043ff#32), -- add sp, sp, #0x10
  (168, 0x17fffff1#32), -- b 0x2310dc <.LBB86_10>
  (172, 0x2a1f03e0#32), -- mov w0, wzr
  (176, 0xa9414ff4#32), -- ldp x20, x19, [sp, #0x10]
  (180, 0xf84207fe#32), -- ldr x30, [sp], #0x20
  (184, 0xd65f03c0#32), -- ret
  (188, 0x52800020#32), -- mov w0, #0x1                // =1
  (192, 0xa9414ff4#32), -- ldp x20, x19, [sp, #0x10]
  (196, 0xf84207fe#32), -- ldr x30, [sp], #0x20
  (200, 0xd65f03c0#32) -- ret
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete function, including every real panic block. -/
def program : List (Nat × BitVec 32) :=
  chunk0

def CodeAt (s : ArmState) (base : BitVec 64) : Prop :=
  WordsAt program s base

theorem chunk0_codeAt {s : ArmState} {base : BitVec 64}
    (code : CodeAt s base) : WordsAt chunk0 s base := by
  intro row member
  apply code row
  simp only [program, List.mem_append]
  exact member

theorem all_decode :
    program.all (fun row => (decode_raw_inst row.2).isSome) = true := by
  simp only [program, List.all_append, chunk0_decodes, Bool.and_self]

end SszArm.Codec.Linked.IsFixed
