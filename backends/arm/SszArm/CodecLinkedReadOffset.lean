import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.ReadOffset

/-- Actual ELF entry address of _ZN13ssz_fv_native5codec11read_offset17h14742c7c7578f3fcE. -/
def address : Nat := 2322624

def byteSize : Nat := 108

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd10043ff#32), -- sub sp, sp, #0x10
  (4, 0xf90003fe#32), -- str x30, [sp]
  (8, 0xb4000201#32), -- cbz x1, 0x237108 <.LBB100_5>
  (12, 0xf100043f#32), -- cmp x1, #0x1
  (16, 0x54000200#32), -- b.eq 0x237110 <.LBB100_6>
  (20, 0xf100083f#32), -- cmp x1, #0x2
  (24, 0x54000209#32), -- b.ls 0x237118 <.LBB100_7>
  (28, 0xf1000c3f#32), -- cmp x1, #0x3
  (32, 0x54000220#32), -- b.eq 0x237124 <.LBB100_8>
  (36, 0x39400008#32), -- ldrb w8, [x0]
  (40, 0x39400409#32), -- ldrb w9, [x0, #0x1]
  (44, 0x3940080a#32), -- ldrb w10, [x0, #0x2]
  (48, 0xaa092108#32), -- orr x8, x8, x9, lsl #8
  (52, 0x39400c09#32), -- ldrb w9, [x0, #0x3]
  (56, 0xaa0a4108#32), -- orr x8, x8, x10, lsl #16
  (60, 0xaa096100#32), -- orr x0, x8, x9, lsl #24
  (64, 0xf84107fe#32), -- ldr x30, [sp], #0x10
  (68, 0xd65f03c0#32), -- ret
  (72, 0xaa1f03e0#32), -- mov x0, xzr
  (76, 0x97ff9c19#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (80, 0x52800020#32), -- mov w0, #0x1                // =1
  (84, 0x97ff9c17#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (88, 0x52800040#32), -- mov w0, #0x2                // =2
  (92, 0x52800041#32), -- mov w1, #0x2                // =2
  (96, 0x97ff9c14#32), -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
  (100, 0x52800060#32), -- mov w0, #0x3                // =3
  (104, 0x97ff9c12#32) -- bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>
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

end SszArm.Codec.Linked.ReadOffset
