import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.Bounded

/-- Actual ELF entry address of _ZN13ssz_fv_native5codec7bounded17haa64e3a0177cad3fE. -/
def address : Nat := 2328284

def byteSize : Nat := 252

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xd100c3ff#32), -- sub sp, sp, #0x30
  (4, 0xf90003fe#32), -- str x30, [sp]
  (8, 0xa90157f6#32), -- stp x22, x21, [sp, #0x10]
  (12, 0xa9024ff4#32), -- stp x20, x19, [sp, #0x20]
  (16, 0xb9400028#32), -- ldr w8, [x1]
  (20, 0xaa0003f3#32), -- mov x19, x0
  (24, 0x7100051f#32), -- cmp w8, #0x1
  (28, 0x54000541#32), -- b.ne 0x2387a0 <.LBB106_3>
  (32, 0xa940d835#32), -- ldp x21, x22, [x1, #0x8]
  (36, 0xaa0203f4#32), -- mov x20, x2
  (40, 0xa9400440#32), -- ldp x0, x1, [x2]
  (44, 0xaa1503e2#32), -- mov x2, x21
  (48, 0xaa1603e3#32), -- mov x3, x22
  (52, 0x97ffb3a7#32), -- bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>
  (56, 0x13001c08#32), -- sxtb w8, w0
  (60, 0x7100051f#32), -- cmp w8, #0x1
  (64, 0x5400042b#32), -- b.lt 0x2387a0 <.LBB106_3>
  (68, 0x52800028#32), -- mov w8, #0x1                // =1
  (72, 0xa9015a75#32), -- stp x21, x22, [x19, #0x10]
  (76, 0xd10043ff#32), -- sub sp, sp, #0x10
  (80, 0xf90003e9#32), -- str x9, [sp]
  (84, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (88, 0x91000269#32), -- add x9, x19, #0x0
  (92, 0xf9000128#32), -- str x8, [x9]
  (96, 0xd280000a#32), -- mov x10, #0x0               // =0
  (100, 0xf900052a#32), -- str x10, [x9, #0x8]
  (104, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (108, 0xf94003e9#32), -- ldr x9, [sp]
  (112, 0x910043ff#32), -- add sp, sp, #0x10
  (116, 0xa9402688#32), -- ldp x8, x9, [x20]
  (120, 0xd10043ff#32), -- sub sp, sp, #0x10
  (124, 0xf90003e9#32), -- str x9, [sp]
  (128, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (132, 0x91000269#32), -- add x9, x19, #0x0
  (136, 0x9100c129#32), -- add x9, x9, #0x30
  (140, 0xd280000a#32), -- mov x10, #0x0               // =0
  (144, 0xf900012a#32), -- str x10, [x9]
  (148, 0xd280000a#32), -- mov x10, #0x0               // =0
  (152, 0xf900052a#32), -- str x10, [x9, #0x8]
  (156, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (160, 0xf94003e9#32), -- ldr x9, [sp]
  (164, 0x910043ff#32), -- add sp, sp, #0x10
  (168, 0xa9022668#32), -- stp x8, x9, [x19, #0x20]
  (172, 0x52800048#32), -- mov w8, #0x2                // =2
  (176, 0xb9004268#32), -- str w8, [x19, #0x40]
  (180, 0xa9424ff4#32), -- ldp x20, x19, [sp, #0x20]
  (184, 0xa94157f6#32), -- ldp x22, x21, [sp, #0x10]
  (188, 0xf84307fe#32), -- ldr x30, [sp], #0x30
  (192, 0xd65f03c0#32), -- ret
  (196, 0xd10043ff#32), -- sub sp, sp, #0x10
  (200, 0xf90003e9#32), -- str x9, [sp]
  (204, 0xf90007ea#32), -- str x10, [sp, #0x8]
  (208, 0x91000269#32), -- add x9, x19, #0x0
  (212, 0x91010129#32), -- add x9, x9, #0x40
  (216, 0x5280000a#32), -- mov w10, #0x0               // =0
  (220, 0xb900012a#32), -- str w10, [x9]
  (224, 0xf94007ea#32), -- ldr x10, [sp, #0x8]
  (228, 0xf94003e9#32), -- ldr x9, [sp]
  (232, 0x910043ff#32), -- add sp, sp, #0x10
  (236, 0xa9424ff4#32), -- ldp x20, x19, [sp, #0x20]
  (240, 0xa94157f6#32), -- ldp x22, x21, [sp, #0x10]
  (244, 0xf84307fe#32), -- ldr x30, [sp], #0x30
  (248, 0xd65f03c0#32) -- ret
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

end SszArm.Codec.Linked.Bounded
