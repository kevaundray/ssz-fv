import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.NatCmpUsize

/-- Actual ELF entry address of _ZN13ssz_fv_native3nat3Nat9cmp_usize17h857d9c8293a9444eE. -/
def address : Nat := 2274508

def byteSize : Nat := 172

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xb4000340#32), -- cbz x0, 0x22b534 <.LBB65_9>
  (4, 0xd1000429#32), -- sub x9, x1, #0x1
  (8, 0xb100053f#32), -- cmn x9, #0x1
  (12, 0x54000220#32), -- b.eq 0x22b51c <.LBB65_6>
  (16, 0xd10043ff#32), -- sub sp, sp, #0x10
  (20, 0xf90003eb#32), -- str x11, [sp]
  (24, 0xaa0903eb#32), -- mov x11, x9
  (28, 0xd37df16b#32), -- lsl x11, x11, #3
  (32, 0x8b0b000b#32), -- add x11, x0, x11
  (36, 0xf940016a#32), -- ldr x10, [x11]
  (40, 0xf94003eb#32), -- ldr x11, [sp]
  (44, 0x910043ff#32), -- add sp, sp, #0x10
  (48, 0xaa0903e8#32), -- mov x8, x9
  (52, 0xd1000529#32), -- sub x9, x9, #0x1
  (56, 0xb4fffe8a#32), -- cbz x10, 0x22b4d4 <.LBB65_2>
  (60, 0x91000508#32), -- add x8, x8, #0x1
  (64, 0xf1000d1f#32), -- cmp x8, #0x3
  (68, 0x54000083#32), -- b.lo 0x22b520 <.LBB65_7>
  (72, 0x52800020#32), -- mov w0, #0x1                // =1
  (76, 0xd65f03c0#32), -- ret
  (80, 0xb40000c1#32), -- cbz x1, 0x22b534 <.LBB65_9>
  (84, 0xf9400009#32), -- ldr x9, [x0]
  (88, 0xf100083f#32), -- cmp x1, #0x2
  (92, 0x540000a3#32), -- b.lo 0x22b53c <.LBB65_10>
  (96, 0xf9400408#32), -- ldr x8, [x0, #0x8]
  (100, 0x14000004#32), -- b 0x22b540 <.LBB65_11>
  (104, 0xaa1f03e8#32), -- mov x8, xzr
  (108, 0x14000003#32), -- b 0x22b544 <.LBB65_12>
  (112, 0xaa1f03e8#32), -- mov x8, xzr
  (116, 0xaa0903e1#32), -- mov x1, x9
  (120, 0xeb01005f#32), -- cmp x2, x1
  (124, 0xfa0803ff#32), -- ngcs xzr, x8
  (128, 0x54000063#32), -- b.lo 0x22b558 <.Llower_arm_543>
  (132, 0x52800009#32), -- mov w9, #0x0                // =0
  (136, 0x14000002#32), -- b 0x22b55c <.Llower_arm_544>
  (140, 0x52800029#32), -- mov w9, #0x1                // =1
  (144, 0xeb02003f#32), -- cmp x1, x2
  (148, 0xfa1f011f#32), -- sbcs xzr, x8, xzr
  (152, 0x54000062#32), -- b.hs 0x22b570 <.Llower_arm_545>
  (156, 0x2a3f03e0#32), -- mvn w0, wzr
  (160, 0x14000002#32), -- b 0x22b574 <.Llower_arm_546>
  (164, 0x2a0903e0#32), -- mov w0, w9
  (168, 0xd65f03c0#32) -- ret
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

end SszArm.Codec.Linked.NatCmpUsize
