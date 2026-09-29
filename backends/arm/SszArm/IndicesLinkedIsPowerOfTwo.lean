import SszArm.CodecLinkedStep

namespace SszArm.Indices.Linked.IsPowerOfTwo

open SszArm.Codec.Linked (WordsAt)

/-- Actual ELF entry address of _ZN13ssz_fv_native3nat3Nat15is_power_of_two17hc06f51fda78fd5d7E. -/
def address : Nat := 2262232

def byteSize : Nat := 248

def chunk0 : List (Nat × BitVec 32) := [
  (0, 0xb40006a0#32), -- cbz x0, 0x2285ac <.LBB60_11>
  (4, 0xd1002008#32), -- sub x8, x0, #0x8
  (8, 0xaa0103e9#32), -- mov x9, x1
  (12, 0xb4000609#32), -- cbz x9, 0x2285a4 <.Llower_arm_494>
  (16, 0xd10043ff#32), -- sub sp, sp, #0x10
  (20, 0xf90003ea#32), -- str x10, [sp]
  (24, 0xaa0903ea#32), -- mov x10, x9
  (28, 0xd37df14a#32), -- lsl x10, x10, #3
  (32, 0x8b0a010a#32), -- add x10, x8, x10
  (36, 0xf940014b#32), -- ldr x11, [x10]
  (40, 0xf94003ea#32), -- ldr x10, [sp]
  (44, 0x910043ff#32), -- add sp, sp, #0x10
  (48, 0xd100052a#32), -- sub x10, x9, #0x1
  (52, 0xaa0a03e9#32), -- mov x9, x10
  (56, 0xb4fffeab#32), -- cbz x11, 0x2284e4 <.LBB60_2>
  (60, 0x2a1f03e8#32), -- mov w8, wzr
  (64, 0xaa1f03e9#32), -- mov x9, xzr
  (68, 0x9100054a#32), -- add x10, x10, #0x1
  (72, 0x14000005#32), -- b 0x228534 <.LBB60_7>
  (76, 0x52800028#32), -- mov w8, #0x1 // =1
  (80, 0x91000529#32), -- add x9, x9, #0x1
  (84, 0xeb09015f#32), -- cmp x10, x9
  (88, 0x540004c0#32), -- b.eq 0x2285c8 <.Llower_arm_496>
  (92, 0xeb01013f#32), -- cmp x9, x1
  (96, 0x54ffff82#32), -- b.hs 0x228528 <.LBB60_6>
  (100, 0xd10043ff#32), -- sub sp, sp, #0x10
  (104, 0xf90003ea#32), -- str x10, [sp]
  (108, 0xaa0903ea#32), -- mov x10, x9
  (112, 0xd37df14a#32), -- lsl x10, x10, #3
  (116, 0x8b0a000a#32), -- add x10, x0, x10
  (120, 0xf940014b#32), -- ldr x11, [x10]
  (124, 0xf94003ea#32), -- ldr x10, [sp]
  (128, 0x910043ff#32), -- add sp, sp, #0x10
  (132, 0xb4fffe6b#32), -- cbz x11, 0x228528 <.LBB60_6>
  (136, 0xd100056c#32), -- sub x12, x11, #0x1
  (140, 0xea0c017f#32), -- tst x11, x12
  (144, 0x54000061#32), -- b.ne 0x228574 <.Llower_arm_491>
  (148, 0x5280000b#32), -- mov w11, #0x0 // =0
  (152, 0x14000002#32), -- b 0x228578 <.Llower_arm_492>
  (156, 0x5280002b#32), -- mov w11, #0x1 // =1
  (160, 0x2a0b0108#32), -- orr w8, w8, w11
  (164, 0xd10043ff#32), -- sub sp, sp, #0x10
  (168, 0xf90003e9#32), -- str x9, [sp]
  (172, 0x12000109#32), -- and w9, w8, #0x1
  (176, 0x34000089#32), -- cbz w9, 0x228598 <.Llower_arm_493>
  (180, 0xf94003e9#32), -- ldr x9, [sp]
  (184, 0x910043ff#32), -- add sp, sp, #0x10
  (188, 0x14000004#32), -- b 0x2285a4 <.Llower_arm_494>
  (192, 0xf94003e9#32), -- ldr x9, [sp]
  (196, 0x910043ff#32), -- add sp, sp, #0x10
  (200, 0x17ffffe1#32), -- b 0x228524 <.LBB60_5>
  (204, 0x120003e0#32), -- and w0, wzr, #0x1
  (208, 0xd65f03c0#32), -- ret
  (212, 0xd1000428#32), -- sub x8, x1, #0x1
  (216, 0xca080029#32), -- eor x9, x1, x8
  (220, 0xeb08013f#32), -- cmp x9, x8
  (224, 0x54000068#32), -- b.hi 0x2285c4 <.Llower_arm_495>
  (228, 0x52800008#32), -- mov w8, #0x0 // =0
  (232, 0x14000002#32), -- b 0x2285c8 <.Llower_arm_496>
  (236, 0x52800028#32), -- mov w8, #0x1 // =1
  (240, 0x12000100#32), -- and w0, w8, #0x1
  (244, 0xd65f03c0#32) -- ret
]

theorem chunk0_decodes :
    chunk0.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

/-- Complete linked function, including every real panic block. -/
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

theorem step_at (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (row : Nat × BitVec 32) (member : row ∈ program)
    (entry : read_pc s = base + BitVec.ofNat 64 row.1)
    (error : read_err s = .None) :
    stepi s = exec_inst (SszArm.Codec.Linked.decoded program all_decode row member) s :=
  SszArm.Codec.Linked.step_at program all_decode s base code row member entry error

end SszArm.Indices.Linked.IsPowerOfTwo
