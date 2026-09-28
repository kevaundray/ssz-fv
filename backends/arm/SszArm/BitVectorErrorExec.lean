import SszArm.BitVectorBlocks

namespace SszArm.BitVector.ErrorTail

open Block

inductive Tail where
  | division | round | tag | padding
  deriving DecidableEq

def p508 : Op := ⟨508, 0xa94423e9#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 8, Rt2 := 8, Rn := 31, Rt := 9 }), by rfl, by decide⟩
def p512 : Op := ⟨512, 0xa90166e8#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 2, Rt2 := 25, Rn := 23, Rt := 8 }), by rfl, by decide⟩
def p516 : Op := ⟨516, 0xb940d7e8#32,
  .LDST (.Reg_unsigned_imm { size := 2, V := 0, opc := 1, imm12 := 53, Rn := 31, Rt := 8 }), by rfl, by decide⟩
def p520 : Op := ⟨520, 0x290922fa#32,
  .LDST (.Reg_pair_signed_offset { opc := 0, V := 0, L := 0, imm7 := 18, Rt2 := 8, Rn := 23, Rt := 26 }), by rfl, by decide⟩
def p524 : Op := ⟨524, 0x52800028#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 8 }), by rfl, by decide⟩
def p528 : Op := ⟨528, 0xa90026e8#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 0, Rt2 := 9, Rn := 23, Rt := 8 }), by rfl, by decide⟩
def p532 : Op := ⟨532, 0x1400041a#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 1050 }), by rfl, by decide⟩
def p3460 : Op := ⟨3460, 0x290952f3#32,
  .LDST (.Reg_pair_signed_offset { opc := 0, V := 0, L := 0, imm7 := 18, Rt2 := 20, Rn := 23, Rt := 19 }), by rfl, by decide⟩
def p3464 : Op := ⟨3464, 0x14000277#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 631 }), by rfl, by decide⟩
def p5988 : Op := ⟨5988, 0x52800028#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 8 }), by rfl, by decide⟩
def p5992 : Op := ⟨5992, 0xf90002e8#32,
  .LDST (.Reg_unsigned_imm { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 23, Rt := 8 }), by rfl, by decide⟩
def p5996 : Op := ⟨5996, 0x17fffec4#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 0x3fffec4 }), by rfl, by decide⟩
def p8224 : Op := ⟨8224, 0x52800029#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 9 }), by rfl, by decide⟩
def p8228 : Op := ⟨8228, 0xb9004ae8#32,
  .LDST (.Reg_unsigned_imm { size := 2, V := 0, opc := 0, imm12 := 18, Rn := 23, Rt := 8 }), by rfl, by decide⟩
def p8232 : Op := ⟨8232, 0xa90026e9#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 0, Rt2 := 9, Rn := 23, Rt := 9 }), by rfl, by decide⟩
def p8236 : Op := ⟨8236, 0x17fffc94#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 0x3fffc94 }), by rfl, by decide⟩

def Tail.ops : Tail → List Op
  | .division => [p508, p512, p516, p520, p524, p528, p532]
  | .round => [p3460, p3464]
  | .tag => [p5988, p5992, p5996]
  | .padding => [p8224, p8228, p8232, p8236]

def Tail.start : Tail → Nat
  | .division => 508
  | .round => 3460
  | .tag => 5988
  | .padding => 8224

def Tail.stop : Tail → Nat
  | .round => 5988
  | _ => 4732

/-- This summary retains the physical fourth status-padding byte, including the
otherwise unobserved read at SP+212. It does not assume it is initialized. -/
@[irreducible] def Tail.result (phase : Tail) (s : ArmState) (base : BitVec 64) : ArmState :=
  let target := r (.GPR 23#5) s
  let sp := r (.GPR 31#5) s
  let t := match phase with
    | .division =>
      let first := write_mem_bytes 16 (target + 16#64)
        ((r (.GPR 25#5) s) ++ read_mem_bytes 8 (sp + 72#64) s) s
      let padding := read_mem_bytes 4 (sp + 212#64) first
      let status := write_mem_bytes 8 (target + 72#64)
        (padding ++ (r (.GPR 26#5) s).setWidth 32) first
      let complete := write_mem_bytes 16 target
        (read_mem_bytes 8 (sp + 64#64) s ++ 1#64) status
      w (.GPR 8#5) 1#64 (w (.GPR 9#5) (read_mem_bytes 8 (sp + 64#64) s) complete)
    | .round =>
      write_mem_bytes 8 (target + 72#64)
        ((r (.GPR 20#5) s).setWidth 32 ++ (r (.GPR 19#5) s).setWidth 32) s
    | .tag => w (.GPR 8#5) 1#64 (write_mem_bytes 8 target 1#64 s)
    | .padding => w (.GPR 9#5) 1#64
        (write_mem_bytes 16 target (1#64 ++ 1#64)
          (write_mem_bytes 4 (target + 72#64) ((r (.GPR 8#5) s).setWidth 32) s))
  w .PC (base + BitVec.ofNat 64 phase.stop) t

private theorem follows (phase : Tail) (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 phase.start) : Follows base phase.ops s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  cases phase <;>
    simp (config := {decide := true, instances := true})
      [Follows, Tail.ops, Tail.start, p508, p512, p516, p520, p524, p528, p532,
       p3460, p3464, p5988, p5992, p5996, p8224, p8228, p8232, p8236,
       Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, error, pc, BitVec.add_assoc]

private theorem division_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 508#64) :
    effect Tail.division.ops s = Tail.division.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, Tail.ops, Tail.stop, Tail.result, p508, p512, p516, p520, p524, p528, p532,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc]
  simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes, Memory.write_mem_bytes_eq_mem_write_bytes,
    w, write_base_pc, write_base_gpr, store_write_over_write_shadow]

private theorem round_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3460#64) :
    effect Tail.round.ops s = Tail.round.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, Tail.ops, Tail.stop, Tail.result, p3460, p3464, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, pc, BitVec.add_assoc]

private theorem tag_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 5988#64) :
    effect Tail.tag.ops s = Tail.tag.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, Tail.ops, Tail.stop, Tail.result, p5988, p5992, p5996, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, pc, BitVec.add_assoc]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem padding_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 8224#64) :
    effect Tail.padding.ops s = Tail.padding.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, Tail.ops, Tail.stop, Tail.result, p8224, p8228, p8232, p8236,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned, pc, BitVec.add_assoc]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

theorem executes (phase : Tail) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 phase.start) :
    run phase.ops.length s = phase.result s base := by
  rw [runs phase.ops s base code (follows phase s base error aligned pc)]
  cases phase with
  | division => exact division_summary s base aligned pc
  | round => exact round_summary s base aligned pc
  | tag => exact tag_summary s base aligned pc
  | padding => exact padding_summary s base aligned pc

end SszArm.BitVector.ErrorTail
