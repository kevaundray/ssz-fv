import SszArm.MeasureResultBlock
import SszArm.MeasureHelpersMemcpy

namespace SszArm.Measure.Bits.Propagation

open Result (Op Follows effect runs)

def p1916 : Op := ⟨1916, 0xa947d3f5#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 15, Rt2 := 20, Rn := 31, Rt := 21 }),
  by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1920 : Op := ⟨1920, 0xb940bbf6#32,
  .LDST (.Reg_unsigned_imm { size := 2, V := 0, opc := 1, imm12 := 46, Rn := 31, Rt := 22 }),
  by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1924 : Op := ⟨1924, 0x34004576#32,
  .BR (.Compare_branch { sf := 0, op := 0, imm19 := 555, Rt := 22 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1928 : Op := ⟨1928, 0x91004260#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 19, Rd := 0 }),
  by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1932 : Op := ⟨1932, 0x910042e1#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 23, Rd := 1 }),
  by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1936 : Op := ⟨1936, 0x52800602#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 48, Rd := 2 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1944 : Op := ⟨1944, 0xb940bfe8#32,
  .LDST (.Reg_unsigned_imm { size := 2, V := 0, opc := 1, imm12 := 47, Rn := 31, Rt := 8 }),
  by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1948 : Op := ⟨1948, 0xa9005275#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 0, Rt2 := 20, Rn := 19, Rt := 21 }),
  by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1952 : Op := ⟨1952, 0x29082276#32,
  .LDST (.Reg_pair_signed_offset { opc := 0, V := 0, L := 0, imm7 := 16, Rt2 := 8, Rn := 19, Rt := 22 }),
  by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p1956 : Op := ⟨1956, 0x1400021c#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 540 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩

-- Only these single-instruction lemmas unfold the interpreter. Stage proofs
-- compose their bounded effects, retaining each original decoder/image witness.
private theorem p1916_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p1916.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 20#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 128#64) s)
        (w (.GPR 21#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 120#64) s) s)) := by
  change exec_inst (.LDST (.Reg_pair_signed_offset
    { opc := 2, V := 0, L := 1, imm7 := 15, Rt2 := 20, Rn := 31, Rt := 21 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned,
      BoolCodec.pair_read_low, BoolCodec.pair_read_high, BitVec.add_assoc,
      NatExact.gpr_w_pc]

private theorem p1920_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p1920.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 22#5)
        ((read_mem_bytes 4 (r (.GPR 31#5) s + 184#64) s).setWidth 64) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 2, V := 0, opc := 1, imm12 := 46, Rn := 31, Rt := 22 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned,
      NatExact.gpr_w_pc]

private theorem p1924_effect (s : ArmState) :
    p1924.effect s = w .PC
      (if (r (.GPR 22#5) s).setWidth 32 = 0#32 then r .PC s + 2220#64
        else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Compare_branch
    { sf := 0, op := 0, imm19 := 555, Rt := 22 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

private theorem p1928_effect (s : ArmState) :
    p1928.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 0#5) (r (.GPR 19#5) s + 16#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 19, Rd := 0 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem p1932_effect (s : ArmState) :
    p1932.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 1#5) (r (.GPR 23#5) s + 16#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 23, Rd := 1 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem p1936_effect (s : ArmState) :
    p1936.effect s = w .PC (r .PC s + 4#64) (w (.GPR 2#5) 48#64 s) := by
  change exec_inst (.DPI (.Move_wide_imm
    { sf := 0, opc := 2, hw := 0, imm16 := 48, Rd := 2 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem p1944_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p1944.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 8#5)
        ((read_mem_bytes 4 (r (.GPR 31#5) s + 188#64) s).setWidth 64) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 2, V := 0, opc := 1, imm12 := 47, Rn := 31, Rt := 8 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned,
      NatExact.gpr_w_pc]

private theorem p1948_effect (s : ArmState) :
    p1948.effect s = w .PC (r .PC s + 4#64)
      (write_mem_bytes 16 (r (.GPR 19#5) s)
        (r (.GPR 20#5) s ++ r (.GPR 21#5) s) s) := by
  change exec_inst (.LDST (.Reg_pair_signed_offset
    { opc := 2, V := 0, L := 0, imm7 := 0, Rt2 := 20, Rn := 19, Rt := 21 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.store_w]

private theorem p1952_effect (s : ArmState) :
    p1952.effect s = w .PC (r .PC s + 4#64)
      (write_mem_bytes 8 (r (.GPR 19#5) s + 64#64)
        ((r (.GPR 8#5) s).setWidth 32 ++ (r (.GPR 22#5) s).setWidth 32) s) := by
  change exec_inst (.LDST (.Reg_pair_signed_offset
    { opc := 0, V := 0, L := 0, imm7 := 16, Rt2 := 8, Rn := 19, Rt := 22 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.store_w]

private theorem p1956_effect (s : ArmState) :
    p1956.effect s = w .PC (r .PC s + 2160#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 540 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

private theorem effect_three (first second third : Op) (s : ArmState) :
    effect [first, second, third] s =
      third.effect (second.effect (first.effect s)) := rfl

private theorem effect_four (first second third fourth : Op) (s : ArmState) :
    effect [first, second, third, fourth] s =
      fourth.effect (third.effect (second.effect (first.effect s))) := rfl

inductive Stage where
  | returned | prepare | finish
  deriving DecidableEq

def Stage.ops : Stage → List Op
  | .returned => [p1916, p1920, p1924]
  | .prepare => [p1928, p1932, p1936]
  | .finish => [p1944, p1948, p1952, p1956]

def Stage.start : Stage → Nat
  | .returned => 1916 | .prepare => 1928 | .finish => 1944

@[irreducible] def Stage.result (stage : Stage) (s : ArmState) (base : BitVec 64) : ArmState :=
  let sp := r (.GPR 31#5) s
  match stage with
  | .returned =>
    let first := read_mem_bytes 8 (sp + 120#64) s
    let second := read_mem_bytes 8 (sp + 128#64) s
    let status := read_mem_bytes 4 (sp + 184#64) s
    w .PC (if status = 0#32 then base + 4144#64 else base + 1928#64)
      (w (.GPR 22#5) (status.setWidth 64)
        (w (.GPR 20#5) second (w (.GPR 21#5) first s)))
  | .prepare =>
    w .PC (base + 1940#64) (w (.GPR 2#5) 48#64
      (w (.GPR 1#5) (r (.GPR 23#5) s + 16#64)
        (w (.GPR 0#5) (r (.GPR 19#5) s + 16#64) s)))
  | .finish =>
    let padding := read_mem_bytes 4 (sp + 188#64) s
    w .PC (base + 4116#64) (w (.GPR 8#5) (padding.setWidth 64)
      (write_mem_bytes 8 (r (.GPR 19#5) s + 64#64)
        (padding ++ (r (.GPR 22#5) s).setWidth 32)
        (write_mem_bytes 16 (r (.GPR 19#5) s)
          (r (.GPR 20#5) s ++ r (.GPR 21#5) s) s)))

private theorem follows (stage : Stage) (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) : Follows base stage.ops s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  cases stage <;>
    simp (config := {decide := true, instances := true})
      [Follows, Stage.ops, Stage.start,
        show p1916.offset = 1916 by rfl, show p1920.offset = 1920 by rfl,
        show p1924.offset = 1924 by rfl, show p1928.offset = 1928 by rfl,
        show p1932.offset = 1932 by rfl, show p1936.offset = 1936 by rfl,
        show p1944.offset = 1944 by rfl, show p1948.offset = 1948 by rfl,
        show p1952.offset = 1952 by rfl, show p1956.offset = 1956 by rfl,
        p1916_effect, p1920_effect, p1928_effect, p1932_effect,
        p1944_effect, p1948_effect, p1952_effect,
        state_simp_rules, aligned, error, pc, BitVec.add_assoc]

private theorem returned_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 1916#64) :
    effect Stage.returned.ops s = Stage.returned.result s base := by
  change r .PC s = _ at pc
  rw [Stage.ops, effect_three]
  simp (config := {decide := true, instances := true})
    [Stage.result, p1916_effect, p1920_effect, p1924_effect,
      state_simp_rules, bitvec_rules, aligned, pc, BitVec.add_assoc,
      NatExact.gpr_w_pc]

private theorem prepare_summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 1928#64) :
    effect Stage.prepare.ops s = Stage.prepare.result s base := by
  change r .PC s = _ at pc
  rw [Stage.ops, effect_three]
  simp (config := {decide := true, instances := true})
    [Stage.result, p1928_effect, p1932_effect, p1936_effect,
      state_simp_rules, pc, BitVec.add_assoc, NatExact.gpr_w_pc]

private theorem finish_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 1944#64) :
    effect Stage.finish.ops s = Stage.finish.result s base := by
  change r .PC s = _ at pc
  rw [Stage.ops, effect_four]
  simp (config := {decide := true, instances := true})
    [Stage.result, p1944_effect, p1948_effect, p1952_effect, p1956_effect,
      state_simp_rules, bitvec_rules, aligned, pc, BitVec.add_assoc,
      NatExact.gpr_w_pc, NatExact.store_w] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

theorem executes (stage : Stage) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) :
    run stage.ops.length s = stage.result s base := by
  rw [runs stage.ops s base code (follows stage s base error aligned pc)]
  cases stage with
  | returned => exact returned_summary s base aligned pc
  | prepare => exact prepare_summary s base pc
  | finish => exact finish_summary s base aligned pc

end SszArm.Measure.Bits.Propagation
