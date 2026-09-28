import SszArm.BitVectorBlocks

namespace SszArm.BitVector.ExpectedStage

open Block

inductive Stage where
  | division | rounding | rounded | scope
  deriving DecidableEq

def p3380 : Op := ⟨3380, 0xa94427e8#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 8, Rt2 := 9, Rn := 31, Rt := 8 }), by rfl, by decide⟩
def p3384 : Op := ⟨3384, 0xa90327e8#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 6, Rt2 := 9, Rn := 31, Rt := 8 }), by rfl, by decide⟩
def p3388 : Op := ⟨3388, 0xb4005019#32,
  .BR (.Compare_branch { sf := 1, op := 0, imm19 := 640, Rt := 25 }), by rfl, by decide⟩
def p3416 : Op := ⟨3416, 0xb940d3f3#32,
  .LDST (.Reg_unsigned_imm { size := 2, V := 0, opc := 1, imm12 := 52, Rn := 31, Rt := 19 }), by rfl, by decide⟩
def p3420 : Op := ⟨3420, 0x34004ed3#32,
  .BR (.Compare_branch { sf := 0, op := 0, imm19 := 630, Rt := 19 }), by rfl, by decide⟩
def p5940 : Op := ⟨5940, 0xa94927e8#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 18, Rt2 := 9, Rn := 31, Rt := 8 }), by rfl, by decide⟩
def p5944 : Op := ⟨5944, 0xa90327e8#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 0, imm7 := 6, Rt2 := 9, Rn := 31, Rt := 8 }), by rfl, by decide⟩
def p5964 : Op := ⟨5964, 0xb940d3e8#32,
  .LDST (.Reg_unsigned_imm { size := 2, V := 0, opc := 1, imm12 := 52, Rn := 31, Rt := 8 }), by rfl, by decide⟩
def p5968 : Op := ⟨5968, 0x34000108#32,
  .BR (.Compare_branch { sf := 0, op := 0, imm19 := 8, Rt := 8 }), by rfl, by decide⟩

def Stage.ops : Stage → List Op
  | .division => [p3380, p3384, p3388]
  | .rounding => [p3416, p3420]
  | .rounded => [p5940, p5944]
  | .scope => [p5964, p5968]

def Stage.start : Stage → Nat
  | .division => 3380
  | .rounding => 3416
  | .rounded => 5940
  | .scope => 5964

@[irreducible] def Stage.result (stage : Stage) (s : ArmState) (base : BitVec 64) : ArmState :=
  let sp := r (.GPR 31#5) s
  let status := read_mem_bytes 4 (sp + 208#64) s
  match stage with
  | .division =>
    let pointer := read_mem_bytes 8 (sp + 64#64) s
    let payload := read_mem_bytes 8 (sp + 72#64) s
    w .PC (if r (.GPR 25#5) s = 0 then base + 5948#64 else base + 3392#64)
      (w (.GPR 9#5) payload (w (.GPR 8#5) pointer
        (write_mem_bytes 16 (sp + 48#64) (payload ++ pointer) s)))
  | .rounding =>
    w .PC (if status = 0 then base + 5940#64 else base + 3424#64)
      (w (.GPR 19#5) (status.setWidth 64) s)
  | .rounded =>
    let pointer := read_mem_bytes 8 (sp + 144#64) s
    let payload := read_mem_bytes 8 (sp + 152#64) s
    w .PC (base + 5948#64) (w (.GPR 9#5) payload (w (.GPR 8#5) pointer
      (write_mem_bytes 16 (sp + 48#64) (payload ++ pointer) s)))
  | .scope =>
    w .PC (if status = 0 then base + 6000#64 else base + 5972#64)
      (w (.GPR 8#5) (status.setWidth 64) s)

private theorem follows (stage : Stage) (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) : Follows base stage.ops s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  cases stage <;>
    simp (config := {decide := true, instances := true})
      [Follows, Stage.ops, Stage.start, p3380, p3384, p3388, p3416, p3420,
       p5940, p5944, p5964, p5968, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, BoolCodec.pair_read_low,
       BoolCodec.pair_read_high, aligned, error, pc, BitVec.add_assoc]

private theorem division_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3380#64) :
    effect Stage.division.ops s = Stage.division.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, Stage.ops, Stage.result, p3380, p3384, p3388, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BoolCodec.pair_read_low,
     BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem rounding_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3416#64) :
    effect Stage.rounding.ops s = Stage.rounding.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, Stage.ops, Stage.result, p3416, p3420, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, pc, BitVec.add_assoc]

private theorem rounded_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 5940#64) :
    effect Stage.rounded.ops s = Stage.rounded.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, Stage.ops, Stage.result, p5940, p5944, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BoolCodec.pair_read_low,
     BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem scope_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 5964#64) :
    effect Stage.scope.ops s = Stage.scope.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, Stage.ops, Stage.result, p5964, p5968, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, pc, BitVec.add_assoc]

private theorem summary (stage : Stage) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) :
    effect stage.ops s = stage.result s base := by
  cases stage with
  | division => exact division_summary s base aligned pc
  | rounding => exact rounding_summary s base aligned pc
  | rounded => exact rounded_summary s base aligned pc
  | scope => exact scope_summary s base aligned pc

theorem executes (stage : Stage) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 stage.start) :
    run stage.ops.length s = stage.result s base := by
  rw [runs stage.ops s base code (follows stage s base error aligned pc),
    summary stage s base aligned pc]

end SszArm.BitVector.ExpectedStage
