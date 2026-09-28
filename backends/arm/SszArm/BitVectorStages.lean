import SszArm.BitVectorBlocks

namespace SszArm.BitVector.Stages

open Block

inductive CallPreparation where
  | round | scope | narrow | divisionError | roundTemporary | roundError | scopeError
  deriving DecidableEq

def p492 : Op := ⟨492, 0x910082e0#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 32, Rn := 23, Rd := 0 }), by rfl, by decide⟩
def p496 : Op := ⟨496, 0x91006361#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 24, Rn := 27, Rd := 1 }), by rfl, by decide⟩
def p500 : Op := ⟨500, 0x52800502#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 40, Rd := 2 }), by rfl, by decide⟩
def p3392 : Op := ⟨3392, 0xa9430be1#32,
  .LDST (.Reg_pair_signed_offset { opc := 2, V := 0, L := 1, imm7 := 6, Rt2 := 2, Rn := 31, Rt := 1 }), by rfl, by decide⟩
def p3396 : Op := ⟨3396, 0x910243e0#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 144, Rn := 31, Rd := 0 }), by rfl, by decide⟩
def p3400 : Op := ⟨3400, 0xaa1f03e3#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 3 }), by rfl, by decide⟩
def p3404 : Op := ⟨3404, 0x52800024#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 4 }), by rfl, by decide⟩
def p3408 : Op := ⟨3408, 0xaa1303e5#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 19, imm6 := 0, Rn := 31, Rd := 5 }), by rfl, by decide⟩
def p3424 : Op := ⟨3424, 0x910103e0#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 64, Rn := 31, Rd := 0 }), by rfl, by decide⟩
def p3428 : Op := ⟨3428, 0x910243e1#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 144, Rn := 31, Rd := 1 }), by rfl, by decide⟩
def p3432 : Op := ⟨3432, 0x52800802#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 64, Rd := 2 }), by rfl, by decide⟩
def p3440 : Op := ⟨3440, 0xb940d7f4#32,
  .LDST (.Reg_unsigned_imm { size := 2, V := 0, opc := 1, imm12 := 53, Rn := 31, Rt := 20 }), by rfl, by decide⟩
def p3444 : Op := ⟨3444, 0x910022e0#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 8, Rn := 23, Rd := 0 }), by rfl, by decide⟩
def p3448 : Op := ⟨3448, 0x910103e1#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 64, Rn := 31, Rd := 1 }), by rfl, by decide⟩
def p3452 : Op := ⟨3452, 0x52800802#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 64, Rd := 2 }), by rfl, by decide⟩
def p5948 : Op := ⟨5948, 0x910243e0#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 144, Rn := 31, Rd := 0 }), by rfl, by decide⟩
def p5952 : Op := ⟨5952, 0x9100c3e1#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 48, Rn := 31, Rd := 1 }), by rfl, by decide⟩
def p5956 : Op := ⟨5956, 0xaa1403e2#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 20, imm6 := 0, Rn := 31, Rd := 2 }), by rfl, by decide⟩
def p5972 : Op := ⟨5972, 0x910022e0#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 8, Rn := 23, Rd := 0 }), by rfl, by decide⟩
def p5976 : Op := ⟨5976, 0x910243e1#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 144, Rn := 31, Rd := 1 }), by rfl, by decide⟩
def p5980 : Op := ⟨5980, 0x52800902#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 72, Rd := 2 }), by rfl, by decide⟩
def p6576 : Op := ⟨6576, 0x910243e0#32,
  .DPI (.Add_sub_imm { sf := 1, op := 0, S := 0, sh := 0, imm12 := 144, Rn := 31, Rd := 0 }), by rfl, by decide⟩
def p6580 : Op := ⟨6580, 0xaa1503e1#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 21, imm6 := 0, Rn := 31, Rd := 1 }), by rfl, by decide⟩
def p6584 : Op := ⟨6584, 0xaa1603e2#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 22, imm6 := 0, Rn := 31, Rd := 2 }), by rfl, by decide⟩

def CallPreparation.start : CallPreparation → Nat
  | .round => 3392
  | .scope => 5948
  | .narrow => 6576
  | .divisionError => 492
  | .roundTemporary => 3424
  | .roundError => 3440
  | .scopeError => 5972

def CallPreparation.stop : CallPreparation → Nat
  | .round => 3412
  | .scope => 5960
  | .narrow => 6588
  | .divisionError => 504
  | .roundTemporary => 3436
  | .roundError => 3456
  | .scopeError => 5984

def CallPreparation.ops : CallPreparation → List Op
  | .round => [p3392, p3396, p3400, p3404, p3408]
  | .scope => [p5948, p5952, p5956]
  | .narrow => [p6576, p6580, p6584]
  | .divisionError => [p492, p496, p500]
  | .roundTemporary => [p3424, p3428, p3432]
  | .roundError => [p3440, p3444, p3448, p3452]
  | .scopeError => [p5972, p5976, p5980]

/-- Compact state images for the actual call argument setup. The round case
loads the exact physical expected pair, including arbitrary Large padding. -/
@[irreducible] def CallPreparation.result (phase : CallPreparation)
    (s : ArmState) (base : BitVec 64) : ArmState :=
  let sp := r (.GPR 31#5) s
  let target := r (.GPR 23#5) s
  let body := match phase with
    | .round =>
      w (.GPR 5#5) (r (.GPR 19#5) s) (w (.GPR 4#5) 1#64
        (w (.GPR 3#5) 0#64 (w (.GPR 0#5) (sp + 144#64)
          (w (.GPR 2#5) (read_mem_bytes 8 (sp + 56#64) s)
            (w (.GPR 1#5) (read_mem_bytes 8 (sp + 48#64) s) s)))))
    | .scope =>
      w (.GPR 2#5) (r (.GPR 20#5) s)
        (w (.GPR 1#5) (sp + 48#64) (w (.GPR 0#5) (sp + 144#64) s))
    | .narrow =>
      w (.GPR 2#5) (r (.GPR 22#5) s)
        (w (.GPR 1#5) (r (.GPR 21#5) s) (w (.GPR 0#5) (sp + 144#64) s))
    | .divisionError =>
      w (.GPR 2#5) 40#64 (w (.GPR 1#5) (r (.GPR 27#5) s + 24#64)
        (w (.GPR 0#5) (target + 32#64) s))
    | .roundTemporary =>
      w (.GPR 2#5) 64#64 (w (.GPR 1#5) (sp + 144#64) (w (.GPR 0#5) (sp + 64#64) s))
    | .roundError =>
      w (.GPR 2#5) 64#64 (w (.GPR 1#5) (sp + 64#64)
        (w (.GPR 0#5) (target + 8#64)
          (w (.GPR 20#5) ((read_mem_bytes 4 (sp + 212#64) s).setWidth 64) s)))
    | .scopeError =>
      w (.GPR 2#5) 72#64 (w (.GPR 1#5) (sp + 144#64) (w (.GPR 0#5) (target + 8#64) s))
  w .PC (base + BitVec.ofNat 64 phase.stop) body

private theorem follows (phase : CallPreparation) (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 phase.start) : Follows base phase.ops s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  cases phase <;>
    simp (config := {decide := true, instances := true})
      [Follows, CallPreparation.ops, CallPreparation.start, p492, p496, p500,
       p3392, p3396, p3400, p3404, p3408, p3424, p3428, p3432,
       p3440, p3444, p3448, p3452, p5948, p5952, p5956,
       p5972, p5976, p5980, p6576, p6580, p6584, Op.effect,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, error, pc, BitVec.add_assoc]

private theorem round_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3392#64) :
    effect CallPreparation.round.ops s = CallPreparation.round.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, CallPreparation.ops, CallPreparation.stop, CallPreparation.result,
     p3392, p3396, p3400, p3404, p3408, Op.effect, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     aligned, pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem scope_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 5948#64) :
    effect CallPreparation.scope.ops s = CallPreparation.scope.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, CallPreparation.ops, CallPreparation.stop, CallPreparation.result,
     p5948, p5952, p5956, Op.effect, exec_inst, state_simp_rules, bitvec_rules,
     minimal_theory, aligned, pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem narrow_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6576#64) :
    effect CallPreparation.narrow.ops s = CallPreparation.narrow.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, CallPreparation.ops, CallPreparation.stop, CallPreparation.result,
     p6576, p6580, p6584, Op.effect, exec_inst, state_simp_rules, bitvec_rules,
     minimal_theory, aligned, pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem division_error_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 492#64) :
    effect CallPreparation.divisionError.ops s = CallPreparation.divisionError.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, CallPreparation.ops, CallPreparation.stop, CallPreparation.result,
     p492, p496, p500, Op.effect, exec_inst, state_simp_rules, bitvec_rules,
     minimal_theory, aligned, pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem round_temporary_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3424#64) :
    effect CallPreparation.roundTemporary.ops s = CallPreparation.roundTemporary.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, CallPreparation.ops, CallPreparation.stop, CallPreparation.result,
     p3424, p3428, p3432, Op.effect, exec_inst, state_simp_rules, bitvec_rules,
     minimal_theory, aligned, pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem round_error_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3440#64) :
    effect CallPreparation.roundError.ops s = CallPreparation.roundError.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, CallPreparation.ops, CallPreparation.stop, CallPreparation.result,
     p3440, p3444, p3448, p3452, Op.effect, exec_inst, state_simp_rules, bitvec_rules,
     minimal_theory, aligned, pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem scope_error_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 5972#64) :
    effect CallPreparation.scopeError.ops s = CallPreparation.scopeError.result s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, CallPreparation.ops, CallPreparation.stop, CallPreparation.result,
     p5972, p5976, p5980, Op.effect, exec_inst, state_simp_rules, bitvec_rules,
     minimal_theory, aligned, pc, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem summary (phase : CallPreparation) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 phase.start) :
    effect phase.ops s = phase.result s base := by
  cases phase with
  | round => exact round_summary s base aligned pc
  | scope => exact scope_summary s base aligned pc
  | narrow => exact narrow_summary s base aligned pc
  | divisionError => exact division_error_summary s base aligned pc
  | roundTemporary => exact round_temporary_summary s base aligned pc
  | roundError => exact round_error_summary s base aligned pc
  | scopeError => exact scope_error_summary s base aligned pc

theorem prepare (phase : CallPreparation) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 phase.start) :
    run phase.ops.length s = phase.result s base := by
  rw [runs phase.ops s base code (follows phase s base error aligned pc),
    summary phase s base aligned pc]

end SszArm.BitVector.Stages
