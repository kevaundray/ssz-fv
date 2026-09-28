import SszArm.MeasureBitVectorScopeReserved

namespace SszArm.Measure.BitVector.Scope

open Result

def headerOps : List Op := [p3484, p3488, p3492, p3496, p3500, p3504, p3508, p3512, p3516, p3520]

def headerSaved (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 8#64) (r (.GPR 11#5) s)
    (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 10#5) s) s)

def headerMemory (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 19#5) s + 8#64) 0#64
    (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 9#5) s) (headerSaved s))

@[irreducible] def headerResult (s : ArmState) (base : BitVec 64) : ArmState :=
  let m := headerMemory s
  w .PC (base + 3524#64)
    (w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) m)
      (w (.GPR 11#5) (read_mem_bytes 8 (r (.GPR 31#5) s - 8#64) m) m))

-- Fix each literal decoder to its concrete AST before simplifying any state.
-- The execution witnesses below still use the original 3484..3520 Op rows.
private theorem header3484_instruction : p3484.instruction =
    .DPI (.Add_sub_imm
      { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }) := rfl

private theorem header3488_instruction : p3488.instruction =
    .LDST (.Reg_unsigned_imm
      { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 10 }) := rfl

private theorem header3492_instruction : p3492.instruction =
    .LDST (.Reg_unsigned_imm
      { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 31, Rt := 11 }) := rfl

private theorem header3496_instruction : p3496.instruction =
    .DPI (.Add_sub_imm
      { sf := 1, op := 0, S := 0, sh := 0, imm12 := 0, Rn := 19, Rd := 10 }) := rfl

private theorem header3500_instruction : p3500.instruction =
    .LDST (.Reg_unsigned_imm
      { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 10, Rt := 9 }) := rfl

private theorem header3504_instruction : p3504.instruction =
    .DPI (.Move_wide_imm
      { sf := 1, opc := 2, hw := 0, imm16 := 0, Rd := 11 }) := rfl

private theorem header3508_instruction : p3508.instruction =
    .LDST (.Reg_unsigned_imm
      { size := 3, V := 0, opc := 0, imm12 := 1, Rn := 10, Rt := 11 }) := rfl

private theorem header3512_instruction : p3512.instruction =
    .LDST (.Reg_unsigned_imm
      { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 31, Rt := 11 }) := rfl

private theorem header3516_instruction : p3516.instruction =
    .LDST (.Reg_unsigned_imm
      { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 10 }) := rfl

private theorem header3520_instruction : p3520.instruction =
    .DPI (.Add_sub_imm
      { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 }) := rfl

-- Unlike Result.spillStage, this block saves X10/X11, leaving X9 as payload.
@[irreducible] private def headerSpilled (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3496#64)
    (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) (headerSaved s))

@[irreducible] private def headerPayload (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3512#64)
    (w (.GPR 11#5) 0#64 (w (.GPR 10#5) (r (.GPR 19#5) s)
      (write_mem_bytes 8 (r (.GPR 19#5) s + 8#64) 0#64
        (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 9#5) s) s))))

-- Reload from the post-store memory, including any output/scratch aliases.
@[irreducible] private def headerReloaded (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3524#64)
    (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64)
      (w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s)
        (w (.GPR 11#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s)))

private theorem header_spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3484#64) :
    effect [p3484, p3488, p3492] s = headerSpilled s base := by
  change p3492.effect (p3488.effect (p3484.effect s)) = _
  simp only [Op.effect, header3484_instruction, header3488_instruction, header3492_instruction]
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  simp (config := {decide := true, instances := true})
    [headerSpilled, headerSaved, exec_inst, state_simp_rules, bitvec_rules,
     minimal_theory, pc, lower, address, BitVec.add_assoc, NatExact.store_w,
     NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem header_payload_summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 3496#64) :
    effect [p3496, p3500, p3504, p3508] s = headerPayload s base := by
  change p3508.effect (p3504.effect (p3500.effect (p3496.effect s))) = _
  simp only [Op.effect, header3496_instruction, header3500_instruction,
    header3504_instruction, header3508_instruction]
  change r .PC s = _ at pc
  have zeroMove : BitVec.partInstall 0 16 0#16 0#64 = 0#64 := by decide
  simp (config := {decide := true, instances := true})
    [headerPayload, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     zeroMove, pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem header_reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3512#64) :
    effect [p3512, p3516, p3520] s = headerReloaded s base := by
  change p3520.effect (p3516.effect (p3512.effect s)) = _
  simp only [Op.effect, header3512_instruction, header3516_instruction, header3520_instruction]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [headerReloaded, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem header_spill_follows (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3484#64) : Follows base [p3484, p3488, p3492] s := by
  let a := p3484.effect s
  let b := p3488.effect a
  change read_err s = .None ∧ read_pc s = base + 3484#64 ∧
    read_err a = .None ∧ read_pc a = base + 3488#64 ∧
    read_err b = .None ∧ read_pc b = base + 3492#64 ∧ True
  simp only [a, b, Op.effect, header3484_instruction, header3488_instruction]
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, lower, error,
     pc, BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc]

private theorem header_payload_follows (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (pc : read_pc s = base + 3496#64) :
    Follows base [p3496, p3500, p3504, p3508] s := by
  let a := p3496.effect s
  let b := p3500.effect a
  let c := p3504.effect b
  change read_err s = .None ∧ read_pc s = base + 3496#64 ∧
    read_err a = .None ∧ read_pc a = base + 3500#64 ∧
    read_err b = .None ∧ read_pc b = base + 3504#64 ∧
    read_err c = .None ∧ read_pc c = base + 3508#64 ∧ True
  simp only [a, b, c, Op.effect, header3496_instruction, header3500_instruction,
    header3504_instruction]
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, error, pc,
     BitVec.add_assoc, NatExact.store_w, NatExact.gpr_w_pc]

private theorem header_reload_follows (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3512#64) : Follows base [p3512, p3516, p3520] s := by
  let a := p3512.effect s
  let b := p3516.effect a
  change read_err s = .None ∧ read_pc s = base + 3512#64 ∧
    read_err a = .None ∧ read_pc a = base + 3516#64 ∧
    read_err b = .None ∧ read_pc b = base + 3520#64 ∧ True
  simp only [a, b, Op.effect, header3512_instruction, header3516_instruction]
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned, error,
     pc, BitVec.add_assoc, NatExact.gpr_w_pc]

private theorem header_spill_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3484#64) : run 3 s = headerSpilled s base := by
  rw [show 3 = [p3484, p3488, p3492].length by rfl,
    runs _ s base code (header_spill_follows s base error aligned pc)]
  exact header_spill_summary s base aligned pc

private theorem header_payload_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3496#64) : run 4 s = headerPayload s base := by
  rw [show 4 = [p3496, p3500, p3504, p3508].length by rfl,
    runs _ s base code (header_payload_follows s base error pc)]
  exact header_payload_summary s base pc

private theorem header_reload_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3512#64) : run 3 s = headerReloaded s base := by
  rw [show 3 = [p3512, p3516, p3520].length by rfl,
    runs _ s base code (header_reload_follows s base error aligned pc)]
  exact header_reload_summary s base aligned pc

private theorem header_scratch_restore (s : ArmState) (low high pointer stack : BitVec 64) :
    w (.GPR 31#5) (r (.GPR 31#5) s)
      (w (.GPR 10#5) low (w (.GPR 11#5) high
        (w (.GPR 11#5) 0#64 (w (.GPR 10#5) pointer (w (.GPR 31#5) stack s))))) =
      w (.GPR 10#5) low (w (.GPR 11#5) high s) := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases isTen : reg = 10#5 <;> by_cases isEleven : reg = 11#5 <;>
        by_cases isSP : reg = 31#5 <;> (try subst reg) <;>
        simp_all [NatExact.r_gpr_w, state_simp_rules]
    | PC => simp [state_simp_rules]
    | SFP reg => simp [state_simp_rules]
    | FLAG flag => simp [state_simp_rules]
    | ERR => simp [state_simp_rules]
  · simp [state_simp_rules]
  · intro bytes address; simp [state_simp_rules]

private theorem header_stages_assemble (s : ArmState) (base : BitVec 64) :
    headerReloaded (headerPayload (headerSpilled s base) base) base = headerResult s base := by
  have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have restored := header_scratch_restore (headerMemory s)
    (read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (headerMemory s))
    (read_mem_bytes 8 (r (.GPR 31#5) s - 8#64) (headerMemory s))
    (r (.GPR 19#5) s) (r (.GPR 31#5) s - 16#64)
  have bridge := congrArg (w .PC (base + 3524#64)) restored
  simpa (config := {decide := true})
    [headerReloaded, headerPayload, headerSpilled, headerResult, headerMemory, headerSaved,
     state_simp_rules, NatExact.store_w, NatExact.gpr_w_pc, BitVec.sub_add_cancel,
     address] using bridge

theorem header_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3484#64) : run 10 s = headerResult s base := by
  let a := headerSpilled s base
  let b := headerPayload a base
  have ap : a.program = s.program := by
    simp [a, headerSpilled, headerSaved, state_simp_rules]
  have ae : read_err a = .None := by
    simpa [a, headerSpilled, headerSaved, state_simp_rules] using error
  have aa : CheckSPAlignment a := by
    have stack := BoolCodec.stack_aligned s aligned
    change Aligned (r (.GPR 31#5) s) 4 at stack
    have lower := BoolCodec.aligned_sub16 _ stack
    simpa [a, headerSpilled, headerSaved, CheckSPAlignment, state_simp_rules] using lower
  have ac : read_pc a = base + 3496#64 := by
    simp [a, headerSpilled, state_simp_rules]
  have ha : run 3 s = a := header_spill_run s base code error aligned pc
  have hb : run 4 a = b := header_payload_run a base (code.congr ap) ae ac
  have bp : b.program = a.program := by
    simp [b, headerPayload, state_simp_rules]
  have be : read_err b = .None := by
    simpa [b, headerPayload, state_simp_rules] using ae
  have ba : CheckSPAlignment b := by
    simpa (config := {decide := true})
      [b, headerPayload, CheckSPAlignment, state_simp_rules] using aa
  have bc : read_pc b = base + 3512#64 := by
    simp [b, headerPayload, state_simp_rules]
  have hc : run 3 b = headerReloaded b base :=
    header_reload_run b base (code.congr (bp.trans ap)) be ba bc
  rw [show 10 = 3 + 4 + 3 by decide, run_plus, run_plus, ha, hb, hc]
  exact header_stages_assemble s base

end SszArm.Measure.BitVector.Scope
