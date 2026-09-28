import SszArm.MeasureBitVectorScanGuard
import SszArm.UintShifts

namespace SszArm.Measure.BitVector

open Result

def scanLoadOps : List Op := [p600, p604, p608, p612, p616, p620, p624, p628]

@[irreducible] def scanLoadResult (s : ArmState) (base limb : BitVec 64) : ArmState :=
  w .PC (base + 632#64) (w (.GPR 14#5) limb (NatCompare.saved s 9#5))

-- Reduce the literal decoders before execution, without changing the linked rows.
private theorem scan600_effect (s : ArmState) :
    p600.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem scan604_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p604.effect s = w .PC (r .PC s + 4#64)
      (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned, NatExact.store_w]

private theorem scan608_effect (s : ArmState) :
    p608.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (r (.GPR 13#5) s) s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 13, imm6 := 0, Rn := 31, Rd := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem scan612_effect (s : ArmState) :
    p612.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (r (.GPR 9#5) s <<< 3) s) := by
  change exec_inst (.DPI (.Bitfield
    { sf := 1, opc := 2, N := 1, immr := 61, imms := 60, Rn := 9, Rd := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     UintCodec.uint_lsl3_mask, UintCodec.uint_and_ones, NatExact.gpr_w_pc]

private theorem scan616_effect (s : ArmState) :
    p616.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (r (.GPR 11#5) s + r (.GPR 9#5) s) s) := by
  change exec_inst (.DPR (.Add_sub_shifted_reg
    { sf := 1, op := 0, S := 0, shift := 0, Rm := 9, imm6 := 0, Rn := 11, Rd := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem scan620_effect (s : ArmState) :
    p620.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 14#5) (read_mem_bytes 8 (r (.GPR 9#5) s) s) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 9, Rt := 14 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem scan624_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p624.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned, NatExact.gpr_w_pc]

private theorem scan628_effect (s : ArmState) :
    p628.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

@[irreducible] private def scanSpilled (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 608#64)
    (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) (NatCompare.saved s 9#5))

@[irreducible] private def scanRead (s : ArmState) (base : BitVec 64) : ArmState :=
  let address := r (.GPR 11#5) s + (r (.GPR 13#5) s <<< 3)
  w .PC (base + 624#64)
    (w (.GPR 14#5) (read_mem_bytes 8 address s) (w (.GPR 9#5) address s))

@[irreducible] private def scanReloaded (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 632#64)
    (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s))

private theorem scan_spill_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 600#64) :
    effect [p600, p604] s = scanSpilled s base := by
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have spillAligned : CheckSPAlignment (p600.effect s) := by
    simpa [scan600_effect, CheckSPAlignment, state_simp_rules] using lower
  change r .PC s = _ at pc
  change p604.effect (p600.effect s) = _
  rw [scan604_effect _ spillAligned, scan600_effect]
  simp (config := {decide := true, instances := true})
    [scanSpilled, NatCompare.saved, state_simp_rules, pc, BitVec.add_assoc,
     NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem scan_read_summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 608#64) :
    effect [p608, p612, p616, p620] s = scanRead s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, scanRead, scan608_effect, scan612_effect, scan616_effect, scan620_effect,
     state_simp_rules, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem scan_reload_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 624#64) :
    effect [p624, p628] s = scanReloaded s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, scanReloaded, scan624_effect, scan628_effect,
     state_simp_rules, pc, aligned, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem scan_spill_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 600#64) : run 2 s = scanSpilled s base := by
  have follows : Follows base [p600, p604] s := by
    change r .PC s = _ at pc
    change r .ERR s = _ at error
    simp (config := {decide := true, instances := true})
      [Follows, show p600.offset = 600 by rfl, show p604.offset = 604 by rfl,
       scan600_effect, state_simp_rules, pc, error, BitVec.add_assoc]
  rw [show 2 = [p600, p604].length by rfl, runs _ s base code follows]
  exact scan_spill_summary s base aligned pc

private theorem scan_read_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 608#64) : run 4 s = scanRead s base := by
  have follows : Follows base [p608, p612, p616, p620] s := by
    change r .PC s = _ at pc
    change r .ERR s = _ at error
    simp (config := {decide := true, instances := true})
      [Follows, show p608.offset = 608 by rfl, show p612.offset = 612 by rfl,
       show p616.offset = 616 by rfl, show p620.offset = 620 by rfl,
       scan608_effect, scan612_effect, scan616_effect,
       state_simp_rules, pc, error, BitVec.add_assoc]
  rw [show 4 = [p608, p612, p616, p620].length by rfl, runs _ s base code follows]
  exact scan_read_summary s base pc

private theorem scan_reload_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 624#64) : run 2 s = scanReloaded s base := by
  have follows : Follows base [p624, p628] s := by
    change r .PC s = _ at pc
    change r .ERR s = _ at error
    simp (config := {decide := true, instances := true})
      [Follows, show p624.offset = 624 by rfl, show p628.offset = 628 by rfl,
       scan624_effect, aligned, state_simp_rules, pc, error, BitVec.add_assoc]
  rw [show 2 = [p624, p628].length by rfl, runs _ s base code follows]
  exact scan_reload_summary s base aligned pc

private theorem scan_scratch_restore (s : ArmState) (limb pointer stack : BitVec 64) :
    w (.GPR 31#5) (r (.GPR 31#5) s)
      (w (.GPR 9#5) (r (.GPR 9#5) s)
        (w (.GPR 14#5) limb (w (.GPR 9#5) pointer (w (.GPR 31#5) stack s)))) =
      w (.GPR 14#5) limb s := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases isNine : reg = 9#5 <;> by_cases isFourteen : reg = 14#5 <;>
        by_cases isSP : reg = 31#5 <;> (try subst reg) <;>
        simp_all [NatExact.r_gpr_w, state_simp_rules]
    | PC => simp [state_simp_rules]
    | SFP reg => simp [state_simp_rules]
    | FLAG flag => simp [state_simp_rules]
    | ERR => simp [state_simp_rules]
  · simp [state_simp_rules]
  · intro bytes address; simp [state_simp_rules]

-- The limb is observed after spilling X9, even when its address aliases that spill.
private theorem scan_assemble (s : ArmState) (base limb : BitVec 64)
    (loaded : read_mem_bytes 8 (r (.GPR 11#5) s + (r (.GPR 13#5) s <<< 3))
      (NatCompare.saved s 9#5) = limb)
    (restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 9#5) = r (.GPR 9#5) s) :
    scanReloaded (scanRead (scanSpilled s base) base) base =
      scanLoadResult s base limb := by
  have bridge := congrArg (w .PC (base + 632#64))
    (scan_scratch_restore (NatCompare.saved s 9#5) limb
      (r (.GPR 11#5) s + (r (.GPR 13#5) s <<< 3)) (r (.GPR 31#5) s - 16#64))
  simp only [NatCompare.saved] at loaded restored
  simpa (config := {decide := true})
    [scanReloaded, scanRead, scanSpilled, scanLoadResult, NatCompare.saved,
     state_simp_rules, NatExact.gpr_w_pc, NatExact.store_w, BitVec.sub_add_cancel,
     loaded, restored] using bridge

theorem scan_load_run (s : ArmState) (base limb : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 600#64) (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat)
    (loaded : read_mem_bytes 8 (r (.GPR 11#5) s + (r (.GPR 13#5) s <<< 3))
      (NatCompare.saved s 9#5) = limb) : run 8 s = scanLoadResult s base limb := by
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 9#5) = r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  let a := scanSpilled s base
  let b := scanRead a base
  have ap : a.program = s.program := by
    simp [a, scanSpilled, NatCompare.saved, state_simp_rules]
  have ae : read_err a = .None := by
    simpa [a, scanSpilled, NatCompare.saved, state_simp_rules] using error
  have aa : CheckSPAlignment a := by
    simpa [a, scanSpilled, NatCompare.saved, CheckSPAlignment, state_simp_rules] using lower
  have ac : read_pc a = base + 608#64 := by
    simp [a, scanSpilled, state_simp_rules]
  have ha : run 2 s = a := scan_spill_run s base code error aligned pc
  have hb : run 4 a = b := scan_read_run a base (code.congr ap) ae ac
  have bp : b.program = a.program := by
    simp [b, scanRead, state_simp_rules]
  have be : read_err b = .None := by
    simpa [b, scanRead, state_simp_rules] using ae
  have ba : CheckSPAlignment b := by
    simpa (config := {decide := true})
      [b, scanRead, CheckSPAlignment, state_simp_rules] using aa
  have bc : read_pc b = base + 624#64 := by
    simp [b, scanRead, state_simp_rules]
  have hc : run 2 b = scanReloaded b base :=
    scan_reload_run b base (code.congr (bp.trans ap)) be ba bc
  rw [show 8 = 2 + 4 + 2 by decide, run_plus, run_plus, ha, hb, hc]
  exact scan_assemble s base limb loaded restored

theorem scan_load_frame (s : ArmState) (base limb : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) : ScanFrame s (scanLoadResult s base limb) := by
  have frame := NatCompare.saved_frame s 9#5 stack
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [scanLoadResult, state_simp_rules] using frame.program
  · simpa [scanLoadResult, state_simp_rules] using frame.error
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [scanLoadResult, NatCompare.saved, state_simp_rules]
  · intro reg
    simpa [scanLoadResult, state_simp_rules] using frame.vectors reg
  · intro address outside
    simpa [scanLoadResult, state_simp_rules] using frame.memory address outside

end SszArm.Measure.BitVector
