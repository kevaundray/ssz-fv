import SszArm.MeasureBitVectorScopeHeader

namespace SszArm.Measure.BitVector.Scope

open Result

-- Resolve the literal decoder before simplifying execution. These effects keep
-- the original linked Op witnesses and the order of the load/store pairs.
private theorem scope3416_effect (s : ArmState) :
    p3416.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 11#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s)
        (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 1#5) s) s) s)) := by
  change exec_inst (.LDST (.Reg_pair_signed_offset
    { opc := 2, V := 0, L := 1, imm7 := 0, Rt2 := 11, Rn := 1, Rt := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, NatExact.gpr_w_pc]

private theorem scope3420_effect (s : ArmState) :
    p3420.effect s = w .PC (r .PC s + 4#64)
      (write_mem_bytes 16 (r (.GPR 19#5) s + 32#64)
        (r (.GPR 8#5) s ++ r (.GPR 10#5) s) s) := by
  change exec_inst (.LDST (.Reg_pair_signed_offset
    { opc := 2, V := 0, L := 0, imm7 := 4, Rt2 := 8, Rn := 19, Rt := 10 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.store_w]

private theorem scope3472_effect (s : ArmState) :
    p3472.effect s = w .PC (r .PC s + 4#64) (w (.GPR 8#5) 3#64 s) := by
  change exec_inst (.DPI (.Move_wide_imm
    { sf := 0, opc := 2, hw := 0, imm16 := 3, Rd := 8 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem scope3476_effect (s : ArmState) :
    p3476.effect s = w .PC (r .PC s + 4#64)
      (write_mem_bytes 16 (r (.GPR 19#5) s + 16#64)
        (r (.GPR 11#5) s ++ r (.GPR 9#5) s) s) := by
  change exec_inst (.LDST (.Reg_pair_signed_offset
    { opc := 2, V := 0, L := 0, imm7 := 2, Rt2 := 11, Rn := 19, Rt := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.store_w]

private theorem scope3480_effect (s : ArmState) :
    p3480.effect s = w .PC (r .PC s + 4#64) (w (.GPR 9#5) 1#64 s) := by
  change exec_inst (.DPI (.Move_wide_imm
    { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem scope3524_effect (s : ArmState) :
    p3524.effect s = w .PC (r .PC s + 372#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 93 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

private theorem scope_err_pc (s : ArmState) (pc : BitVec 64) :
    r .ERR (w .PC pc s) = r .ERR s :=
  r_of_w_different (by decide)

private theorem scope_sp_pc (s : ArmState) (pc : BitVec 64) :
    r (.GPR 31#5) (w .PC pc s) = r (.GPR 31#5) s :=
  r_of_w_different (by decide)

@[irreducible] def prefixResult (s : ArmState) (base : BitVec 64) : ArmState :=
  let fields := w (.GPR 11#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s)
    (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 1#5) s) s) s)
  w .PC (base + 3424#64)
    (write_mem_bytes 16 (r (.GPR 19#5) s + 32#64) (r (.GPR 8#5) s ++ r (.GPR 10#5) s) fields)

theorem prefix_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3416#64) : run 2 s = prefixResult s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p3416, p3420] s := by
    change read_err s = .None ∧ read_pc s = base + 3416#64 ∧
      read_err (p3416.effect s) = .None ∧
      read_pc (p3416.effect s) = base + 3420#64 ∧ True
    simp (config := {decide := true, instances := true})
      [scope3416_effect, state_simp_rules, pc, error, BitVec.add_assoc]
  rw [show 2 = [p3416, p3420].length by rfl, runs _ s base code follows]
  change p3420.effect (p3416.effect s) = _
  simp (config := {decide := true, instances := true})
    [prefixResult, scope3416_effect, scope3420_effect, state_simp_rules,
     pc, BitVec.add_assoc, NatExact.gpr_w_pc, NatExact.store_w, w_of_w_shadow]

@[irreducible] def fieldsResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3484#64) (w (.GPR 9#5) 1#64
    (write_mem_bytes 16 (r (.GPR 19#5) s + 16#64) (r (.GPR 11#5) s ++ r (.GPR 9#5) s)
      (w (.GPR 8#5) 3#64 s)))

theorem fields_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3472#64) : run 3 s = fieldsResult s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p3472, p3476, p3480] s := by
    change read_err s = .None ∧ read_pc s = base + 3472#64 ∧
      read_err (p3472.effect s) = .None ∧
      read_pc (p3472.effect s) = base + 3476#64 ∧
      read_err (p3476.effect (p3472.effect s)) = .None ∧
      read_pc (p3476.effect (p3472.effect s)) = base + 3480#64 ∧ True
    simp (config := {decide := true, instances := true})
      [scope3472_effect, scope3476_effect, state_simp_rules,
       pc, error, BitVec.add_assoc]
  rw [show 3 = [p3472, p3476, p3480].length by rfl, runs _ s base code follows]
  change p3480.effect (p3476.effect (p3472.effect s)) = _
  simp (config := {decide := true, instances := true})
    [fieldsResult, scope3472_effect, scope3476_effect, scope3480_effect,
     state_simp_rules, pc, BitVec.add_assoc,
     NatExact.gpr_w_pc, NatExact.store_w, w_of_w_shadow]

theorem suffix_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3524#64) : run 3 s = statusResult s base := by
  let next := w .PC (base + 3896#64) s
  have branchRun : run 1 s = next := by
    have follows : Follows base [p3524] s := ⟨error, pc, trivial⟩
    rw [show 1 = [p3524].length by rfl, runs _ s base code follows]
    change p3524.effect s = next
    change r .PC s = _ at pc
    simp [scope3524_effect, next, pc, BitVec.add_assoc]
  have nextProgram : next.program = s.program := by
    simp [next, state_simp_rules]
  have nextError : read_err next = .None := by
    simpa only [next, read_err, scope_err_pc] using error
  have nextPc : read_pc next = base + 3896#64 := by
    simp [next, state_simp_rules]
  have statusRun : run 2 next = statusResult next base :=
    status_run next base (code.congr nextProgram) nextError nextPc
  rw [show 3 = 1 + 2 by decide, run_plus, branchRun, statusRun]
  simp [next, statusResult, state_simp_rules, NatExact.store_w, w_of_w_shadow]

@[irreducible] def result (s : ArmState) (base : BitVec 64) : ArmState :=
  statusResult (headerResult (fieldsResult (reservedResult (prefixResult s base) base) base) base) base

theorem executes (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3416#64) : run 30 s = result s base := by
  let a := prefixResult s base
  let b := reservedResult a base
  let c := fieldsResult b base
  let d := headerResult c base
  have arun : run 2 s = a := prefix_run s base code error pc
  have ap : a.program = s.program := by simp [a, prefixResult, state_simp_rules]
  have ae : read_err a = .None := by simpa [a, prefixResult, state_simp_rules] using error
  have aa : CheckSPAlignment a := by
    simpa (config := {decide := true}) [a, prefixResult, CheckSPAlignment, state_simp_rules] using aligned
  have brun : run 12 a = b := reserved_run a base (code.congr ap) ae aa
    (by simp [a, prefixResult, state_simp_rules])
  have bp : b.program = s.program := by simp [b, reservedResult, state_simp_rules, ap]
  have be : read_err b = .None := by
    simpa only [b, reservedResult, read_err, scope_err_pc] using
      (Lower.error .wrongReserved a base).trans ae
  have ba : CheckSPAlignment b := by
    simpa only [b, reservedResult, CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
      scope_sp_pc, Lower.sp] using aa
  have crun : run 3 b = c := fields_run b base (code.congr bp) be
    (by simp [b, reservedResult, state_simp_rules])
  have cp : c.program = s.program := by simp [c, fieldsResult, state_simp_rules, bp]
  have ce : read_err c = .None := by
    simpa [c, fieldsResult, state_simp_rules] using be
  have ca : CheckSPAlignment c := by
    simpa (config := {decide := true}) [c, fieldsResult, CheckSPAlignment, state_simp_rules] using ba
  have drun : run 10 c = d := header_run c base (code.congr cp) ce ca
    (by simp [c, fieldsResult, state_simp_rules])
  have dp : d.program = s.program := by
    simp [d, headerResult, headerMemory, headerSaved, state_simp_rules, cp]
  have de : read_err d = .None := by
    simpa [d, headerResult, headerMemory, headerSaved, state_simp_rules] using ce
  have erun : run 3 d = statusResult d base := suffix_run d base (code.congr dp) de
    (by simp [d, headerResult, state_simp_rules])
  rw [show 30 = 2 + 12 + 3 + 10 + 3 by decide, run_plus, run_plus, run_plus, run_plus,
    arun, brun, crun, drun, erun]
  simp only [result, a, b, c, d]

end SszArm.Measure.BitVector.Scope
