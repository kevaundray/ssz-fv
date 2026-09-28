import SszArm.MeasureScalarByteWrong

namespace SszArm.Measure.Scalar.Bytes.ListSteps

open Result

theorem p2376_effect (s : ArmState) :
    p2376.effect s = write_pstate (AddWithCarry (r (.GPR 20#5) s) (~~~r (.GPR 10#5) s) 1#1).2
      (w .PC (r .PC s + 4#64) s) := by
  change exec_inst (.DPR (.Add_sub_shifted_reg
    { sf := 1, op := 1, S := 1, shift := 0, Rm := 10, imm6 := 0, Rn := 20, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem p2332_effect (s : ArmState) :
    p2332.effect s = write_pstate (AddWithCarry (r (.GPR 11#5) s) (~~~r (.GPR 10#5) s) 1#1).2
      (w .PC (r .PC s + 4#64) s) := by
  change exec_inst (.DPR (.Add_sub_shifted_reg
    { sf := 1, op := 1, S := 1, shift := 0, Rm := 10, imm6 := 0, Rn := 11, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem p2056_effect (s : ArmState) :
    p2056.effect s = write_pstate (AddWithCarry (r (.GPR 20#5) s) (~~~r (.GPR 9#5) s) 1#1).2
      (w .PC (r .PC s + 4#64) s) := by
  change exec_inst (.DPR (.Add_sub_shifted_reg
    { sf := 1, op := 1, S := 1, shift := 0, Rm := 9, imm6 := 0, Rn := 20, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem p2336_effect (s : ArmState) :
    p2336.effect s = w .PC
      (if r (.FLAG .C) s = 1#1 then r .PC s + 4#64 else r .PC s + 12#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 3, o0 := 0, cond := 3 })) s = _
  have choices : r (.FLAG .C) s = 0#1 ∨ r (.FLAG .C) s = 1#1 := by bv_omega
  rcases choices with flag | flag <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, flag]

theorem p2352_effect (s : ArmState) :
    p2352.effect s = w .PC
      (if r (.FLAG .Z) s = 1#1 then r .PC s + 4#64 else r .PC s + 36#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 9, o0 := 0, cond := 1 })) s = _
  have choices : r (.FLAG .Z) s = 0#1 ∨ r (.FLAG .Z) s = 1#1 := by bv_omega
  rcases choices with flag | flag <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, flag]

theorem p2372_effect (s : ArmState) :
    p2372.effect s = w .PC
      (if r (.FLAG .Z) s = 1#1 then r .PC s + 1372#64 else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 343, o0 := 0, cond := 0 })) s = _
  have choices : r (.FLAG .Z) s = 0#1 ∨ r (.FLAG .Z) s = 1#1 := by bv_omega
  rcases choices with flag | flag <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, flag]

theorem p2064_effect (s : ArmState) :
    p2064.effect s = w .PC
      (if r (.FLAG .Z) s = 1#1 then r .PC s + 4#64 else r .PC s + 312#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 78, o0 := 0, cond := 1 })) s = _
  have choices : r (.FLAG .Z) s = 0#1 ∨ r (.FLAG .Z) s = 1#1 := by bv_omega
  rcases choices with flag | flag <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, flag]

theorem p2380_effect (s : ArmState) :
    p2380.effect s = w .PC
      (if r (.FLAG .C) s ≠ 1#1 ∨ r (.FLAG .Z) s = 1#1
       then r .PC s + 1364#64 else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 341, o0 := 0, cond := 9 })) s = _
  have carry : r (.FLAG .C) s = 0#1 ∨ r (.FLAG .C) s = 1#1 := by bv_omega
  have zero : r (.FLAG .Z) s = 0#1 ∨ r (.FLAG .Z) s = 1#1 := by bv_omega
  rcases carry with carry | carry <;> rcases zero with zero | zero <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, carry, zero]

theorem p2356_effect (s : ArmState) :
    p2356.effect s = w .PC
      (if r (.GPR 20#5) s = 0#64 then r .PC s + 1388#64 else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Compare_branch { sf := 1, op := 0, imm19 := 347, Rt := 20 })) s = _
  by_cases zero : r (.GPR 20#5) s = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

theorem p2360_effect (s : ArmState) :
    p2360.effect s = w .PC
      (if r (.GPR 9#5) s = 0#64 then r .PC s + 32#64 else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Compare_branch { sf := 1, op := 0, imm19 := 8, Rt := 9 })) s = _
  by_cases zero : r (.GPR 9#5) s = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

theorem p2388_effect (s : ArmState) :
    p2388.effect s = w .PC
      (if (r (.GPR 10#5) s).setWidth 32 = 0#32 then r .PC s + 1356#64 else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Compare_branch { sf := 0, op := 0, imm19 := 339, Rt := 10 })) s = _
  by_cases zero : (r (.GPR 10#5) s).setWidth 32 = 0#32 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

theorem p2052_effect (s : ArmState) :
    p2052.effect s = w .PC
      (if r (.GPR 20#5) s = 0#64 then r .PC s + 2092#64 else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Compare_branch { sf := 1, op := 0, imm19 := 523, Rt := 20 })) s = _
  by_cases zero : r (.GPR 20#5) s = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

theorem p2384_effect (s : ArmState) :
    p2384.effect s = w .PC (r .PC s + 8#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 2 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem p2344_effect (s : ArmState) :
    p2344.effect s = w .PC (r .PC s + 8#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 2 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem p2068_effect (s : ArmState) :
    p2068.effect s = w .PC (r .PC s + 2076#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 519 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem p2340_effect (s : ArmState) :
    p2340.effect s = w .PC (r .PC s + 4#64) (w (.GPR 10#5) 0#64 s) := by
  change exec_inst (.DPI (.Move_wide_imm
    { sf := 0, opc := 2, hw := 0, imm16 := 0, Rd := 10 })) s = _
  have literal : BitVec.partInstall 0 16 0#16 0#32 = 0#32 := by decide
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, literal, NatExact.gpr_w_pc]

theorem p2348_effect (s : ArmState) :
    p2348.effect s = w .PC (r .PC s + 4#64) (w (.GPR 10#5) 1#64 s) := by
  change exec_inst (.DPI (.Move_wide_imm
    { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 10 })) s = _
  have literal : BitVec.partInstall 0 16 1#16 0#32 = 1#32 := by decide
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, literal, NatExact.gpr_w_pc]

theorem p2048_effect (s : ArmState) :
    p2048.effect s = w .PC (r .PC s + 4#64) (w (.GPR 21#5) (0#64) s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 21 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem p2060_effect (s : ArmState) :
    p2060.effect s = w .PC (r .PC s + 4#64) (w (.GPR 10#5) (r (.GPR 9#5) s) s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 9, imm6 := 0, Rn := 31, Rd := 10 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem p2364_effect (s : ArmState) :
    p2364.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 8#5) s) s) s) :=
  VectorLoadSteps.load2856_effect s

theorem p2368_effect (s : ArmState) :
    p2368.effect s = write_pstate (AddWithCarry (r (.GPR 20#5) s) (~~~r (.GPR 10#5) s) 1#1).2
      (w .PC (r .PC s + 4#64) s) := p2376_effect s

theorem flags_pc (s : ArmState) (flags : PState) (pc : BitVec 64) :
    write_pstate flags (w .PC pc s) = w .PC pc (write_pstate flags s) := by
  simp only [write_pstate, w, write_base_pc, write_base_flag]

theorem unsigned_le (a b : BitVec 64) :
    ((AddWithCarry a (~~~b) 1#1).2.c ≠ 1#1 ∨ (AddWithCarry a (~~~b) 1#1).2.z = 1#1) ↔
      a.toNat ≤ b.toNat := by
  simp only [ne_eq, Udivti3.cmp_carry, Udivti3.cmp_zero]
  have equal : a = b ↔ a.toNat = b.toNat := ⟨congrArg BitVec.toNat, BitVec.eq_of_toNat_eq⟩
  rw [equal]
  omega

end SszArm.Measure.Scalar.Bytes.ListSteps
