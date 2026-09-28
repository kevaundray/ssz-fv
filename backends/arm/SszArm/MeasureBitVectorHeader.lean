import SszArm.MeasureBitVectorGate

namespace SszArm.Measure.BitVector

open Result

def headerOps : List Op := [p576, p580, p584]

@[irreducible] def header (s : ArmState) : ArmState := effect headerOps s

-- Pin each literal decoder before exposing execution to the state simplifier.
private theorem inputHeader576_instruction : p576.instruction =
    .LDST (.Reg_pair_pre_indexed
      { opc := 2, V := 0, L := 1, imm7 := 1, Rt2 := 10, Rn := 1, Rt := 11 }) := rfl

private theorem inputHeader580_instruction : p580.instruction =
    .LDST (.Reg_pair_signed_offset
      { opc := 2, V := 0, L := 1, imm7 := 4, Rt2 := 9, Rn := 21, Rt := 8 }) := rfl

private theorem inputHeader584_instruction : p584.instruction =
    .BR (.Compare_branch { sf := 1, op := 0, imm19 := 671, Rt := 11 }) := rfl

private theorem inputHeader576_effect (s : ArmState) :
    p576.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 1#5) (r (.GPR 1#5) s + 8#64)
        (w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s)
          (w (.GPR 11#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s) s))) := by
  simp only [Op.effect, inputHeader576_instruction]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, BitVec.add_assoc]

private theorem inputHeader580_effect (s : ArmState) :
    p580.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 21#5) s + 40#64) s)
        (w (.GPR 8#5) (read_mem_bytes 8 (r (.GPR 21#5) s + 32#64) s) s)) := by
  simp only [Op.effect, inputHeader580_instruction]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, BitVec.add_assoc]

-- Both LDPs read the original memory; only the first writes its base register.
@[irreducible] private def inputHeaderRead (s : ArmState) : ArmState :=
  w .PC (r .PC s + 8#64)
    (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 21#5) s + 40#64) s)
      (w (.GPR 8#5) (read_mem_bytes 8 (r (.GPR 21#5) s + 32#64) s)
        (w (.GPR 1#5) (r (.GPR 1#5) s + 8#64)
          (w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s)
            (w (.GPR 11#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s) s)))))

@[irreducible] private def inputHeaderBranched (s : ArmState) : ArmState :=
  w .PC (if r (.GPR 11#5) s = 0#64 then r .PC s + 2684#64 else r .PC s + 4#64) s

private theorem inputHeader_read_summary (s : ArmState) :
    p580.effect (p576.effect s) = inputHeaderRead s := by
  rw [inputHeader580_effect, inputHeader576_effect]
  simp (config := {decide := true, instances := true})
    [inputHeaderRead, state_simp_rules, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem inputHeader_branch_summary (s : ArmState) :
    p584.effect s = inputHeaderBranched s := by
  simp only [Op.effect, inputHeader584_instruction]
  simp (config := {decide := true, instances := true})
    [inputHeaderBranched, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

private theorem inputHeader_summary (s : ArmState) :
    header s = inputHeaderBranched (inputHeaderRead s) := by
  unfold header
  change p584.effect (p580.effect (p576.effect s)) = _
  rw [inputHeader_read_summary, inputHeader_branch_summary]

theorem header_run (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (error : read_err s = .None) (pc : read_pc s = base + 576#64) : run 3 s = header s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base headerOps s := by
    change read_err s = .None ∧ read_pc s = base + 576#64 ∧
      read_err (p576.effect s) = .None ∧
      read_pc (p576.effect s) = base + 580#64 ∧
      read_err (p580.effect (p576.effect s)) = .None ∧
      read_pc (p580.effect (p576.effect s)) = base + 584#64 ∧ True
    simp only [inputHeader_read_summary]
    simp (config := {decide := true, instances := true})
      [inputHeader576_effect, inputHeaderRead, state_simp_rules, error, pc, BitVec.add_assoc]
  rw [show 3 = headerOps.length by rfl, runs _ s base code follows]
  unfold header
  rfl

@[simp] theorem header_program (s : ArmState) : (header s).program = s.program := by
  rw [inputHeader_summary]
  simp [inputHeaderBranched, inputHeaderRead, state_simp_rules]

@[simp] theorem header_error (s : ArmState) : read_err (header s) = read_err s := by
  rw [inputHeader_summary]
  simp [inputHeaderBranched, inputHeaderRead, state_simp_rules]

@[simp] theorem header_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (header s) = r (.SFP reg) s := by
  rw [inputHeader_summary]
  simp [inputHeaderBranched, inputHeaderRead, state_simp_rules]

@[simp] theorem header_memory (s : ArmState) : (header s).mem = s.mem := by
  rw [inputHeader_summary]
  simp [inputHeaderBranched, inputHeaderRead, state_simp_rules]

theorem header_register (s : ArmState) (reg : BitVec 5)
    (unchanged : reg ∉ [1#5, 8#5, 9#5, 10#5, 11#5]) :
    r (.GPR reg) (header s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at unchanged
  rw [inputHeader_summary]
  simp [inputHeaderBranched, inputHeaderRead, NatExact.r_gpr_w, state_simp_rules,
    unchanged.1, unchanged.2.1, unchanged.2.2.1, unchanged.2.2.2.1, unchanged.2.2.2.2]

theorem header_fields (s : ArmState) :
    r (.GPR 1#5) (header s) = r (.GPR 1#5) s + 8#64 ∧
    r (.GPR 11#5) (header s) = read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s ∧
    r (.GPR 10#5) (header s) = read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s ∧
    r (.GPR 8#5) (header s) = read_mem_bytes 8 (r (.GPR 21#5) s + 32#64) s ∧
    r (.GPR 9#5) (header s) = read_mem_bytes 8 (r (.GPR 21#5) s + 40#64) s := by
  rw [inputHeader_summary]
  simp (config := {decide := true})
    [inputHeaderBranched, inputHeaderRead, state_simp_rules]

theorem header_pc (s : ArmState) (base : BitVec 64) (pc : read_pc s = base + 576#64) :
    read_pc (header s) = base + BitVec.ofNat 64
      (if read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = 0#64 then 3268 else 588) := by
  change r .PC s = _ at pc
  rw [inputHeader_summary]
  by_cases capZero : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = 0#64 <;>
    simp (config := {decide := true})
      [inputHeaderBranched, inputHeaderRead, state_simp_rules, capZero, pc, BitVec.add_assoc]

end SszArm.Measure.BitVector
