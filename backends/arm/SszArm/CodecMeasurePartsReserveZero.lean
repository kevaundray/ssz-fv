import SszArm.CodecMeasurePartsReserveCommit

set_option autoImplicit false

namespace SszArm.Codec.Measure.PartsReserve

/-- The actual zero-count branch precedes all arena header reads and checks. -/
def selected (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (if r (.GPR 26) s = 0#64 then base + 628#64 else base + 364#64) s

theorem select_step (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureParts.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 360#64) : stepi s = selected s base := by
  have fetched := Linked.MeasureParts.chunk1_codeAt code (360, 0xb400087a#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = base + 360#64 at pc
  simp (config := {decide := true, instances := true})
    [selected, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      pc, BitVec.add_assoc, BitVec.setWidth_eq, apply_ite]

def zeroResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w (.GPR 24) 8#64 (w .PC (base + 632#64) s)

theorem zero_step (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureParts.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 628#64) : stepi s = zeroResult s base := by
  have fetched := Linked.MeasureParts.chunk2_codeAt code (628, 0x52800118#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = base + 628#64 at pc
  simp (config := {decide := true, instances := true})
    [zeroResult, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      pc, BitVec.add_assoc, BitVec.setWidth_eq]
  exact w_of_w_commute (by decide)

/-- No cursor precondition is needed: even an invalid cursor is ignored by the
native empty typed reservation, and its dangling child pointer is eight. -/
theorem zero_runs (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureParts.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 360#64) (zero : r (.GPR 26) s = 0#64) :
    run 2 s = zeroResult s base := by
  have selectRun := select_step s base code error pc
  have codeSelected : Linked.MeasureParts.CodeAt (selected s base) base := by
    intro row member
    simpa [selected, state_simp_rules] using code row member
  have stepZero := zero_step (selected s base) base codeSelected
    (by simpa [selected, state_simp_rules] using error)
    (by simp [selected, zero, state_simp_rules])
  rw [show (2 : Nat) = 1 + 1 from rfl, run_plus]
  change stepi (stepi s) = _
  rw [selectRun, stepZero]
  simp [selected, zeroResult, state_simp_rules]

theorem zero_observations (s : ArmState) (base : BitVec 64) :
    read_pc (zeroResult s base) = base + 632#64 ∧
      r (.GPR 24) (zeroResult s base) = 8#64 ∧
      (zeroResult s base).mem = s.mem ∧
      (zeroResult s base).program = s.program ∧
      read_err (zeroResult s base) = read_err s ∧
      ∀ reg : BitVec 5, reg ≠ 24#5 → r (.GPR reg) (zeroResult s base) = r (.GPR reg) s := by
  simp [zeroResult, state_simp_rules]

end SszArm.Codec.Measure.PartsReserve
