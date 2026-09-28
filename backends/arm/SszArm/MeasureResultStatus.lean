import SszArm.MeasureResultOps

namespace SszArm.Measure.Result

@[irreducible] def statusResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 4116#64)
    (write_mem_bytes 4 (r (.GPR 19#5) s + 64#64) ((r (.GPR 8#5) s).setWidth 32) s)

theorem status_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3896#64) : run 2 s = statusResult s base := by
  have follows : Follows base [p3896, p3900] s := by
    change r .PC s = _ at pc
    change r .ERR s = _ at error
    simp (config := {decide := true, instances := true})
      [Follows, p3896, p3900, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, pc, error, BitVec.add_assoc]
  rw [show 2 = [p3896, p3900].length by rfl, runs _ s base code follows]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, p3896, p3900, Op.effect, exec_inst, statusResult, state_simp_rules,
     bitvec_rules, minimal_theory, pc, BitVec.add_assoc]

@[simp] theorem status_program (s : ArmState) (base : BitVec 64) :
    (statusResult s base).program = s.program := by
  simp [statusResult, state_simp_rules]

@[simp] theorem status_error (s : ArmState) (base : BitVec 64) :
    read_err (statusResult s base) = read_err s := by
  simp [statusResult, state_simp_rules]

@[simp] theorem status_pc (s : ArmState) (base : BitVec 64) :
    read_pc (statusResult s base) = base + 4116#64 := by
  simp [statusResult, state_simp_rules]

@[simp] theorem status_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (statusResult s base) = r (.GPR reg) s := by
  simp [statusResult, state_simp_rules]

@[simp] theorem status_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (statusResult s base) = r (.SFP reg) s := by
  simp [statusResult, state_simp_rules]

theorem status_frame (s : ArmState) (base : BitVec 64)
    (bound : (r (.GPR 19#5) s).toNat + 68 ≤ 2^64) :
    Delimited.MemoryFrame [((r (.GPR 19#5) s).toNat + 64, 4)] s (statusResult s base) := by
  have address : (r (.GPR 19#5) s + 64#64).toNat = (r (.GPR 19#5) s).toNat + 64 := by
    bv_omega
  have stored := Delimited.store_frame s (r (.GPR 19#5) s + 64#64) 4
    ((r (.GPR 8#5) s).setWidth 32) (by rw [address]; omega)
  simpa only [address, statusResult, Delimited.MemoryFrame, ArmState.mem_w_eq_mem] using stored

theorem status_value (s : ArmState) (base : BitVec 64)
    (bound : (r (.GPR 19#5) s).toNat + 68 ≤ 2^64) :
    read_mem_bytes 4 (r (.GPR 19#5) s + 64#64) (statusResult s base) =
      (r (.GPR 8#5) s).setWidth 32 := by
  simp only [statusResult, state_simp_rules]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 4 _ _ (by bv_omega)

end SszArm.Measure.Result
