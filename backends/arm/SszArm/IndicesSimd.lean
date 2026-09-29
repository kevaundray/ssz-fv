import SszArm.CodecSimd

namespace SszArm.Indices.Linked.Simd

/-- stp q0, q0, [sp, #0xa0]: all 128 bits in each real SIMD lane are retained. -/
theorem word_ad0503e0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xad0503e0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 32 (r (.GPR 31#5) s + 160#64) (r (.SFP 0#5) s ++ r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q0, [sp, #0x90]: all 128 bits in each real SIMD lane are retained. -/
theorem word_3d8027e0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d8027e0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 31#5) s + 144#64) (r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- stp q0, q0, [x8, #0x10]: all 128 bits in each real SIMD lane are retained. -/
theorem word_ad008100 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xad008100#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 32 (r (.GPR 8#5) s + 16#64) (r (.SFP 0#5) s ++ r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q0, [x8]: all 128 bits in each real SIMD lane are retained. -/
theorem word_3d800100 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d800100#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 8#5) s + 0#64) (r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

end SszArm.Indices.Linked.Simd
