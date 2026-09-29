import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.Simd

/-- movi v0.2d, #0000000000000000. All 128 bits and all copied bytes are retained. -/
theorem word_6f00e400 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x6f00e400#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (w (.SFP 0#5) 0#128 s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]
  exact w_of_w_commute (by decide)

/-- stp q0, q0, [sp, #0x90]. All 128 bits and all copied bytes are retained. -/
theorem word_ad0483e0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xad0483e0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 32 (r (.GPR 31#5) s + 144#64) ((r (.SFP 0#5) s) ++ (r (.SFP 0#5) s)) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q0, [sp, #0xb0]. All 128 bits and all copied bytes are retained. -/
theorem word_3d802fe0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d802fe0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 31#5) s + 176#64) (r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- ldp q1, q0, [sp, #0x90]. All 128 bits and all copied bytes are retained. -/
theorem word_ad4483e1 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xad4483e1#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (w (.SFP 0#5) ((read_mem_bytes 32 (r (.GPR 31#5) s + 144#64) s).extractLsb' 128 128)
      (w (.SFP 1#5) ((read_mem_bytes 32 (r (.GPR 31#5) s + 144#64) s).extractLsb' 0 128) s)) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- ldr q2, [sp, #0xb0]. All 128 bits and all copied bytes are retained. -/
theorem word_3dc02fe2 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3dc02fe2#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (w (.SFP 2#5) (read_mem_bytes 16 (r (.GPR 31#5) s + 176#64) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- stp q1, q0, [sp, #0x40]. All 128 bits and all copied bytes are retained. -/
theorem word_ad0203e1 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xad0203e1#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 32 (r (.GPR 31#5) s + 64#64) ((r (.SFP 0#5) s) ++ (r (.SFP 1#5) s)) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q2, [sp, #0x60]. All 128 bits and all copied bytes are retained. -/
theorem word_3d801be2 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d801be2#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 31#5) s + 96#64) (r (.SFP 2#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- ldp q0, q1, [sp, #0xe0]. All 128 bits and all copied bytes are retained. -/
theorem word_ad4707e0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xad4707e0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (w (.SFP 1#5) ((read_mem_bytes 32 (r (.GPR 31#5) s + 224#64) s).extractLsb' 128 128)
      (w (.SFP 0#5) ((read_mem_bytes 32 (r (.GPR 31#5) s + 224#64) s).extractLsb' 0 128) s)) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- ldr q2, [sp, #0x100]. All 128 bits and all copied bytes are retained. -/
theorem word_3dc043e2 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3dc043e2#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (w (.SFP 2#5) (read_mem_bytes 16 (r (.GPR 31#5) s + 256#64) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- stp q0, q1, [x8]. All 128 bits and all copied bytes are retained. -/
theorem word_ad000500 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xad000500#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 32 (r (.GPR 8#5) s + 0#64) ((r (.SFP 1#5) s) ++ (r (.SFP 0#5) s)) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q2, [x8, #0x20]. All 128 bits and all copied bytes are retained. -/
theorem word_3d800902 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d800902#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 8#5) s + 32#64) (r (.SFP 2#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- stp q0, q0, [x21, #0x20]. All 128 bits and all copied bytes are retained. -/
theorem word_ad0102a0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xad0102a0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 32 (r (.GPR 21#5) s + 32#64) ((r (.SFP 0#5) s) ++ (r (.SFP 0#5) s)) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q0, [x21, #0x10]. All 128 bits and all copied bytes are retained. -/
theorem word_3d8006a0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d8006a0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 21#5) s + 16#64) (r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q0, [x23, #0x30]. All 128 bits and all copied bytes are retained. -/
theorem word_3d800ee0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d800ee0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 23#5) s + 48#64) (r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q0, [x23, #0x10]. All 128 bits and all copied bytes are retained. -/
theorem word_3d8006e0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d8006e0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 23#5) s + 16#64) (r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q0, [x23, #0x20]. All 128 bits and all copied bytes are retained. -/
theorem word_3d800ae0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d800ae0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 23#5) s + 32#64) (r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- stp q0, q0, [sp, #0x80]. All 128 bits and all copied bytes are retained. -/
theorem word_ad0403e0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xad0403e0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 32 (r (.GPR 31#5) s + 128#64) ((r (.SFP 0#5) s) ++ (r (.SFP 0#5) s)) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q0, [sp, #0x70]. All 128 bits and all copied bytes are retained. -/
theorem word_3d801fe0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d801fe0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 31#5) s + 112#64) (r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- stp q0, q0, [sp, #0x20]. All 128 bits and all copied bytes are retained. -/
theorem word_ad0103e0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xad0103e0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 32 (r (.GPR 31#5) s + 32#64) ((r (.SFP 0#5) s) ++ (r (.SFP 0#5) s)) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q0, [sp, #0x10]. All 128 bits and all copied bytes are retained. -/
theorem word_3d8007e0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d8007e0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 31#5) s + 16#64) (r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- stp q0, q0, [sp, #0x50]. All 128 bits and all copied bytes are retained. -/
theorem word_ad0283e0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xad0283e0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 32 (r (.GPR 31#5) s + 80#64) ((r (.SFP 0#5) s) ++ (r (.SFP 0#5) s)) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q0, [sp, #0x40]. All 128 bits and all copied bytes are retained. -/
theorem word_3d8013e0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d8013e0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 31#5) s + 64#64) (r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- stp q0, q0, [x19, #0x20]. All 128 bits and all copied bytes are retained. -/
theorem word_ad010260 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xad010260#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 32 (r (.GPR 19#5) s + 32#64) ((r (.SFP 0#5) s) ++ (r (.SFP 0#5) s)) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q0, [x19, #0x10]. All 128 bits and all copied bytes are retained. -/
theorem word_3d800660 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d800660#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 19#5) s + 16#64) (r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- stp q0, q0, [sp, #0x30]. All 128 bits and all copied bytes are retained. -/
theorem word_ad0183e0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xad0183e0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 32 (r (.GPR 31#5) s + 48#64) ((r (.SFP 0#5) s) ++ (r (.SFP 0#5) s)) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

/-- str q0, [sp, #0x20]. All 128 bits and all copied bytes are retained. -/
theorem word_3d800be0 (s : ArmState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x3d800be0#32) :
    stepi s = w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 31#5) s + 32#64) (r (.SFP 0#5) s) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.setWidth_eq, aligned, BitVec.add_assoc]

end SszArm.Codec.Linked.Simd
