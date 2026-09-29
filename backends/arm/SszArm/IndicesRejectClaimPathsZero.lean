import SszArm.IndicesLinkedRejectClaimPaths

namespace SszArm.Indices.RejectClaimPaths.Zero

/-- Empty and all-zero Large claims leave through offset 72, skipping the
Small-only pointer assignment at 856. The original pointer and length survive. -/
theorem large_guard (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 72#64) (exhausted : r (.GPR 9#5) s = 0#64) :
    stepi s = w .PC (base + 860#64) s := by
  have fetched := Linked.RejectClaimPaths.chunk0_codeAt code (72, 0xb40018a9#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, exhausted, pc, BitVec.add_assoc]

theorem small_guard (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 188#64) (zero : r (.GPR 20#5) s = 0#64) :
    stepi s = w .PC (base + 856#64) s := by
  have fetched := Linked.RejectClaimPaths.chunk0_codeAt code (188, 0xb40014f4#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero, pc, BitVec.add_assoc]

theorem small_pointer (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 856#64) :
    stepi s = w (.GPR 21#5) 0#64 (w .PC (base + 860#64) s) := by
  have fetched := Linked.RejectClaimPaths.chunk3_codeAt code (856, 0xaa1f03f5#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, pc, BitVec.add_assoc]

theorem small_run (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 188#64) (zero : r (.GPR 20#5) s = 0#64) :
    run 2 s = w (.GPR 21#5) 0#64 (w .PC (base + 860#64) s) := by
  have guardCode : Linked.RejectClaimPaths.CodeAt (w .PC (base + 856#64) s) base := by
    simpa only [Linked.RejectClaimPaths.CodeAt, Codec.Linked.WordsAt, state_simp_rules] using code
  have guardError : read_err (w .PC (base + 856#64) s) = .None := by
    simpa only [state_simp_rules] using error
  change run 1 (stepi s) = _
  rw [small_guard s base code error pc zero]
  change stepi (w .PC (base + 856#64) s) = _
  rw [small_pointer _ base guardCode guardError (by simp [state_simp_rules])]
  simp [state_simp_rules]

/-- No canonical-only input restriction is needed at the Large error edge. -/
theorem large_raw_pair (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 72#64) (exhausted : r (.GPR 9#5) s = 0#64) :
    r (.GPR 21#5) (run 1 s) = r (.GPR 21#5) s ∧
      r (.GPR 20#5) (run 1 s) = r (.GPR 20#5) s ∧ (run 1 s).mem = s.mem := by
  change r (.GPR 21#5) (stepi s) = _ ∧ r (.GPR 20#5) (stepi s) = _ ∧ (stepi s).mem = _
  rw [large_guard s base code error pc exhausted]
  simp [state_simp_rules]

end SszArm.Indices.RejectClaimPaths.Zero
