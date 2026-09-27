import SszArm.BoolExec

namespace SszArm.BoolCodec

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def tagInitialized (s : ArmState) : ArmState :=
  w (.GPR 9) 1#64 (w .PC (read_pc s + 4#64) s)

def reasonStored (s : ArmState) : ArmState :=
  w .PC (read_pc s + 4#64)
    (write_mem_bytes 4 (r (.GPR 0) s + 72#64) ((r (.GPR 8) s).setWidth 32) s)

def tagsStored (s : ArmState) : ArmState :=
  w .PC (read_pc s + 4#64)
    (write_mem_bytes 16 (r (.GPR 0) s) ((r (.GPR 9) s) ++ (r (.GPR 9) s)) s)

theorem tag_init (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4720#64) (he : read_err s = .None) :
    stepi s = tagInitialized s := by
  have hf := hc (4720, 0x52800029#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, tagInitialized, state_simp_rules, bitvec_rules, minimal_theory]
  apply w_of_w_commute <;> decide

theorem reason_store (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4724#64) (he : read_err s = .None) :
    stepi s = reasonStored s := by
  have hf := hc (4724, 0xb9004808#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, reasonStored, state_simp_rules, bitvec_rules, minimal_theory]

theorem tags_store (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4728#64) (he : read_err s = .None) :
    stepi s = tagsStored s := by
  have hf := hc (4728, 0xa9002409#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, tagsStored, state_simp_rules, bitvec_rules, minimal_theory]

/-- The actual shared error tail writes reason, error tag, and empty-string pointer. -/
theorem error_tail (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4720#64) (he : read_err s = .None) :
    run 3 s = tagsStored (reasonStored (tagInitialized s)) := by
  have hpc : r .PC s = base + 4720#64 := hp
  have hc1 : CodeAt (tagInitialized s) base := by
    simpa [CodeAt, tagInitialized, state_simp_rules] using hc
  have hp1 : read_pc (tagInitialized s) = base + 4724#64 := by
    simp [tagInitialized, state_simp_rules, hpc, BitVec.add_assoc]
  have he1 : read_err (tagInitialized s) = .None := by
    simpa [tagInitialized, state_simp_rules] using he
  have hc2 : CodeAt (reasonStored (tagInitialized s)) base := by
    simpa [CodeAt, reasonStored, tagInitialized, state_simp_rules] using hc
  have hp2 : read_pc (reasonStored (tagInitialized s)) = base + 4728#64 := by
    simp [reasonStored, tagInitialized, state_simp_rules, hpc, BitVec.add_assoc]
  have he2 : read_err (reasonStored (tagInitialized s)) = .None := by
    simpa [reasonStored, tagInitialized, state_simp_rules] using he
  change stepi (stepi (stepi s)) = _
  rw [tag_init s base hc hp he, reason_store (tagInitialized s) base hc1 hp1 he1,
    tags_store (reasonStored (tagInitialized s)) base hc2 hp2 he2]

end SszArm.BoolCodec
