import SszArm.BoolMemory

namespace SszArm.BoolCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Saved activation values, all read from the original memory and stack pointer. -/
def returned (s : ArmState) : ArmState :=
  let sp := r (.GPR 31) s
  let t := w (.GPR 19) (read_mem_bytes 8 (sp + 360#64) s)
    (w (.GPR 20) (read_mem_bytes 8 (sp + 352#64) s) s)
  let t := w (.GPR 21) (read_mem_bytes 8 (sp + 344#64) s)
    (w (.GPR 22) (read_mem_bytes 8 (sp + 336#64) s) t)
  let t := w (.GPR 23) (read_mem_bytes 8 (sp + 328#64) s)
    (w (.GPR 24) (read_mem_bytes 8 (sp + 320#64) s) t)
  let t := w (.GPR 25) (read_mem_bytes 8 (sp + 312#64) s)
    (w (.GPR 26) (read_mem_bytes 8 (sp + 304#64) s) t)
  let t := w (.GPR 27) (read_mem_bytes 8 (sp + 296#64) s)
    (w (.GPR 28) (read_mem_bytes 8 (sp + 288#64) s) t)
  let t := w (.GPR 30) (read_mem_bytes 8 (sp + 280#64) s)
    (w (.GPR 29) (read_mem_bytes 8 (sp + 272#64) s) t)
  w .PC (read_mem_bytes 8 (sp + 280#64) s) (w (.GPR 31) (sp + 368#64) t)

/-- Six real LDP pairs, ADD SP, and RET, including all restored registers. -/
theorem epilogue (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (hp : read_pc s = base + 4732#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 8 s = returned s := by
  let sp := r (.GPR 31) s
  let s1 := w .PC (base + 4736#64)
    (w (.GPR 19) (read_mem_bytes 8 (sp + 360#64) s)
      (w (.GPR 20) (read_mem_bytes 8 (sp + 352#64) s) s))
  let s2 := w .PC (base + 4740#64)
    (w (.GPR 21) (read_mem_bytes 8 (sp + 344#64) s)
      (w (.GPR 22) (read_mem_bytes 8 (sp + 336#64) s) s1))
  let s3 := w .PC (base + 4744#64)
    (w (.GPR 23) (read_mem_bytes 8 (sp + 328#64) s)
      (w (.GPR 24) (read_mem_bytes 8 (sp + 320#64) s) s2))
  let s4 := w .PC (base + 4748#64)
    (w (.GPR 25) (read_mem_bytes 8 (sp + 312#64) s)
      (w (.GPR 26) (read_mem_bytes 8 (sp + 304#64) s) s3))
  let s5 := w .PC (base + 4752#64)
    (w (.GPR 27) (read_mem_bytes 8 (sp + 296#64) s)
      (w (.GPR 28) (read_mem_bytes 8 (sp + 288#64) s) s4))
  let s6 := w .PC (base + 4756#64)
    (w (.GPR 30) (read_mem_bytes 8 (sp + 280#64) s)
      (w (.GPR 29) (read_mem_bytes 8 (sp + 272#64) s) s5))
  let s7 := w .PC (base + 4760#64) (w (.GPR 31) (sp + 368#64) s6)
  have hpc : r .PC s = base + 4732#64 := hp
  have h1 : stepi s = s1 := by
    have hf := hc (4732, 0xa9564ff4#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pair_read_low, pair_read_high, s1, sp, hpc, ha, BitVec.add_assoc]
  have h2 : stepi s1 = s2 := by
    have hf := hc (4736, 0xa95557f6#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s1 _ _ _
      (by simpa [s1, state_simp_rules] using he)
      (show read_pc s1 = base + 4736#64 by simp [s1, state_simp_rules])
      (by simpa [fetch_inst, s1, state_simp_rules] using (fetch_inst_from_program.trans hf)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pair_read_low, pair_read_high, s2, s1, sp, ha, BitVec.add_assoc]
  have h3 : stepi s2 = s3 := by
    have hf := hc (4740, 0xa9545ff8#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s2 _ _ _
      (by simpa [s2, s1, state_simp_rules] using he)
      (show read_pc s2 = base + 4740#64 by simp [s2, state_simp_rules])
      (by simpa [fetch_inst, s2, s1, state_simp_rules] using (fetch_inst_from_program.trans hf)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pair_read_low, pair_read_high, s3, s2, s1, sp, ha, BitVec.add_assoc]
  have h4 : stepi s3 = s4 := by
    have hf := hc (4744, 0xa95367fa#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s3 _ _ _
      (by simpa [s3, s2, s1, state_simp_rules] using he)
      (show read_pc s3 = base + 4744#64 by simp [s3, state_simp_rules])
      (by simpa [fetch_inst, s3, s2, s1, state_simp_rules] using (fetch_inst_from_program.trans hf)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pair_read_low, pair_read_high, s4, s3, s2, s1, sp, ha, BitVec.add_assoc]
  have h5 : stepi s4 = s5 := by
    have hf := hc (4748, 0xa9526ffc#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s4 _ _ _
      (by simpa [s4, s3, s2, s1, state_simp_rules] using he)
      (show read_pc s4 = base + 4748#64 by simp [s4, state_simp_rules])
      (by simpa [fetch_inst, s4, s3, s2, s1, state_simp_rules]
        using (fetch_inst_from_program.trans hf)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pair_read_low, pair_read_high, s5, s4, s3, s2, s1, sp, ha, BitVec.add_assoc]
  have h6 : stepi s5 = s6 := by
    have hf := hc (4752, 0xa9517bfd#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s5 _ _ _
      (by simpa [s5, s4, s3, s2, s1, state_simp_rules] using he)
      (show read_pc s5 = base + 4752#64 by simp [s5, state_simp_rules])
      (by simpa [fetch_inst, s5, s4, s3, s2, s1, state_simp_rules]
        using (fetch_inst_from_program.trans hf)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pair_read_low, pair_read_high, s6, s5, s4, s3, s2, s1, sp, ha, BitVec.add_assoc]
  have h7 : stepi s6 = s7 := by
    have hf := hc (4756, 0x9105c3ff#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s6 _ _ _
      (by simpa [s6, s5, s4, s3, s2, s1, state_simp_rules] using he)
      (show read_pc s6 = base + 4756#64 by simp [s6, state_simp_rules])
      (by simpa [fetch_inst, s6, s5, s4, s3, s2, s1, state_simp_rules]
        using (fetch_inst_from_program.trans hf)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       s7, s6, s5, s4, s3, s2, s1, sp, BitVec.add_assoc]
    apply state_eq_iff_components_eq.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro field
      cases field <;> simp (config := {decide := true}) [state_simp_rules]
      simp only [r, w]
      rfl
    · simp [state_simp_rules]
    · intro n address
      simp [state_simp_rules]
  have h8 : stepi s7 = returned s := by
    have hf := hc (4760, 0xd65f03c0#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s7 _ _ _
      (by simpa [s7, s6, s5, s4, s3, s2, s1, state_simp_rules] using he)
      (show read_pc s7 = base + 4760#64 by simp [s7, state_simp_rules])
      (by simpa [fetch_inst, s7, s6, s5, s4, s3, s2, s1, state_simp_rules]
        using (fetch_inst_from_program.trans hf)) rfl]
    apply state_eq_iff_components_eq.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro field
      cases field <;> simp (config := {decide := true, instances := true})
        [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         returned, s7, s6, s5, s4, s3, s2, s1, sp]
      simp only [r, w]
      rfl
    · simp [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
        returned, s7, s6, s5, s4, s3, s2, s1]
    · intro n address
      simp [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
        returned, s7, s6, s5, s4, s3, s2, s1]
  change stepi (stepi (stepi (stepi (stepi (stepi (stepi (stepi s))))))) = _
  rw [h1, h2, h3, h4, h5, h6, h7, h8]

theorem returned_sp (s : ArmState) :
    r (.GPR 31#5) (returned s) = r (.GPR 31#5) s + 368#64 := by
  simp (config := {decide := true}) [returned, state_simp_rules]

theorem returned_mem (s : ArmState) : (returned s).mem = s.mem := by
  simp [returned, state_simp_rules]

theorem returned_pc_read (s : ArmState) :
    read_pc (returned s) =
      read_mem_bytes 8 (r (.GPR 31#5) s + 280#64) (returned s) := by
  simp (config := {decide := true}) [returned, state_simp_rules]

def savedRegisters : List (BitVec 5 × Nat) :=
  [(19#5, 360), (20#5, 352), (21#5, 344), (22#5, 336), (23#5, 328), (24#5, 320),
   (25#5, 312), (26#5, 304), (27#5, 296), (28#5, 288), (29#5, 272), (30#5, 280)]

theorem savedRegister_bounds (reg : BitVec 5) (offset : Nat)
    (h : (reg, offset) ∈ savedRegisters) : 272 ≤ offset ∧ offset + 8 ≤ 368 := by
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  omega

theorem returned_register (s : ArmState) (reg : BitVec 5) (offset : Nat)
    (h : (reg, offset) ∈ savedRegisters) :
    r (.GPR reg) (returned s) =
      read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) (returned s) := by
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp (config := {decide := true}) [returned, state_simp_rules]

end SszArm.BoolCodec
