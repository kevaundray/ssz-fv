import SszArm.Memmove

namespace SszArm.Memmove

open BitVec

/-- The dispatcher is decoded by the pinned ISA, not a postulated transition. -/
theorem step_dispatch (s : ArmState) (base : BitVec 64) (k : Nat) (hk : k < 5)
    (hc : CodeAt s base program) (hp : read_pc s = base + BitVec.ofNat 64 (4 * k))
    (he : read_err s = .None) : stepi s = dispatch_instruction k s := by
  have hindex : k < program.length := by
    simp only [program, List.length_cons, List.length_nil]
    omega
  have hf : s.program.find? (read_pc s) = some (program[k]'hindex) := by
    rw [hp]
    exact hc k hindex
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    simp [program] at hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true}) [dispatch_instruction,
      exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
      BitVec.sub_eq_add_neg]
    all_goals first
      | rfl
      | exact w_of_w_commute (by decide)

/-- The embedded ascending sequence is exactly the checked memcpy code. -/
theorem forward_code (s : ArmState) (base : BitVec 64) (hc : CodeAt s base program) :
    CodeAt s (base + 20#64) SszArm.Memcpy.program := by
  intro k hk
  simp only [SszArm.Memcpy.program, List.length_cons, List.length_nil] at hk
  match k, hk with
  | 0, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 5 (by decide)
  | 1, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 6 (by decide)
  | 2, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 7 (by decide)
  | 3, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 8 (by decide)
  | 4, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 9 (by decide)
  | 5, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 10 (by decide)
  | 6, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 11 (by decide)
  | 7, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 12 (by decide)
  | 8, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 13 (by decide)
  | 9, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 14 (by decide)
  | 10, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 15 (by decide)
  | 11, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 16 (by decide)
  | 12, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 17 (by decide)
  | 13, _ =>
    simpa (config := {decide := true}) [program, SszArm.Memcpy.program, BitVec.add_assoc]
      using hc 18 (by decide)

/-- Literal correspondence of the descending internal block. -/
theorem backward_code (s : ArmState) (base : BitVec 64) (hc : CodeAt s base program) :
    CodeAt s (base + 76#64) Backward.program := by
  intro k hk
  simp only [Backward.program, List.length_cons, List.length_nil] at hk
  match k, hk with
  | 0, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 19 (by decide)
  | 1, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 20 (by decide)
  | 2, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 21 (by decide)
  | 3, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 22 (by decide)
  | 4, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 23 (by decide)
  | 5, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 24 (by decide)
  | 6, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 25 (by decide)
  | 7, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 26 (by decide)
  | 8, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 27 (by decide)
  | 9, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 28 (by decide)
  | 10, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 29 (by decide)
  | 11, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 30 (by decide)
  | 12, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 31 (by decide)
  | 13, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 32 (by decide)
  | 14, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 33 (by decide)
  | 15, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 34 (by decide)
  | 16, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 35 (by decide)
  | 17, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 36 (by decide)
  | 18, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 37 (by decide)
  | 19, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 38 (by decide)
  | 20, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 39 (by decide)
  | 21, _ =>
    simpa (config := {decide := true}) [program, Backward.program, BitVec.add_assoc]
      using hc 40 (by decide)
  | k + 22, hk => omega

theorem step_return (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base + 72#64)
    (he : read_err s = .None) : stepi s = return_state s := by
  apply SszArm.step_ret s he
  rw [hp]
  simpa [program] using hc 18 (by decide)

theorem run_equal_entry (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hn : r (.GPR 2) s ≠ 0#64) : run 3 s = equal_entry s := by
  have h0 := step_dispatch s base 0 (by decide) hc (by simpa using hp) he
  change r .PC s = base at hp
  have h1 := step_dispatch (dispatch_instruction 0 s) base 1 (by decide)
    (by simpa only [CodeAt, dispatch_instruction_program] using hc)
    (by simp_all (config := {decide := true}) [dispatch_instruction, state_simp_rules])
    (by simpa only [dispatch_instruction_err] using he)
  have h2 := step_dispatch (dispatch_instruction 1 (dispatch_instruction 0 s)) base 2 (by decide)
    (by simpa only [CodeAt, dispatch_instruction_program] using hc)
    (by simp_all (config := {decide := true}) [dispatch_instruction, state_simp_rules,
      BitVec.add_assoc])
    (by simpa only [dispatch_instruction_err] using he)
  change stepi (stepi (stepi s)) = _
  rw [h0, h1, h2]
  rfl

theorem equal_entry_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base)
    (hn : r (.GPR 2) s ≠ 0#64) :
    read_pc (equal_entry s) =
      if r (.GPR 0) s = r (.GPR 1) s then base + 72#64 else base + 12#64 := by
  have hz : r (.GPR 0) s - r (.GPR 1) s = 0#64 ↔ r (.GPR 0) s = r (.GPR 1) s := by
    bv_omega
  change r .PC s = base at hp
  simp_all (config := {decide := true, instances := true})
    [equal_entry, dispatch_instruction, state_simp_rules, BitVec.add_assoc]

theorem run_dispatch (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hn : r (.GPR 2) s ≠ 0#64) (hne : r (.GPR 0) s ≠ r (.GPR 1) s) :
    run 5 s = dispatch s := by
  have hep : read_pc (equal_entry s) = base + 12#64 := by
    simpa only [if_neg hne] using equal_entry_pc s base hp hn
  have h3 := step_dispatch (equal_entry s) base 3 (by decide)
    (by simpa only [equal_entry, CodeAt, dispatch_instruction_program] using hc) hep
    (by simpa only [equal_entry, dispatch_instruction_err] using he)
  change r .PC (equal_entry s) = base + 12#64 at hep
  have h4 := step_dispatch (dispatch_instruction 3 (equal_entry s)) base 4 (by decide)
    (by simpa only [equal_entry, CodeAt, dispatch_instruction_program] using hc)
    (by simp (config := {decide := true}) [dispatch_instruction, state_simp_rules, hep,
      BitVec.add_assoc])
    (by simpa only [equal_entry, dispatch_instruction_err] using he)
  rw [show 5 = 3 + 2 by decide, run_plus, run_equal_entry s base hc hp he hn]
  change stepi (stepi (equal_entry s)) = _
  rw [h3, h4]
  rfl

theorem dispatch_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base)
    (hn : r (.GPR 2) s ≠ 0#64) (hne : r (.GPR 0) s ≠ r (.GPR 1) s) :
    read_pc (dispatch s) =
      if (r (.GPR 1) s).toNat ≤ (r (.GPR 0) s).toNat then base + 76#64 else base + 20#64 := by
  have hep : read_pc (equal_entry s) = base + 12#64 := by
    simpa only [if_neg hne] using equal_entry_pc s base hp hn
  have h0 : r (.GPR 0) (equal_entry s) = r (.GPR 0) s := by
    simp [equal_entry, dispatch_instruction, state_simp_rules]
  have h1 : r (.GPR 1) (equal_entry s) = r (.GPR 1) s := by
    simp [equal_entry, dispatch_instruction, state_simp_rules]
  change r .PC (equal_entry s) = base + 12#64 at hep
  simp_all (config := {decide := true, instances := true})
    [dispatch, dispatch_instruction, state_simp_rules, apply_ite,
      carry_compare, BitVec.add_assoc]

/-- Actual full-ISA execution, with exact finite fuel and both RET instructions. -/
theorem program_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None) :
    run (fuel s) s = result s := by
  by_cases hn : r (.GPR 2) s = 0#64
  · have h0 := step_dispatch s base 0 (by decide) hc (by simpa using hp) he
    have hret := step_return (dispatch_instruction 0 s) base
      (by simpa only [CodeAt, dispatch_instruction_program] using hc)
      (by change r .PC s = base at hp
          simp_all (config := {decide := true, instances := true})
            [dispatch_instruction, state_simp_rules])
      (by simpa only [dispatch_instruction_err] using he)
    simp only [fuel, result, if_pos hn]
    change stepi (stepi s) = _
    rw [h0, hret]
  · by_cases heq : r (.GPR 0) s = r (.GPR 1) s
    · have hret := step_return (equal_entry s) base
        (by simpa only [equal_entry, CodeAt, dispatch_instruction_program] using hc)
        (by simpa only [if_pos heq] using equal_entry_pc s base hp hn)
        (by simpa only [equal_entry, dispatch_instruction_err] using he)
      simp only [fuel, result, if_neg hn, if_pos heq]
      rw [show 4 = 3 + 1 by decide, run_plus, run_equal_entry s base hc hp he hn]
      exact hret
    · have hdc : CodeAt (dispatch s) base program := by
        simpa only [CodeAt, dispatch_program] using hc
      have hde : read_err (dispatch s) = .None :=
        (dispatch_frame s .ERR trivial).trans he
      have hdn := (dispatch_data s).2.2.2
      have hdp := dispatch_pc s base hp hn heq
      by_cases hlt : (r (.GPR 0) s).toNat < (r (.GPR 1) s).toNat
      · have hnot : ¬(r (.GPR 1) s).toNat ≤ (r (.GPR 0) s).toNat := by omega
        rw [if_neg hnot] at hdp
        have hr := SszArm.Memcpy.program_run (dispatch s) (base + 20#64)
          (forward_code (dispatch s) base hdc) hdp hde
        rw [hdn] at hr
        simp only [fuel, result, if_neg hn, if_neg heq, if_pos hlt]
        rw [run_plus, run_dispatch s base hc hp he hn heq]
        exact hr
      · have hle : (r (.GPR 1) s).toNat ≤ (r (.GPR 0) s).toNat := by omega
        rw [if_pos hle] at hdp
        have hr := Backward.program_run (dispatch s) (base + 76#64)
          (backward_code (dispatch s) base hdc) hdp hde (by simpa only [hdn] using hn)
        rw [hdn] at hr
        simp only [fuel, result, if_neg hn, if_neg heq, if_neg hlt]
        rw [run_plus, run_dispatch s base hc hp he hn heq]
        exact hr

private theorem return_frame (s : ArmState) (f : StateField) (hf : Preserved f) :
    r f (return_state s) = r f s := by
  have hpc : f ≠ .PC := by intro h; subst f; exact hf
  exact r_of_w_different hpc

theorem result_frame (s : ArmState) (f : StateField) (hf : Preserved f) :
    r f (result s) = r f s := by
  unfold result
  split
  · rw [return_frame _ _ hf, dispatch_instruction_frame _ _ _ hf]
  · split
    · rw [return_frame _ _ hf]
      simp only [equal_entry, dispatch_instruction_frame _ _ _ hf]
    · split
      · rw [SszArm.Memcpy.result_frame _ _ hf, dispatch_frame _ _ hf]
      · rw [Backward.result_frame _ _ hf, dispatch_frame _ _ hf]

theorem result_program (s : ArmState) : (result s).program = s.program := by
  unfold result
  split
  · simp only [return_state, w_program, dispatch_instruction_program]
  · split
    · simp only [return_state, w_program, equal_entry, dispatch_instruction_program]
    · split
      · rw [SszArm.Memcpy.result_program, dispatch_program]
      · rw [Backward.result_program, dispatch_program]

theorem result_return (s : ArmState) : read_pc (result s) = r (.GPR 30) s := by
  have hf : Preserved (.GPR 30) := by simp [Preserved, SszArm.Memcpy.Preserved]
  unfold result
  split
  · simp only [return_state, read_pc, r_of_w_same,
      dispatch_instruction_frame _ _ _ hf]
  · split
    · simp only [return_state, read_pc, r_of_w_same, equal_entry,
        dispatch_instruction_frame _ _ _ hf]
    · split
      · rw [SszArm.Memcpy.result_return, dispatch_frame _ _ hf]
      · rw [Backward.result_return, dispatch_frame _ _ hf]

/-- The whole result reads only the original snapshot in its specification.
There is deliberately no unchanged-source postcondition for overlapping ranges. -/
theorem result_memory (s : ArmState)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsrc : (r (.GPR 1) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64) :
    ∀ a, (result s).mem a = image s.mem (r (.GPR 0) s) (r (.GPR 1) s)
      (r (.GPR 2) s).toNat a := by
  intro a
  by_cases hn : r (.GPR 2) s = 0#64
  · rw [result, if_pos hn]
    have hm : (return_state (dispatch_instruction 0 s)).mem = s.mem := by
      simp [return_state, dispatch_instruction, state_simp_rules]
    rw [hm, hn]
    simp only [image, SszArm.Memcpy.image, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
    rw [if_neg (by omega)]
  · by_cases heq : r (.GPR 0) s = r (.GPR 1) s
    · simp only [result, if_neg hn, if_pos heq, return_state, equal_entry,
        dispatch_instruction, ArmState.mem_w_eq_mem, image, SszArm.Memcpy.image]
      split
      · rename_i h
        congr 1
        bv_omega
      · rfl
    · obtain ⟨hm, h0, h1, h2⟩ := dispatch_data s
      have hd : (r (.GPR 0) (dispatch s)).toNat + (r (.GPR 2) (dispatch s)).toNat ≤ 2^64 := by
        simpa only [h0, h2] using hdst
      have hs : (r (.GPR 1) (dispatch s)).toNat + (r (.GPR 2) (dispatch s)).toNat ≤ 2^64 := by
        simpa only [h1, h2] using hsrc
      by_cases hlt : (r (.GPR 0) s).toNat < (r (.GPR 1) s).toNat
      · have ho : (r (.GPR 0) (dispatch s)).toNat ≤ (r (.GPR 1) (dispatch s)).toNat := by
          rw [h0, h1]; omega
        simp only [result, if_neg hn, if_neg heq, if_pos hlt]
        simpa only [hm, h0, h1, h2] using Forward.result_memory (dispatch s) hd hs ho a
      · have ho : (r (.GPR 1) (dispatch s)).toNat ≤ (r (.GPR 0) (dispatch s)).toNat := by
          rw [h0, h1]; omega
        simp only [result, if_neg hn, if_neg heq, if_neg hlt]
        simpa only [hm, h0, h1, h2] using Backward.result_memory (dispatch s) hd hs ho a

/-- Full refinement at arbitrary code base and runtime length. The mathematical
ends may equal 2^64. All AAPCS64 callee-saved fields and original x0 are preserved;
only destination bytes change, to the caller's original source snapshot. -/
theorem program_correct (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsrc : (r (.GPR 1) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64) :
    let final := run (fuel s) s
    read_err final = .None ∧ read_pc final = r (.GPR 30) s ∧
    r (.GPR 0) final = r (.GPR 0) s ∧ final.program = s.program ∧
    (∀ f, Preserved f → r f final = r f s) ∧
    (∀ a, final.mem a = image s.mem (r (.GPR 0) s) (r (.GPR 1) s)
      (r (.GPR 2) s).toNat a) := by
  dsimp only
  rw [program_run s base hc hp he]
  refine ⟨?_, result_return s, result_frame s (.GPR 0) (by simp [Preserved, SszArm.Memcpy.Preserved]),
    result_program s, result_frame s, result_memory s hdst hsrc⟩
  exact (result_frame s .ERR trivial).trans he

/-- Pointwise copied-byte corollary, including valid overlap in either direction. -/
theorem program_byte (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsrc : (r (.GPR 1) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (i : Nat) (hi : i < (r (.GPR 2) s).toNat) :
    (run (fuel s) s).mem (r (.GPR 0) s + BitVec.ofNat 64 i) =
      s.mem (r (.GPR 1) s + BitVec.ofNat 64 i) := by
  rw [program_run s base hc hp he, result_memory s hdst hsrc]
  have ha : (r (.GPR 0) s + BitVec.ofNat 64 i).toNat = (r (.GPR 0) s).toNat + i := by bv_omega
  simp only [image, SszArm.Memcpy.image, ha]
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- Exact outside-destination frame, not an incorrect overlapping-source frame. -/
theorem program_outside (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsrc : (r (.GPR 1) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (a : BitVec 64) (hout : a.toNat < (r (.GPR 0) s).toNat ∨
      (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ a.toNat) :
    (run (fuel s) s).mem a = s.mem a := by
  rw [program_run s base hc hp he, result_memory s hdst hsrc]
  unfold image SszArm.Memcpy.image
  rw [if_neg (by omega)]

/-- No data access and actual RET after only CBZ, even for unmapped/null pointers. -/
theorem program_zero (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hn : r (.GPR 2) s = 0#64) :
    run 2 s = return_state (dispatch_instruction 0 s) := by
  simpa only [fuel, result, if_pos hn] using program_run s base hc hp he

/-- Equality returns without any load/store, independently of count or mapping. -/
theorem program_equal (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hn : r (.GPR 2) s ≠ 0#64) (heq : r (.GPR 0) s = r (.GPR 1) s) :
    run 4 s = return_state (equal_entry s) := by
  simpa only [fuel, result, if_neg hn, if_pos heq] using program_run s base hc hp he

end SszArm.Memmove
