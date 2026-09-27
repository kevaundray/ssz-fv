import SszArm.MemsetMemory

namespace SszArm.Memset

open BitVec

private theorem carry16_immediate (x : BitVec 64) :
    (AddWithCarry x 0xffffffffffffffef#64 1#1).2.c = 1#1 ↔ 16 ≤ x.toNat := by
  exact SszArm.Memcpy.carry16 x

theorem prefix_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base) :
    read_pc (prefix_state s) = if 16 ≤ (r (.GPR 2) s).toNat then base + 16#64
      else base + 32#64 := by
  change r .PC s = base at hp
  by_cases h : 16 ≤ (r (.GPR 2) s).toNat
  all_goals
    simp_all (config := {decide := true, instances := true})
      [prefix_state, instruction, state_simp_rules, apply_ite, carry16_immediate,
       BitVec.add_assoc]

theorem tail_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base + 32#64) :
    read_pc (instruction 8 s) = if r (.GPR 2) s = 0#64 then base + 48#64
      else base + 36#64 := by
  change r .PC s = base + 32#64 at hp
  simp (config := {decide := true}) [instruction, state_simp_rules, hp,
    BitVec.add_assoc] <;> split <;> bv_omega

theorem bulk_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base + 16#64) :
    read_pc (bulk s) = if 16 ≤ (r (.GPR 2) s - 16#64).toNat then base + 16#64
      else base + 32#64 := by
  change r .PC s = base + 16#64 at hp
  by_cases h : 16 ≤ (r (.GPR 2) s - 16#64).toNat
  all_goals
    simp_all (config := {decide := true, instances := true})
      [bulk, instruction, state_simp_rules, apply_ite, carry16_immediate, BitVec.add_assoc]
    try bv_omega

theorem byte_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base + 36#64) :
    read_pc (byte s) = if r (.GPR 2) s - 1#64 = 0#64 then base + 48#64
      else base + 36#64 := by
  change r .PC s = base + 36#64 at hp
  simp (config := {decide := true}) [byte, instruction, state_simp_rules, hp,
    BitVec.add_assoc] <;> split <;> bv_omega


theorem step_code (s : ArmState) (base : BitVec 64) (k : Nat) (hk : k < 13)
    (hc : CodeAt s base program) (hp : read_pc s = base + BitVec.ofNat 64 (4 * k))
    (he : read_err s = .None) : stepi s = instruction k s := by
  apply step_word s k hk he
  rw [hp]
  exact hc k hk

theorem run_prefix (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None) :
    run (prefix_fuel (r (.GPR 2) s).toNat) s = prefix_state s := by
  have h0 := step_code s base 0 (by decide) hc (by simpa using hp) he
  change r .PC s = base at hp
  have h1 := step_code (instruction 0 s) base 1 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp])
    (by simpa only [instruction_err] using he)
  have h2 := step_code (instruction 1 (instruction 0 s)) base 2 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  by_cases hlarge : 16 ≤ (r (.GPR 2) s).toNat
  · have h3 := step_code (instruction 2 (instruction 1 (instruction 0 s)))
      base 3 (by decide)
      (by simpa only [CodeAt, instruction_program] using hc)
      (by
        have hl : 16 ≤ (r (.GPR 2#5) s).toNat := hlarge
        simp (config := {decide := true, instances := true})
          [instruction, state_simp_rules, hp, carry16_immediate, hl,
            BitVec.add_assoc])
      (by simpa only [instruction_err] using he)
    simp only [prefix_fuel, prefix_state, if_pos hlarge]
    change stepi (stepi (stepi (stepi s))) = _
    rw [h0, h1, h2, h3]
  · simp only [prefix_fuel, prefix_state, if_neg hlarge]
    change stepi (stepi (stepi s)) = _
    rw [h0, h1, h2]

theorem run_bulk (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base + 16#64)
    (he : read_err s = .None) : run 4 s = bulk s := by
  change r .PC s = base + 16#64 at hp
  have h4 := step_code s base 4 (by decide) hc hp he
  have h5 := step_code (instruction 4 s) base 5 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  have h6 := step_code (instruction 5 (instruction 4 s)) base 6 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  have h7 := step_code (instruction 6 (instruction 5 (instruction 4 s))) base 7 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  change stepi (stepi (stepi (stepi s))) = _
  rw [h4, h5, h6, h7]
  rfl

theorem run_byte (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base + 36#64)
    (he : read_err s = .None) : run 3 s = byte s := by
  change r .PC s = base + 36#64 at hp
  have h9 := step_code s base 9 (by decide) hc hp he
  have h10 := step_code (instruction 9 s) base 10 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  have h11 := step_code (instruction 10 (instruction 9 s)) base 11 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  change stepi (stepi (stepi s)) = _
  rw [h9, h10, h11]
  rfl

private theorem run_iterate (f : ArmState → ArmState) (cycles : Nat)
    (Inv : Nat → ArmState → Prop)
    (advance : ∀ q s, Inv (q + 1) s → run cycles s = f s ∧ Inv q (f s))
    (q : Nat) (s : ArmState) (h : Inv q s) :
    run (cycles * q) s = iterate f q s ∧ Inv 0 (iterate f q s) := by
  induction q generalizing s with
  | zero => exact ⟨rfl, h⟩
  | succ q ih =>
    have hs := advance q s h
    have ht := ih (s := f s) hs.2
    refine ⟨?_, ht.2⟩
    rw [Nat.mul_succ, Nat.add_comm (cycles * q) cycles, run_plus, hs.1]
    exact ht.1

/-- The bulk loop terminates after exactly `q` four-instruction iterations. -/
theorem bulk_loop (q t : Nat) (ht : t < 16) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (he : read_err s = .None)
    (hn : (r (.GPR 2) s).toNat = 16 * q + t)
    (hp : read_pc s = if q = 0 then base + 32#64 else base + 16#64) :
    run (4 * q) s = iterate bulk q s ∧
    read_pc (iterate bulk q s) = base + 32#64 ∧
    (r (.GPR 2) (iterate bulk q s)).toNat = t := by
  let Inv := fun q s => CodeAt s base program ∧ read_err s = .None ∧
    (r (.GPR 2) s).toNat = 16 * q + t ∧
    read_pc s = if q = 0 then base + 32#64 else base + 16#64
  have advance : ∀ q s, Inv (q + 1) s → run 4 s = bulk s ∧ Inv q (bulk s) := by
    intro p u hu
    rcases hu with ⟨huc, hue, hun, hup⟩
    have hup' : read_pc u = base + 16#64 := by simpa using hup
    have huc' : CodeAt (bulk u) base program := by
      simpa only [bulk, CodeAt, instruction_program] using huc
    have hue' : read_err (bulk u) = .None := by
      simpa only [bulk, instruction_err] using hue
    have hun' : (r (.GPR 2) (bulk u)).toNat = 16 * p + t := by
      rw [(bulk_data u).2.1]
      bv_omega
    have hup'' : read_pc (bulk u) = if p = 0 then base + 32#64 else base + 16#64 := by
      rw [bulk_pc u base hup']
      have hv : (r (.GPR 2) u - 16#64).toNat = 16 * p + t := by bv_omega
      rw [hv]
      by_cases hq : p = 0 <;> simp [hq] <;> omega
    exact ⟨run_bulk u base huc hup' hue, huc', hue', hun', hup''⟩
  have hstart : Inv q s := by
    refine ⟨hc, he, hn, hp⟩
  have hout := run_iterate bulk 4 Inv advance q s hstart
  exact ⟨hout.1, by simpa using hout.2.2.2.2, by simpa using hout.2.2.2.1⟩

/-- The byte loop terminates after exactly `t` three-instruction iterations. -/
theorem byte_loop (t : Nat) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (he : read_err s = .None)
    (hn : (r (.GPR 2) s).toNat = t)
    (hp : read_pc s = if t = 0 then base + 48#64 else base + 36#64) :
    run (3 * t) s = iterate byte t s ∧ read_pc (iterate byte t s) = base + 48#64 ∧
    r (.GPR 2) (iterate byte t s) = 0#64 := by
  let Inv := fun t s => CodeAt s base program ∧ read_err s = .None ∧
    (r (.GPR 2) s).toNat = t ∧
    read_pc s = if t = 0 then base + 48#64 else base + 36#64
  have advance : ∀ t s, Inv (t + 1) s → run 3 s = byte s ∧ Inv t (byte s) := by
    intro p u hu
    rcases hu with ⟨huc, hue, hun, hup⟩
    have hup' : read_pc u = base + 36#64 := by simpa using hup
    have huc' : CodeAt (byte u) base program := by
      simpa only [byte, CodeAt, instruction_program] using huc
    have hue' : read_err (byte u) = .None := by
      simpa only [byte, instruction_err] using hue
    have hun' : (r (.GPR 2) (byte u)).toNat = p := by
      rw [(byte_data u).2.1]
      bv_omega
    have hup'' : read_pc (byte u) = if p = 0 then base + 48#64 else base + 36#64 := by
      rw [byte_pc u base hup']
      have hz : r (.GPR 2) u - 1#64 = 0#64 ↔ p = 0 := by bv_omega
      simp only [hz]
    exact ⟨run_byte u base huc hup' hue, huc', hue', hun', hup''⟩
  have hstart : Inv t s := by
    refine ⟨hc, he, hn, hp⟩
  have hout := run_iterate byte 3 Inv advance t s hstart
  exact ⟨hout.1, by simpa using hout.2.2.2.2, BitVec.eq_of_toNat_eq hout.2.2.2.1⟩


/-- The frame preserves x0, x1, x4–x30, SP and q1–q31. -/
theorem result_frame (s : ArmState) (f : StateField) (hf : Preserved f) :
    r f (result s) = r f s := by
  unfold result
  rw [instruction_frame _ _ _ hf,
    iterate_frame byte _ byte_frame _ _ hf,
    instruction_frame _ _ _ hf,
    iterate_frame bulk _ bulk_frame _ _ hf,
    prefix_state_frame _ _ hf]

/-- RET returns the original caller address in x30. -/
theorem result_return (s : ArmState) : read_pc (result s) = r (.GPR 30) s := by
  have ret_pc (t : ArmState) : read_pc (instruction 12 t) = r (.GPR 30) t := by
    simp (config := {instances := true}) [instruction, state_simp_rules]
  unfold result
  rw [ret_pc]
  rw [iterate_frame byte _ byte_frame _ (.GPR 30) (by simp [Preserved]),
    instruction_frame _ _ (.GPR 30) (by simp [Preserved]),
    iterate_frame bulk _ bulk_frame _ (.GPR 30) (by simp [Preserved]),
    prefix_state_frame _ (.GPR 30) (by simp [Preserved])]

/-- The instruction map is unchanged. -/
theorem result_program (s : ArmState) : (result s).program = s.program := by
  unfold result
  rw [instruction_program,
    iterate_program byte _ (by intro t; simp only [byte, instruction_program]),
    instruction_program,
    iterate_program bulk _ (by intro t; simp only [bulk, instruction_program])]
  exact prefix_state_program s

/-- Total execution of the complete literal memset, including its return. -/
theorem program_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None) :
    run (fuel (r (.GPR 2) s).toNat) s = result s := by
  let n := (r (.GPR 2) s).toNat
  let q := n / 16
  let t := n % 16
  let sb := iterate bulk q (prefix_state s)
  have hprefix := run_prefix s base hc hp he
  have hpc_prefix : read_pc (prefix_state s) = if q = 0 then base + 32#64 else base + 16#64 := by
    rw [prefix_pc s base hp]
    change (if 16 ≤ n then _ else _) = _
    by_cases hn16 : 16 ≤ n <;>
      simp [q, hn16, show (n / 16 = 0 ↔ ¬ 16 ≤ n) by omega]
  have hcode_prefix : CodeAt (prefix_state s) base program := by
    simpa only [CodeAt, prefix_state_program] using hc
  have herr_prefix : read_err (prefix_state s) = .None := by
    exact (prefix_state_frame s .ERR trivial).trans he
  have hn : (r (.GPR 2) (prefix_state s)).toNat = 16 * q + t := by
    rw [(prefix_state_data s).2.2.1]
    dsimp [q, t, n]
    omega
  obtain ⟨hbr, hbpc, hbnout⟩ := bulk_loop q t (by dsimp [t]; omega) (prefix_state s) base
    hcode_prefix herr_prefix hn hpc_prefix
  have hbprog : sb.program = s.program := by
    dsimp [sb]
    rw [iterate_program bulk _ (by intro t; simp only [bulk, instruction_program]),
      prefix_state_program]
  have hberr : read_err sb = .None := by
    change r .ERR sb = .None
    dsimp [sb]
    rw [iterate_frame bulk _ bulk_frame _ .ERR trivial, prefix_state_frame _ .ERR trivial]
    exact he
  have hs8 := step_code sb base 8 (by decide)
    (by simpa only [CodeAt, hbprog] using hc) hbpc hberr
  have htc : CodeAt (instruction 8 sb) base program := by
    simpa only [CodeAt, instruction_program, hbprog] using hc
  have hte : read_err (instruction 8 sb) = .None := by
    simpa only [instruction_err] using hberr
  have htp : read_pc (instruction 8 sb) = if t = 0 then base + 48#64 else base + 36#64 := by
    rw [tail_pc sb base hbpc]
    have hz : r (.GPR 2) sb = 0#64 ↔ t = 0 := by
      change (r (.GPR 2) sb).toNat = t at hbnout
      bv_omega
    simp only [hz]
  have htr := byte_loop t (instruction 8 sb) base htc hte
    (by simpa (config := {decide := true}) [instruction, state_simp_rules] using hbnout) htp
  have hbyte_prog : (iterate byte t (instruction 8 sb)).program = s.program := by
    rw [iterate_program byte _ (by intro u; simp only [byte, instruction_program]),
      instruction_program, hbprog]
  have hbyte_err : read_err (iterate byte t (instruction 8 sb)) = .None := by
    change r .ERR _ = .None
    rw [iterate_frame byte _ byte_frame _ .ERR trivial]
    exact hte
  have hs12 := step_code (iterate byte t (instruction 8 sb)) base 12 (by decide)
    (by simpa only [CodeAt, hbyte_prog] using hc)
    (by simpa using htr.2.1) hbyte_err
  have hsteps : fuel n = prefix_fuel n + (4 * q + (1 + (3 * t + 1))) := by
    simp only [fuel, q, t]
    omega
  change run (fuel n) s = _
  rw [hsteps, run_plus, hprefix, run_plus, hbr, run_plus]
  change run (3 * t + 1) (stepi sb) = _
  rw [hs8, run_plus, htr.1]
  change stepi (iterate byte t (instruction 8 sb)) = _
  exact hs12

/-- Empty memset allows arbitrary pointers and still returns immediately. -/
theorem program_zero (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hn : r (.GPR 2) s = 0#64) :
    (run 5 s).mem = s.mem ∧ read_pc (run 5 s) = r (.GPR 30) s := by
  have hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64 := by
    rw [hn]
    bv_omega
  have hr := program_run s base hc hp he
  rw [hn] at hr
  simp [fuel, prefix_fuel] at hr
  rw [hr]
  refine ⟨?_, result_return s⟩
  funext a
  rw [result_memory s hdst, hn]
  simp only [image, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
  rw [if_neg (by omega)]

/-- Complete refinement and frame. -/
theorem program_correct (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64) :
    let final := run (fuel (r (.GPR 2) s).toNat) s
    read_err final = .None ∧ read_pc final = r (.GPR 30) s ∧
    r (.GPR 0) final = r (.GPR 0) s ∧ final.program = s.program ∧
    (∀ f, Preserved f → r f final = r f s) ∧
    (∀ a, final.mem a = image s.mem (r (.GPR 0) s) ((r (.GPR 1) s).setWidth 8)
      (r (.GPR 2) s).toNat a) := by
  dsimp only
  rw [program_run s base hc hp he]
  refine ⟨?_, ?_, result_frame s (.GPR 0) (by simp [Preserved]), result_program s,
    (fun f hf => result_frame s f hf), result_memory s hdst⟩
  · exact (result_frame s .ERR trivial).trans he
  · exact result_return s
end SszArm.Memset
