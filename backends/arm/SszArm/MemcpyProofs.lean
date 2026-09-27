import SszArm.MemcpyMemory

namespace SszArm.Memcpy

open BitVec

theorem step_code (s : ArmState) (base : BitVec 64) (k : Nat) (hk : k < 14)
    (hc : CodeAt s base program) (hp : read_pc s = base + BitVec.ofNat 64 (4 * k))
    (he : read_err s = .None) : stepi s = instruction k s := by
  apply step_word s k hk he
  rw [hp]
  exact hc k hk

theorem run_prefix (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None) :
    run 3 s = prefix_state s := by
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
  change stepi (stepi (stepi s)) = _
  rw [h0, h1, h2]
  rfl

theorem run_bulk (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base + 12#64)
    (he : read_err s = .None) : run 5 s = bulk s := by
  change r .PC s = base + 12#64 at hp
  have h3 := step_code s base 3 (by decide) hc hp he
  have h4 := step_code (instruction 3 s) base 4 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  have h5 := step_code (instruction 4 (instruction 3 s)) base 5 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  have h6 := step_code (instruction 5 (instruction 4 (instruction 3 s))) base 6 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  have h7 := step_code (instruction 6 (instruction 5 (instruction 4 (instruction 3 s))))
    base 7 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  change stepi (stepi (stepi (stepi (stepi s)))) = _
  rw [h3, h4, h5, h6, h7]
  rfl

theorem run_byte (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base + 36#64)
    (he : read_err s = .None) : run 4 s = byte s := by
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
  have h12 := step_code (instruction 11 (instruction 10 (instruction 9 s))) base 12 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  change stepi (stepi (stepi (stepi s))) = _
  rw [h9, h10, h11, h12]
  rfl

private theorem carry16_immediate (x : BitVec 64) :
    (AddWithCarry x 0xffffffffffffffef#64 1#1).2.c = 1#1 ↔ 16 ≤ x.toNat := by
  exact carry16 x

theorem prefix_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base) :
    read_pc (prefix_state s) = if 16 ≤ (r (.GPR 2) s).toNat then base + 12#64
      else base + 32#64 := by
  change r .PC s = base at hp
  by_cases h : 16 ≤ (r (.GPR 2) s).toNat
  all_goals
    simp_all (config := {decide := true, instances := true})
      [prefix_state, instruction, state_simp_rules, apply_ite, carry16_immediate, BitVec.add_assoc]

theorem bulk_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base + 12#64) :
    read_pc (bulk s) = if 16 ≤ (r (.GPR 2) s - 16#64).toNat then base + 12#64
      else base + 32#64 := by
  change r .PC s = base + 12#64 at hp
  by_cases h : 16 ≤ (r (.GPR 2) s - 16#64).toNat
  all_goals
    simp_all (config := {decide := true, instances := true})
      [bulk, instruction, state_simp_rules, apply_ite, carry16_immediate, BitVec.add_assoc]
    try bv_omega

theorem byte_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base + 36#64) :
    read_pc (byte s) = if r (.GPR 2) s - 1#64 = 0#64 then base + 52#64
      else base + 36#64 := by
  change r .PC s = base + 36#64 at hp
  simp (config := {decide := true}) [byte, instruction, state_simp_rules, hp,
    BitVec.add_assoc]
  split <;> bv_omega

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

/-- The SIMD loop terminates after exactly `q` five-instruction iterations. -/
theorem bulk_loop (q t : Nat) (ht : t < 16) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (he : read_err s = .None)
    (hn : (r (.GPR 2) s).toNat = 16 * q + t)
    (hp : read_pc s = if q = 0 then base + 32#64 else base + 12#64) :
    run (5 * q) s = iterate bulk q s ∧
    read_pc (iterate bulk q s) = base + 32#64 ∧
    (r (.GPR 2) (iterate bulk q s)).toNat = t := by
  let Inv := fun q s => CodeAt s base program ∧ read_err s = .None ∧
    (r (.GPR 2) s).toNat = 16 * q + t ∧
    read_pc s = if q = 0 then base + 32#64 else base + 12#64
  have advance : ∀ q s, Inv (q + 1) s → run 5 s = bulk s ∧ Inv q (bulk s) := by
    intro p u hu
    rcases hu with ⟨huc, hue, hun, hup⟩
    have hup' : read_pc u = base + 12#64 := by simpa using hup
    have huc' : CodeAt (bulk u) base program := by
      simpa only [bulk, CodeAt, instruction_program] using huc
    have hue' : read_err (bulk u) = .None := by
      simpa only [bulk, instruction_err] using hue
    have hun' : (r (.GPR 2) (bulk u)).toNat = 16 * p + t := by
      rw [(bulk_data u).2.2.1]
      bv_omega
    have hup'' : read_pc (bulk u) = if p = 0 then base + 32#64 else base + 12#64 := by
      rw [bulk_pc u base hup']
      have hv : (r (.GPR 2) u - 16#64).toNat = 16 * p + t := by bv_omega
      rw [hv]
      by_cases hq : p = 0 <;> simp [hq] <;> omega
    exact ⟨run_bulk u base huc hup' hue, huc', hue', hun', hup''⟩
  have hout := run_iterate bulk 5 Inv advance q s ⟨hc, he, hn, hp⟩
  exact ⟨hout.1, by simpa using hout.2.2.2.2, by simpa using hout.2.2.2.1⟩

/-- The byte loop terminates after exactly `t` four-instruction iterations. -/
theorem byte_loop (t : Nat) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (he : read_err s = .None)
    (hn : (r (.GPR 2) s).toNat = t)
    (hp : read_pc s = if t = 0 then base + 52#64 else base + 36#64) :
    run (4 * t) s = iterate byte t s ∧ read_pc (iterate byte t s) = base + 52#64 ∧
    r (.GPR 2) (iterate byte t s) = 0#64 := by
  let Inv := fun t s => CodeAt s base program ∧ read_err s = .None ∧
    (r (.GPR 2) s).toNat = t ∧
    read_pc s = if t = 0 then base + 52#64 else base + 36#64
  have advance : ∀ t s, Inv (t + 1) s → run 4 s = byte s ∧ Inv t (byte s) := by
    intro p u hu
    rcases hu with ⟨huc, hue, hun, hup⟩
    have hup' : read_pc u = base + 36#64 := by simpa using hup
    have huc' : CodeAt (byte u) base program := by
      simpa only [byte, CodeAt, instruction_program] using huc
    have hue' : read_err (byte u) = .None := by
      simpa only [byte, instruction_err] using hue
    have hun' : (r (.GPR 2) (byte u)).toNat = p := by
      rw [(byte_data u).2.2.1]
      bv_omega
    have hup'' : read_pc (byte u) = if p = 0 then base + 52#64 else base + 36#64 := by
      rw [byte_pc u base hup']
      have hz : r (.GPR 2) u - 1#64 = 0#64 ↔ p = 0 := by bv_omega
      simp only [hz]
    exact ⟨run_byte u base huc hup' hue, huc', hue', hun', hup''⟩
  have hout := run_iterate byte 4 Inv advance t s ⟨hc, he, hn, hp⟩
  exact ⟨hout.1, by simpa using hout.2.2.2.2, BitVec.eq_of_toNat_eq hout.2.2.2.1⟩

theorem result_frame (s : ArmState) (f : StateField) (hf : Preserved f) :
    r f (result s) = r f s := by
  unfold result
  rw [instruction_frame _ _ _ hf, iterate_frame byte _ byte_frame _ _ hf,
    instruction_frame _ _ _ hf, iterate_frame bulk _ bulk_frame _ _ hf,
    prefix_state_frame _ _ hf]

theorem result_return (s : ArmState) : read_pc (result s) = r (.GPR 30) s := by
  have ret_pc (t : ArmState) : read_pc (instruction 13 t) = r (.GPR 30) t := by
    simp (config := {instances := true}) [instruction, state_simp_rules]
  unfold result
  rw [ret_pc]
  rw [iterate_frame byte _ byte_frame _ (.GPR 30) (by simp [Preserved]),
    instruction_frame _ _ (.GPR 30) (by simp [Preserved]),
    iterate_frame bulk _ bulk_frame _ (.GPR 30) (by simp [Preserved]),
    prefix_state_frame _ (.GPR 30) (by simp [Preserved])]

theorem result_program (s : ArmState) : (result s).program = s.program := by
  unfold result
  rw [instruction_program, iterate_program byte _ (by intro s; simp only [byte, instruction_program]),
    instruction_program, iterate_program bulk _ (by intro s; simp only [bulk, instruction_program])]
  simp only [prefix_state, instruction_program]

/-- Total execution of the complete literal memcpy, including its return.
No lower bound on the runtime length or the input pointers is required. -/
theorem program_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None) :
    run (fuel (r (.GPR 2) s).toNat) s = result s := by
  let n := (r (.GPR 2) s).toNat
  let sb := iterate bulk (n / 16) (prefix_state s)
  have hbc : CodeAt (prefix_state s) base program := by
    simpa only [prefix_state, CodeAt, instruction_program] using hc
  have hbe : read_err (prefix_state s) = .None := by
    simpa only [prefix_state, instruction_err] using he
  have hbn : (r (.GPR 2) (prefix_state s)).toNat = 16 * (n / 16) + n % 16 := by
    rw [(prefix_state_data s).2.2.1]
    dsimp [n]; omega
  have hbp : read_pc (prefix_state s) = if n / 16 = 0 then base + 32#64 else base + 12#64 := by
    rw [prefix_pc s base hp]
    change (if 16 ≤ n then _ else _) = _
    by_cases hn : 16 ≤ n <;> simp [hn, show (n / 16 = 0 ↔ ¬ 16 ≤ n) by omega]
  obtain ⟨hbr, hbpc, hbnout⟩ := bulk_loop (n / 16) (n % 16) (by omega)
    (prefix_state s) base hbc hbe hbn hbp
  have hbprog : sb.program = s.program := by
    dsimp [sb]
    rw [iterate_program bulk _ (by intro s; simp only [bulk, instruction_program])]
    simp only [prefix_state, instruction_program]
  have hberr : read_err sb = .None := by
    change r .ERR sb = .None
    dsimp [sb]
    rw [iterate_frame bulk _ bulk_frame _ .ERR trivial, prefix_state_frame _ .ERR trivial]
    exact he
  have hs8 := step_code sb base 8 (by decide)
    (by simpa only [CodeAt, hbprog] using hc) hbpc hberr
  have htc : CodeAt (instruction 8 sb) base program := by
    simpa only [CodeAt, instruction_program, hbprog] using hc
  have hte : read_err (instruction 8 sb) = .None := by simpa only [instruction_err] using hberr
  have htn : (r (.GPR 2) (instruction 8 sb)).toNat = n % 16 := by
    simpa (config := {decide := true}) [instruction, state_simp_rules] using hbnout
  change r .PC sb = base + 32#64 at hbpc
  have htp : read_pc (instruction 8 sb) =
      if n % 16 = 0 then base + 52#64 else base + 36#64 := by
    have hz : r (.GPR 2) sb = 0#64 ↔ n % 16 = 0 := by
      change (r (.GPR 2) sb).toNat = n % 16 at hbnout
      bv_omega
    simp_all (config := {decide := true, instances := true})
      [instruction, state_simp_rules, BitVec.add_assoc]
  obtain ⟨htr, htpc, _⟩ := byte_loop (n % 16) (instruction 8 sb) base htc hte htn htp
  have htprog : (iterate byte (n % 16) (instruction 8 sb)).program = s.program := by
    rw [iterate_program byte _ (by intro s; simp only [byte, instruction_program]),
      instruction_program, hbprog]
  have hterr : read_err (iterate byte (n % 16) (instruction 8 sb)) = .None := by
    change r .ERR _ = .None
    rw [iterate_frame byte _ byte_frame _ .ERR trivial]
    exact hte
  have hs13 := step_code (iterate byte (n % 16) (instruction 8 sb)) base 13 (by decide)
    (by simpa only [CodeAt, htprog] using hc) htpc hterr
  have hsteps : fuel n = 3 + (5 * (n / 16) + (1 + (4 * (n % 16) + 1))) := by
    simp only [fuel]; omega
  change run (fuel n) s = _
  rw [hsteps, run_plus, run_prefix s base hc hp he, run_plus, hbr, run_plus]
  change run (4 * (n % 16) + 1) (stepi sb) = _
  rw [hs8, run_plus, htr]
  change stepi (iterate byte (n % 16) (instruction 8 sb)) = _
  exact hs13

/-- Complete refinement and frame, for symbolic length and arbitrary initial bytes.
The frame preserves x0, x5–x30, SP and q1–q31, in particular every AAPCS64
callee-saved register. Source preservation is a consequence of the exact memory
image and disjointness. -/
theorem program_correct (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsrc : (r (.GPR 1) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsep : Disjoint (r (.GPR 0) s) (r (.GPR 1) s) (r (.GPR 2) s).toNat) :
    let final := run (fuel (r (.GPR 2) s).toNat) s
    read_err final = .None ∧ read_pc final = r (.GPR 30) s ∧
    r (.GPR 0) final = r (.GPR 0) s ∧ final.program = s.program ∧
    (∀ f, Preserved f → r f final = r f s) ∧
    (∀ a, final.mem a = image s.mem (r (.GPR 0) s) (r (.GPR 1) s)
      (r (.GPR 2) s).toNat a) := by
  dsimp only
  rw [program_run s base hc hp he]
  refine ⟨?_, ?_, result_frame s (.GPR 0) (by simp [Preserved]), result_program s,
    result_frame s, result_memory s hdst hsrc hsep⟩
  · exact (result_frame s .ERR trivial).trans he
  · exact result_return s

/-- Empty memcpy accesses no data memory and allows arbitrary, including null,
pointers. It still executes the five control/register instructions and returns. -/
theorem program_zero (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hn : r (.GPR 2) s = 0#64) :
    (run 5 s).mem = s.mem ∧ read_pc (run 5 s) = r (.GPR 30) s := by
  have hr := program_run s base hc hp he
  simp only [hn, BitVec.toNat_ofNat, fuel] at hr
  rw [hr]
  refine ⟨?_, result_return s⟩
  have hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2^64 := by
    rw [hn]
    bv_omega
  have hsrc : (r (.GPR 1) s).toNat + (r (.GPR 2) s).toNat ≤ 2^64 := by
    rw [hn]
    bv_omega
  have hsep : Disjoint (r (.GPR 0) s) (r (.GPR 1) s) (r (.GPR 2) s).toNat := by
    unfold Disjoint
    rw [hn]
    bv_omega
  funext a
  rw [result_memory s hdst hsrc hsep, hn]
  simp only [image, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
  rw [if_neg (by omega)]

end SszArm.Memcpy

