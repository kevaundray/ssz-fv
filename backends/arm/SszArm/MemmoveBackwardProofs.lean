import SszArm.MemmoveBackward

namespace SszArm.Memmove.Backward

open BitVec

theorem step_code (s : ArmState) (base : BitVec 64) (k : Nat) (hk : k < 22)
    (hc : CodeAt s base program) (hp : read_pc s = base + BitVec.ofNat 64 (4 * k))
    (he : read_err s = .None) : stepi s = instruction k s := by
  apply step_word s k hk he
  rw [hp]
  exact hc k hk

private theorem carry16_immediate (x : BitVec 64) :
    (AddWithCarry x 0xffffffffffffffef#64 1#1).2.c = 1#1 ↔ 16 ≤ x.toNat := by
  exact SszArm.Memcpy.carry16 x

theorem run_prefix_entry (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None) :
    run 4 s = prefix_entry s := by
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
  have h3 := step_code (instruction 2 (instruction 1 (instruction 0 s))) base 3 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  change stepi (stepi (stepi (stepi s))) = _
  rw [h0, h1, h2, h3]
  rfl

theorem prefix_entry_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base) :
    read_pc (prefix_entry s) = if 16 ≤ (r (.GPR 2) s).toNat then base + 16#64
      else base + 60#64 := by
  change r .PC s = base at hp
  by_cases h : 16 ≤ (r (.GPR 2) s).toNat
  all_goals
    simp_all (config := {decide := true, instances := true})
      [prefix_entry, instruction, state_simp_rules, apply_ite, carry16_immediate,
        BitVec.add_assoc]

theorem prefix_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base) :
    read_pc (prefix_state s) = if 16 ≤ (r (.GPR 2) s).toNat then base + 24#64
      else base + 60#64 := by
  change r .PC s = base at hp
  by_cases h : 16 ≤ (r (.GPR 2) s).toNat
  all_goals
    simp_all (config := {decide := true, instances := true})
      [prefix_state, prefix_entry, instruction, state_simp_rules, apply_ite,
        carry16_immediate, BitVec.add_assoc]

theorem run_prefix (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None) :
    run (prefix_fuel (r (.GPR 2) s).toNat) s = prefix_state s := by
  by_cases hn : 16 ≤ (r (.GPR 2) s).toNat
  · have hep : read_pc (prefix_entry s) = base + 16#64 := by
      simpa only [if_pos hn] using prefix_entry_pc s base hp
    have hec : CodeAt (prefix_entry s) base program := by
      simpa only [prefix_entry, CodeAt, instruction_program] using hc
    have hee : read_err (prefix_entry s) = .None := by
      simpa only [prefix_entry, instruction_err] using he
    have h4 := step_code (prefix_entry s) base 4 (by decide) hec hep hee
    change r .PC (prefix_entry s) = base + 16#64 at hep
    have h5 := step_code (instruction 4 (prefix_entry s)) base 5 (by decide)
      (by simpa only [CodeAt, instruction_program] using hec)
      (by simp (config := {decide := true}) [instruction, state_simp_rules, hep,
        BitVec.add_assoc])
      (by simpa only [instruction_err] using hee)
    simp only [prefix_fuel, prefix_state, if_pos hn]
    rw [show (6 : Nat) = 4 + 2 from rfl, run_plus, run_prefix_entry s base hc hp he]
    change stepi (stepi (prefix_entry s)) = _
    rw [h4, h5]
  · simpa only [prefix_fuel, prefix_state, if_neg hn] using
      run_prefix_entry s base hc hp he

theorem run_bulk (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base + 24#64)
    (he : read_err s = .None) : run 5 s = bulk s := by
  change r .PC s = base + 24#64 at hp
  have h6 := step_code s base 6 (by decide) hc hp he
  have h7 := step_code (instruction 6 s) base 7 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  have h8 := step_code (instruction 7 (instruction 6 s)) base 8 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  have h9 := step_code (instruction 8 (instruction 7 (instruction 6 s))) base 9 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  have h10 := step_code (instruction 9 (instruction 8 (instruction 7 (instruction 6 s))))
    base 10 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  change stepi (stepi (stepi (stepi (stepi s)))) = _
  rw [h6, h7, h8, h9, h10]
  rfl

theorem run_tail (big : Bool) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program)
    (hp : read_pc s = if big then base + 44#64 else base + 60#64)
    (he : read_err s = .None) :
    run (tail_fuel big (r (.GPR 2) s).toNat) s = tail_state big s := by
  cases big with
  | false =>
    change r .PC s = base + 60#64 at hp
    have h15 := step_code s base 15 (by decide) hc hp he
    have h16 := step_code (instruction 15 s) base 16 (by decide)
      (by simpa only [CodeAt, instruction_program] using hc)
      (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
        BitVec.add_assoc])
      (by simpa only [instruction_err] using he)
    change stepi (stepi s) = instruction 16 (instruction 15 s)
    rw [h15, h16]
  | true =>
    change r .PC s = base + 44#64 at hp
    change run (tail_fuel true (r (.GPR (2#5)) s).toNat) s = tail_state true s
    have h11 := step_code s base 11 (by decide) hc hp he
    by_cases hz : r (.GPR (2#5)) s = 0#64
    · have hcount : (r (.GPR (2#5)) s).toNat = 0 := by rw [hz]; rfl
      rw [show tail_fuel true (r (.GPR (2#5)) s).toNat = 1 by simp [tail_fuel, hcount]]
      change stepi s = _
      simpa [tail_state, hz] using h11
    · have hcount : (r (.GPR (2#5)) s).toNat ≠ 0 := by bv_omega
      have h12 := step_code (instruction 11 s) base 12 (by decide)
        (by simpa only [CodeAt, instruction_program] using hc)
        (by simp_all (config := {decide := true})
          [instruction, state_simp_rules, BitVec.add_assoc])
        (by simpa only [instruction_err] using he)
      have h13 := step_code (instruction 12 (instruction 11 s)) base 13 (by decide)
        (by simpa only [CodeAt, instruction_program] using hc)
        (by simp_all (config := {decide := true})
          [instruction, state_simp_rules, BitVec.add_assoc])
        (by simpa only [instruction_err] using he)
      have h14 := step_code (instruction 13 (instruction 12 (instruction 11 s))) base 14
        (by decide)
        (by simpa only [CodeAt, instruction_program] using hc)
        (by simp_all (config := {decide := true})
          [instruction, state_simp_rules, BitVec.add_assoc])
        (by simpa only [instruction_err] using he)
      rw [show tail_fuel true (r (.GPR (2#5)) s).toNat = 4 by simp [tail_fuel, hcount]]
      change stepi (stepi (stepi (stepi s))) = _
      rw [h11, h12, h13, h14]
      simp [tail_state, hz]

theorem tail_pc (big : Bool) (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = if big then base + 44#64 else base + 60#64)
    (hsmall : big = false → r (.GPR 2) s ≠ 0#64) :
    read_pc (tail_state big s) =
      if r (.GPR 2) s = 0#64 then base + 84#64 else base + 68#64 := by
  cases big with
  | false =>
    have hn : r (.GPR (2#5)) s ≠ 0#64 := hsmall rfl
    change r .PC s = base + 60#64 at hp
    simp_all (config := {decide := true}) [tail_state, instruction, state_simp_rules,
      BitVec.add_assoc]
  | true =>
    change r .PC s = base + 44#64 at hp
    by_cases hz : r (.GPR (2#5)) s = 0#64 <;>
      simp_all (config := {decide := true}) [tail_state, instruction, state_simp_rules,
        BitVec.add_assoc]

theorem run_byte (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base + 68#64)
    (he : read_err s = .None) : run 4 s = byte s := by
  change r .PC s = base + 68#64 at hp
  have h17 := step_code s base 17 (by decide) hc hp he
  have h18 := step_code (instruction 17 s) base 18 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  have h19 := step_code (instruction 18 (instruction 17 s)) base 19 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  have h20 := step_code (instruction 19 (instruction 18 (instruction 17 s))) base 20
    (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  change stepi (stepi (stepi (stepi s))) = _
  rw [h17, h18, h19, h20]
  rfl

theorem bulk_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base + 24#64) :
    read_pc (bulk s) = if 16 ≤ (r (.GPR 2) s - 16#64).toNat then base + 24#64
      else base + 44#64 := by
  change r .PC s = base + 24#64 at hp
  by_cases h : 16 ≤ (r (.GPR 2) s - 16#64).toNat
  all_goals
    simp_all (config := {decide := true, instances := true})
      [bulk, instruction, state_simp_rules, apply_ite, carry16_immediate, BitVec.add_assoc]
    try bv_omega

theorem byte_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base + 68#64) :
    read_pc (byte s) = if r (.GPR 2) s - 1#64 = 0#64 then base + 84#64
      else base + 68#64 := by
  change r .PC s = base + 68#64 at hp
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
    (hp : read_pc s = if q = 0 then base + 44#64 else base + 24#64) :
    run (5 * q) s = iterate bulk q s ∧
    read_pc (iterate bulk q s) = base + 44#64 ∧
    (r (.GPR 2) (iterate bulk q s)).toNat = t := by
  let Inv := fun q s => CodeAt s base program ∧ read_err s = .None ∧
    (r (.GPR 2) s).toNat = 16 * q + t ∧
    read_pc s = if q = 0 then base + 44#64 else base + 24#64
  have advance : ∀ q s, Inv (q + 1) s → run 5 s = bulk s ∧ Inv q (bulk s) := by
    intro p u hu
    rcases hu with ⟨huc, hue, hun, hup⟩
    have hup' : read_pc u = base + 24#64 := by simpa using hup
    have huc' : CodeAt (bulk u) base program := by
      simpa only [bulk, CodeAt, instruction_program] using huc
    have hue' : read_err (bulk u) = .None := by
      simpa only [bulk, instruction_err] using hue
    have hun' : (r (.GPR 2) (bulk u)).toNat = 16 * p + t := by
      rw [(bulk_data u).2.2.1]
      bv_omega
    have hup'' : read_pc (bulk u) = if p = 0 then base + 44#64 else base + 24#64 := by
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
    (hp : read_pc s = if t = 0 then base + 84#64 else base + 68#64) :
    run (4 * t) s = iterate byte t s ∧ read_pc (iterate byte t s) = base + 84#64 ∧
    r (.GPR 2) (iterate byte t s) = 0#64 := by
  let Inv := fun t s => CodeAt s base program ∧ read_err s = .None ∧
    (r (.GPR 2) s).toNat = t ∧
    read_pc s = if t = 0 then base + 84#64 else base + 68#64
  have advance : ∀ t s, Inv (t + 1) s → run 4 s = byte s ∧ Inv t (byte s) := by
    intro p u hu
    rcases hu with ⟨huc, hue, hun, hup⟩
    have hup' : read_pc u = base + 68#64 := by simpa using hup
    have huc' : CodeAt (byte u) base program := by
      simpa only [byte, CodeAt, instruction_program] using huc
    have hue' : read_err (byte u) = .None := by
      simpa only [byte, instruction_err] using hue
    have hun' : (r (.GPR 2) (byte u)).toNat = p := by
      rw [(byte_data u).2.2.1]
      bv_omega
    have hup'' : read_pc (byte u) = if p = 0 then base + 84#64 else base + 68#64 := by
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
    tail_state_frame _ _ _ hf, iterate_frame bulk _ bulk_frame _ _ hf,
    prefix_state_frame _ _ hf]

theorem result_return (s : ArmState) : read_pc (result s) = r (.GPR 30) s := by
  have ret_pc (t : ArmState) : read_pc (instruction 21 t) = r (.GPR 30) t := by
    simp (config := {instances := true}) [instruction, state_simp_rules]
  unfold result
  rw [ret_pc]
  rw [iterate_frame byte _ byte_frame _ (.GPR 30) (by simp [Preserved]),
    tail_state_frame _ _ (.GPR 30) (by simp [Preserved]),
    iterate_frame bulk _ bulk_frame _ (.GPR 30) (by simp [Preserved]),
    prefix_state_frame _ (.GPR 30) (by simp [Preserved])]

theorem result_program (s : ArmState) : (result s).program = s.program := by
  unfold result
  rw [instruction_program, iterate_program byte _ (by intro s; simp only [byte, instruction_program]),
    tail_state_program, iterate_program bulk _ (by intro s; simp only [bulk, instruction_program]),
    prefix_state_program]

/-- Execution of the complete literal backward block, including its return.
The outer dispatcher excludes zero before entering this internal block; no lower
bound on either input pointer or on the nonzero runtime length is required. -/
theorem program_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hn : r (.GPR 2) s ≠ 0#64) :
    run (fuel (r (.GPR 2) s).toNat) s = result s := by
  let n := (r (.GPR 2) s).toNat
  let sb := iterate bulk (n / 16) (prefix_state s)
  let st := tail_state (decide (16 ≤ n)) sb
  have hnonzero : n ≠ 0 := by
    change (r (.GPR 2) s).toNat ≠ 0
    bv_omega
  have hbc : CodeAt (prefix_state s) base program := by
    simpa only [CodeAt, prefix_state_program] using hc
  have hbe : read_err (prefix_state s) = .None := by
    change r .ERR (prefix_state s) = .None
    rw [prefix_state_frame _ .ERR trivial]
    exact he
  have hbn : (r (.GPR 2) (prefix_state s)).toNat = 16 * (n / 16) + n % 16 := by
    rw [(prefix_state_data s).2.2.1]
    dsimp [n]; omega
  have hprefixpc : read_pc (prefix_state s) =
      if 16 ≤ n then base + 24#64 else base + 60#64 := prefix_pc s base hp
  have hbulk : run (5 * (n / 16)) (prefix_state s) = sb ∧
      read_pc sb = (if 16 ≤ n then base + 44#64 else base + 60#64) ∧
      (r (.GPR 2) sb).toNat = n % 16 := by
    by_cases hbig : 16 ≤ n
    · have hq : n / 16 ≠ 0 := by omega
      have hbp : read_pc (prefix_state s) =
          if n / 16 = 0 then base + 44#64 else base + 24#64 := by
        simpa only [if_neg hq, if_pos hbig] using hprefixpc
      obtain ⟨hbr, hbpc, hbnout⟩ := bulk_loop (n / 16) (n % 16) (by omega)
        (prefix_state s) base hbc hbe hbn hbp
      exact ⟨hbr, by simpa only [if_pos hbig] using hbpc, hbnout⟩
    · have hq : n / 16 = 0 := by omega
      have ht : n % 16 = n := Nat.mod_eq_of_lt (by omega)
      have hbr : run (5 * (n / 16)) (prefix_state s) = sb := by
        simpa only [sb, hq, Nat.mul_zero, iterate] using
          (show run 0 (prefix_state s) = prefix_state s from rfl)
      have hbpc : read_pc sb = base + 60#64 := by
        simpa only [sb, hq, iterate, if_neg hbig] using hprefixpc
      have hbnout : (r (.GPR 2) sb).toNat = n % 16 := by
        change (r (.GPR 2) (iterate bulk (n / 16) (prefix_state s))).toNat = n % 16
        rw [hq]
        change (r (.GPR 2) (prefix_state s)).toNat = n % 16
        rw [(prefix_state_data s).2.2.1]
        exact ht.symm
      exact ⟨hbr, by simpa only [if_neg hbig] using hbpc, hbnout⟩
  obtain ⟨hbr, hbpc, hbnout⟩ := hbulk
  have hbprog : sb.program = s.program := by
    dsimp [sb]
    rw [iterate_program bulk _ (by intro s; simp only [bulk, instruction_program]),
      prefix_state_program]
  have hberr : read_err sb = .None := by
    change r .ERR sb = .None
    dsimp [sb]
    rw [iterate_frame bulk _ bulk_frame _ .ERR trivial, prefix_state_frame _ .ERR trivial]
    exact he
  have hsmall : decide (16 ≤ n) = false → r (.GPR 2) sb ≠ 0#64 := by
    intro hsmall hz
    have hlt : ¬16 ≤ n := by simpa only [decide_eq_false_iff_not] using hsmall
    have hzero : (r (.GPR 2) sb).toNat = 0 := by rw [hz]; rfl
    have ht : n % 16 = n := Nat.mod_eq_of_lt (by omega)
    omega
  have htailpc : read_pc sb =
      if decide (16 ≤ n) then base + 44#64 else base + 60#64 := by
    simpa using hbpc
  have htailrun : run (tail_fuel (decide (16 ≤ n)) (n % 16)) sb = st := by
    simpa only [hbnout] using run_tail (decide (16 ≤ n)) sb base
      (by simpa only [CodeAt, hbprog] using hc) htailpc hberr
  have htc : CodeAt st base program := by
    simpa only [st, CodeAt, tail_state_program, hbprog] using hc
  have hte : read_err st = .None := by
    change r .ERR st = .None
    dsimp [st]
    rw [tail_state_frame _ _ .ERR trivial]
    exact hberr
  have htn : (r (.GPR 2) st).toNat = n % 16 := by
    exact (congrArg BitVec.toNat (tail_state_data (decide (16 ≤ n)) sb).2.1).trans hbnout
  have htp : read_pc st = if n % 16 = 0 then base + 84#64 else base + 68#64 := by
    have hz : r (.GPR 2) sb = 0#64 ↔ n % 16 = 0 := by bv_omega
    simpa only [hz] using tail_pc (decide (16 ≤ n)) sb base htailpc hsmall
  obtain ⟨htr, htpc, _⟩ := byte_loop (n % 16) st base htc hte htn htp
  have htprog : (iterate byte (n % 16) st).program = s.program := by
    rw [iterate_program byte _ (by intro s; simp only [byte, instruction_program])]
    dsimp [st]
    rw [tail_state_program, hbprog]
  have hterr : read_err (iterate byte (n % 16) st) = .None := by
    change r .ERR _ = .None
    rw [iterate_frame byte _ byte_frame _ .ERR trivial]
    exact hte
  have hret := step_code (iterate byte (n % 16) st) base 21 (by decide)
    (by simpa only [CodeAt, htprog] using hc) htpc hterr
  change run (fuel n) s = _
  rw [fuel, run_plus, run_prefix s base hc hp he, run_plus, hbr, run_plus,
    htailrun, run_plus, htr]
  change stepi (iterate byte (n % 16) st) = _
  exact hret

end SszArm.Memmove.Backward
