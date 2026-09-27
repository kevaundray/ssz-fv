import SszArm.Memcmp

namespace SszArm.Memcmp

open BitVec

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem step_code (s : ArmState) (base : BitVec 64) (k : Nat) (hk : k < 10)
    (hc : CodeAt s base program) (hp : read_pc s = base + BitVec.ofNat 64 (4 * k))
    (he : read_err s = .None) : stepi s = instruction k s := by
  apply step_word s k hk he
  rw [hp]
  exact hc k hk

theorem entry_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base) :
    read_pc (entry s) = if r (.GPR 2) s = 0#64 then base + 36#64 else base + 12#64 := by
  change r .PC s = base at hp
  simp (config := {decide := true}) [entry, instruction, state_simp_rules, hp,
    BitVec.add_assoc]

theorem entry_data (s : ArmState) :
    r (.GPR 0) (entry s) = 0#64 ∧ r (.GPR 1) (entry s) = r (.GPR 1) s ∧
    r (.GPR 2) (entry s) = r (.GPR 2) s ∧ r (.GPR 3) (entry s) = r (.GPR 0) s := by
  simp (config := {decide := true}) [entry, instruction, state_simp_rules]

theorem compare_data (s : ArmState) (a b : BitVec 8)
    (ha : s.mem.read_bytes 1 (r (.GPR 3) s) = a)
    (hb : s.mem.read_bytes 1 (r (.GPR 1) s) = b) :
    r (.GPR 0) (compare s) = (a.setWidth 32 - b.setWidth 32).setWidth 64 ∧
    r (.GPR 1) (compare s) = r (.GPR 1) s + 1#64 ∧
    r (.GPR 2) (compare s) = r (.GPR 2) s ∧
    r (.GPR 3) (compare s) = r (.GPR 3) s + 1#64 := by
  have ha' : s.mem.read_bytes 1 (r (.GPR 3#5) s) = a := ha
  have hb' : s.mem.read_bytes 1 (r (.GPR 1#5) s) = b := hb
  simp (config := {decide := true}) [compare, instruction, state_simp_rules,
    Memory.State.read_mem_bytes_eq_mem_read_bytes, ha', hb', apply_ite, bitvec_rules]

theorem compare_pc (s : ArmState) (base : BitVec 64) (a b : BitVec 8)
    (hp : read_pc s = base + 12#64)
    (ha : s.mem.read_bytes 1 (r (.GPR 3) s) = a)
    (hb : s.mem.read_bytes 1 (r (.GPR 1) s) = b) :
    read_pc (compare s) = if a = b then base + 28#64 else base + 36#64 := by
  change r .PC s = base + 12#64 at hp
  have heq : a.setWidth 32 = b.setWidth 32 ↔ a = b := by bv_omega
  have ha' : s.mem.read_bytes 1 (r (.GPR 3#5) s) = a := ha
  have hb' : s.mem.read_bytes 1 (r (.GPR 1#5) s) = b := hb
  simp (config := {decide := true}) [compare, instruction, state_simp_rules,
    Memory.State.read_mem_bytes_eq_mem_read_bytes, ha', hb', hp, sub_equal,
    heq, BitVec.add_assoc, apply_ite, bitvec_rules]

theorem advance_pc (s : ArmState) (base : BitVec 64) (hp : read_pc s = base + 28#64) :
    read_pc (advance s) = if r (.GPR 2) s - 1#64 = 0#64 then base + 36#64
      else base + 12#64 := by
  change r .PC s = base + 28#64 at hp
  simp (config := {decide := true}) [advance, instruction, state_simp_rules, hp,
    BitVec.add_assoc] <;> split <;> bv_omega

theorem advance_data (s : ArmState) :
    r (.GPR 0) (advance s) = r (.GPR 0) s ∧
    r (.GPR 1) (advance s) = r (.GPR 1) s ∧
    r (.GPR 2) (advance s) = r (.GPR 2) s - 1#64 ∧
    r (.GPR 3) (advance s) = r (.GPR 3) s := by
  simp (config := {decide := true}) [advance, instruction, state_simp_rules]

theorem run_entry (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None) :
    run 3 s = entry s := by
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

theorem run_compare (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base + 12#64)
    (he : read_err s = .None) : run 4 s = compare s := by
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
  change stepi (stepi (stepi (stepi s))) = _
  rw [h3, h4, h5, h6]
  rfl

theorem run_advance (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base + 28#64)
    (he : read_err s = .None) : run 2 s = advance s := by
  change r .PC s = base + 28#64 at hp
  have h7 := step_code s base 7 (by decide) hc hp he
  have h8 := step_code (instruction 7 s) base 8 (by decide)
    (by simpa only [CodeAt, instruction_program] using hc)
    (by simp (config := {decide := true}) [instruction, state_simp_rules, hp,
      BitVec.add_assoc])
    (by simpa only [instruction_err] using he)
  change stepi (stepi s) = _
  rw [h7, h8]
  rfl

/-- A finite run of actual ISA steps. Composition is exactly `run_plus`. -/
def Reaches (s t : ArmState) : Prop := ∃ n, run n s = t

theorem reaches_refl (s : ArmState) : Reaches s s := ⟨0, rfl⟩
theorem reaches_trans {s t u : ArmState} (h : Reaches s t) (h' : Reaches t u) : Reaches s u := by
  rcases h with ⟨n, hn⟩
  rcases h' with ⟨m, hm⟩
  exact ⟨n + m, by rw [run_plus, hn, hm]⟩

end SszArm.Memcmp
