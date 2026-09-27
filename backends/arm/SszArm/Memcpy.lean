import SszArm.Proofs

/-!
The literal instructions of `asm/arm/memcpy.s`.  The instruction map is separate
from the total ordinary byte memory in LNSym; mapping, permissions, devices and
concurrent interference are not represented by this contract.
-/
namespace SszArm.Memcpy

open BitVec

/-- Object words, in increasing address order. -/
def program : List (BitVec 32) :=
  [0xaa0003e3#32, 0xf100405f#32, 0x540000c3#32, 0x3cc10420#32,
   0x3c810460#32, 0xd1004042#32, 0xf100405f#32, 0x54ffff82#32,
   0xb40000a2#32, 0x38401424#32, 0x38001464#32, 0xd1000442#32,
   0xb5ffffa2#32, 0xd65f03c0#32]

/-- Small-step effects. All memory accesses retain the pinned model operations. -/
def instruction (k : Nat) (s : ArmState) : ArmState :=
  match k with
  | 0 => w .PC (read_pc s + 4#64) (w (.GPR 3) (r (.GPR 0) s) s)
  | 1 | 6 => write_pstate (AddWithCarry (r (.GPR 2) s) (~~~16#64) 1#1).2
      (w .PC (read_pc s + 4#64) s)
  | 2 => if r (.FLAG .C) s = 1#1 then w .PC (read_pc s + 4#64) s
      else w .PC (read_pc s + 24#64) s
  | 3 => w .PC (read_pc s + 4#64)
      (w (.GPR 1) (r (.GPR 1) s + 16#64)
        (w (.SFP 0) (read_mem_bytes 16 (r (.GPR 1) s) s) s))
  | 4 => w .PC (read_pc s + 4#64)
      (w (.GPR 3) (r (.GPR 3) s + 16#64)
        (write_mem_bytes 16 (r (.GPR 3) s) (r (.SFP 0) s) s))
  | 5 => w (.GPR 2) (r (.GPR 2) s - 16#64) (w .PC (read_pc s + 4#64) s)
  | 7 => if r (.FLAG .C) s = 1#1 then w .PC (read_pc s - 16#64) s
      else w .PC (read_pc s + 4#64) s
  | 8 => w .PC (if r (.GPR 2) s = 0#64 then read_pc s + 20#64
      else read_pc s + 4#64) s
  | 9 => w .PC (read_pc s + 4#64)
      (w (.GPR 1) (r (.GPR 1) s + 1#64)
        (w (.GPR 4) ((read_mem_bytes 1 (r (.GPR 1) s) s).setWidth 64) s))
  | 10 => w .PC (read_pc s + 4#64)
      (w (.GPR 3) (r (.GPR 3) s + 1#64)
        (write_mem_bytes 1 (r (.GPR 3) s) ((r (.GPR 4) s).setWidth 8) s))
  | 11 => w (.GPR 2) (r (.GPR 2) s - 1#64) (w .PC (read_pc s + 4#64) s)
  | 12 => w .PC (if r (.GPR 2) s = 0#64 then read_pc s + 4#64
      else read_pc s - 12#64) s
  | 13 => w .PC (r (.GPR 30) s) s
  | _ => s

/-- Decoding and executing every literal word, without a native decision oracle. -/
theorem step_word (s : ArmState) (k : Nat) (hk : k < 14)
    (herr : read_err s = .None)
    (hf : s.program.find? (read_pc s) = some program[k]) :
    stepi s = instruction k s := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _
  | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ =>
    simp [program] at hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ herr rfl
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true}) [instruction, exec_inst,
      state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
      BitVec.sub_eq_add_neg]
    all_goals first
      | rfl
      | exact w_of_w_commute (by decide)

private theorem wide_add_nat (x y : BitVec 64) (c : BitVec 1) :
    (x.setWidth 65 + y.setWidth 65 + c.setWidth 65).toNat =
      x.toNat + y.toNat + c.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  have hc := c.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add]
  simp only [BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 65),
    BitVec.toNat_setWidth_of_le (by decide : 1 ≤ 65)]
  have hxy : x.toNat + y.toNat < 2^65 := by omega
  rw [Nat.mod_eq_of_lt hxy]
  exact Nat.mod_eq_of_lt (by omega)

/-- The carry used by both unsigned branches is exactly the unsigned comparison. -/
theorem carry16 (x : BitVec 64) :
    (AddWithCarry x (~~~16#64) 1#1).2.c = 1#1 ↔ 16 ≤ x.toNat := by
  let u : BitVec 65 := x.setWidth 65 + (~~~16#64).setWidth 65 + (1#1).setWidth 65
  have hu : u.toNat = x.toNat + 18446744073709551600 := by
    dsimp only [u]
    rw [wide_add_nat, BitVec.toNat_not, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.add_assoc]
  have hc : (u.setWidth 64 |>.setWidth 65) = u ↔ x.toNat < 16 := by
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth] at hn
      rw [hu] at hn
      omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      rw [hu]
      omega
  simp only [AddWithCarry, make_pstate]
  change (if (u.setWidth 64 |>.setWidth 65) = u then 0#1 else 1#1) = 1#1 ↔ _
  by_cases h : (u.setWidth 64 |>.setWidth 65) = u
  · rw [if_pos h]
    have hn := hc.mp h
    have hz : (0#1 : BitVec 1) ≠ 1#1 := by decide
    exact ⟨fun he => False.elim (hz he), fun he => False.elim ((Nat.not_le_of_lt hn) he)⟩
  · rw [if_neg h]
    have hn : 16 ≤ x.toNat :=
      Nat.le_of_not_gt (fun hn => h (hc.mpr hn))
    exact ⟨fun _ => hn, fun _ => rfl⟩

def prefix_state (s : ArmState) : ArmState := instruction 2 (instruction 1 (instruction 0 s))
def bulk (s : ArmState) : ArmState :=
  instruction 7 (instruction 6 (instruction 5 (instruction 4 (instruction 3 s))))
def byte (s : ArmState) : ArmState :=
  instruction 12 (instruction 11 (instruction 10 (instruction 9 s)))

def iterate (f : ArmState → ArmState) : Nat → ArmState → ArmState
  | 0, s => s
  | n + 1, s => iterate f n (f s)

/-- Fields not clobbered by the AAPCS64 implementation; stronger than the ABI frame. -/
def Preserved : StateField → Prop
  | .GPR i => i ≠ 1#5 ∧ i ≠ 2#5 ∧ i ≠ 3#5 ∧ i ≠ 4#5
  | .SFP i => i ≠ 0#5
  | .PC | .FLAG _ => False
  | .ERR => True

theorem instruction_frame (k : Nat) (s : ArmState) (f : StateField)
    (h : Preserved f) : r f (instruction k s) = r f s := by
  cases f <;> simp only [Preserved] at h
  · rcases h with ⟨h1, h2, h3, h4⟩
    unfold instruction
    split <;> simp [state_simp_rules, h1, h2, h3, h4, apply_ite]
  · unfold instruction
    split <;> simp [state_simp_rules, h, apply_ite]
  · unfold instruction
    split <;> simp [state_simp_rules, apply_ite]

theorem instruction_program (k : Nat) (s : ArmState) :
    (instruction k s).program = s.program := by
  unfold instruction
  split <;> simp [state_simp_rules, apply_ite]

theorem instruction_err (k : Nat) (s : ArmState) :
    read_err (instruction k s) = read_err s :=
  instruction_frame k s .ERR trivial

theorem prefix_state_frame (s : ArmState) (f : StateField) (h : Preserved f) :
    r f (prefix_state s) = r f s := by
  simp only [prefix_state, instruction_frame _ _ _ h]

theorem bulk_frame (s : ArmState) (f : StateField) (h : Preserved f) :
    r f (bulk s) = r f s := by
  simp only [bulk, instruction_frame _ _ _ h]

theorem byte_frame (s : ArmState) (f : StateField) (h : Preserved f) :
    r f (byte s) = r f s := by
  simp only [byte, instruction_frame _ _ _ h]

theorem iterate_frame (f : ArmState → ArmState) (n : Nat)
    (h : ∀ s field, Preserved field → r field (f s) = r field s)
    (s : ArmState) (field : StateField) (hf : Preserved field) :
    r field (iterate f n s) = r field s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [iterate, ih, h s field hf]

theorem iterate_program (f : ArmState → ArmState) (n : Nat)
    (h : ∀ s, (f s).program = s.program) (s : ArmState) :
    (iterate f n s).program = s.program := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [iterate, ih, h]

theorem prefix_state_data (s : ArmState) :
    (prefix_state s).mem = s.mem ∧
    r (.GPR 1) (prefix_state s) = r (.GPR 1) s ∧
    r (.GPR 2) (prefix_state s) = r (.GPR 2) s ∧
    r (.GPR 3) (prefix_state s) = r (.GPR 0) s := by
  simp [prefix_state, instruction, state_simp_rules, apply_ite]

theorem bulk_data (s : ArmState) :
    (bulk s).mem = (write_mem_bytes 16 (r (.GPR 3) s)
      (read_mem_bytes 16 (r (.GPR 1) s) s) s).mem ∧
    r (.GPR 1) (bulk s) = r (.GPR 1) s + 16#64 ∧
    r (.GPR 2) (bulk s) = r (.GPR 2) s - 16#64 ∧
    r (.GPR 3) (bulk s) = r (.GPR 3) s + 16#64 := by
  constructor
  · simp [bulk, instruction, state_simp_rules, apply_ite,
      Memory.write_mem_bytes_eq_mem_write_bytes]
  · simp [bulk, instruction, state_simp_rules, apply_ite]

theorem byte_data (s : ArmState) :
    (byte s).mem = (write_mem_bytes 1 (r (.GPR 3) s)
      (read_mem_bytes 1 (r (.GPR 1) s) s) s).mem ∧
    r (.GPR 1) (byte s) = r (.GPR 1) s + 1#64 ∧
    r (.GPR 2) (byte s) = r (.GPR 2) s - 1#64 ∧
    r (.GPR 3) (byte s) = r (.GPR 3) s + 1#64 := by
  constructor
  · simp [byte, instruction, state_simp_rules,
      BitVec.setWidth_setWidth_of_le, Memory.write_mem_bytes_eq_mem_write_bytes]
  · simp [byte, instruction, state_simp_rules]

/-- The exact terminating-state expression, with no postulated loop behavior. -/
def result (s : ArmState) : ArmState :=
  instruction 13 (iterate byte ((r (.GPR 2) s).toNat % 16)
    (instruction 8 (iterate bulk ((r (.GPR 2) s).toNat / 16) (prefix_state s))))

def fuel (n : Nat) : Nat := 5 + 5 * (n / 16) + 4 * (n % 16)

end SszArm.Memcpy

