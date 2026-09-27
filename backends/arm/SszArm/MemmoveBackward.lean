import SszArm.MemcpyProofs

/-!
Backward internal block of `asm/arm/memmove.s`. Instruction and data maps are
separate; total ordinary memory does not model mappings, permissions, devices,
alignment traps, or concurrent interference. No data non-overlap is assumed.
Only supported post-index loads/stores are used. Pointer setup is outside loops;
registers may wrap when not dereferenced, including below the last copied byte.
-/
namespace SszArm.Memmove.Backward

open BitVec
open SszArm.Memcpy (carry16)

/-- Encoded directly from A64 fields, using signed post-index imm9 -16 and -1. -/
def program : List (BitVec 32) :=
  [0x8b020021#32, 0x8b020003#32, 0xf100405f#32, 0x54000183#32,
   0xd1004021#32, 0xd1004063#32, 0x3cdf0420#32, 0x3c9f0460#32,
   0xd1004042#32, 0xf100405f#32, 0x54ffff82#32, 0xb4000142#32,
   0x91003c21#32, 0x91003c63#32, 0x14000003#32,
   0xd1000421#32, 0xd1000463#32, 0x385ff424#32, 0x381ff464#32,
   0xd1000442#32, 0xb5ffffa2#32, 0xd65f03c0#32]

/-- Each entire vector is loaded before its store. The negative post-index
update positions the register for the next iteration, not the current access. -/
def instruction (k : Nat) (s : ArmState) : ArmState :=
  match k with
  | 0 => w .PC (read_pc s + 4#64)
      (w (.GPR 1) (r (.GPR 1) s + r (.GPR 2) s) s)
  | 1 => w .PC (read_pc s + 4#64)
      (w (.GPR 3) (r (.GPR 0) s + r (.GPR 2) s) s)
  | 2 | 9 => write_pstate (AddWithCarry (r (.GPR 2) s) (~~~16#64) 1#1).2
      (w .PC (read_pc s + 4#64) s)
  | 3 => if r (.FLAG .C) s = 1#1 then w .PC (read_pc s + 4#64) s
      else w .PC (read_pc s + 48#64) s
  | 4 => w .PC (read_pc s + 4#64) (w (.GPR 1) (r (.GPR 1) s - 16#64) s)
  | 5 => w .PC (read_pc s + 4#64) (w (.GPR 3) (r (.GPR 3) s - 16#64) s)
  | 6 => w .PC (read_pc s + 4#64)
      (w (.GPR 1) (r (.GPR 1) s - 16#64)
        (w (.SFP 0) (read_mem_bytes 16 (r (.GPR 1) s) s) s))
  | 7 => w .PC (read_pc s + 4#64)
      (w (.GPR 3) (r (.GPR 3) s - 16#64)
        (write_mem_bytes 16 (r (.GPR 3) s) (r (.SFP 0) s) s))
  | 8 => w (.GPR 2) (r (.GPR 2) s - 16#64) (w .PC (read_pc s + 4#64) s)
  | 10 => if r (.FLAG .C) s = 1#1 then w .PC (read_pc s - 16#64) s
      else w .PC (read_pc s + 4#64) s
  | 11 => w .PC (if r (.GPR 2) s = 0#64 then read_pc s + 40#64
      else read_pc s + 4#64) s
  | 12 => w .PC (read_pc s + 4#64) (w (.GPR 1) (r (.GPR 1) s + 15#64) s)
  | 13 => w .PC (read_pc s + 4#64) (w (.GPR 3) (r (.GPR 3) s + 15#64) s)
  | 14 => w .PC (read_pc s + 12#64) s
  | 15 => w .PC (read_pc s + 4#64) (w (.GPR 1) (r (.GPR 1) s - 1#64) s)
  | 16 => w .PC (read_pc s + 4#64) (w (.GPR 3) (r (.GPR 3) s - 1#64) s)
  | 17 => w .PC (read_pc s + 4#64)
      (w (.GPR 1) (r (.GPR 1) s - 1#64)
        (w (.GPR 4) ((read_mem_bytes 1 (r (.GPR 1) s) s).setWidth 64) s))
  | 18 => w .PC (read_pc s + 4#64)
      (w (.GPR 3) (r (.GPR 3) s - 1#64)
        (write_mem_bytes 1 (r (.GPR 3) s) ((r (.GPR 4) s).setWidth 8) s))
  | 19 => w (.GPR 2) (r (.GPR 2) s - 1#64) (w .PC (read_pc s + 4#64) s)
  | 20 => w .PC (if r (.GPR 2) s = 0#64 then read_pc s + 4#64
      else read_pc s - 12#64) s
  | 21 => w .PC (r (.GPR 30) s) s
  | _ => s

/-- Kernel-reducible decoding of every literal backward instruction. -/
theorem step_word (s : ArmState) (k : Nat) (hk : k < 22)
    (herr : read_err s = .None)
    (hf : s.program.find? (read_pc s) = some program[k]) :
    stepi s = instruction k s := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _
  | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _
  | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ =>
    simp [program] at hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ herr rfl
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true}) [instruction, exec_inst,
      state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
      BitVec.sub_eq_add_neg]
    all_goals first
      | rfl
      | exact w_of_w_commute (by decide)
  | k + 22, hk => omega

def prefix_entry (s : ArmState) : ArmState :=
  instruction 3 (instruction 2 (instruction 1 (instruction 0 s)))

def prefix_state (s : ArmState) : ArmState :=
  if 16 ≤ (r (.GPR 2) s).toNat then instruction 5 (instruction 4 (prefix_entry s))
  else prefix_entry s

def prefix_fuel (n : Nat) : Nat := if 16 ≤ n then 6 else 4

def bulk (s : ArmState) : ArmState :=
  instruction 10 (instruction 9 (instruction 8 (instruction 7 (instruction 6 s))))

def byte (s : ArmState) : ArmState :=
  instruction 20 (instruction 19 (instruction 18 (instruction 17 s)))

/-- After bulk, post-index pointers need +15; without bulk, endpoints need -1.
The zero-remainder bulk path skips adjustment and every byte access. The small
path is entered only with nonzero count, as proved by the outer dispatcher. -/
def tail_state (big : Bool) (s : ArmState) : ArmState :=
  if big then
    if r (.GPR 2) s = 0#64 then instruction 11 s
    else instruction 14 (instruction 13 (instruction 12 (instruction 11 s)))
  else instruction 16 (instruction 15 s)

def tail_fuel (big : Bool) (n : Nat) : Nat :=
  if big then (if n = 0 then 1 else 4) else 2

def iterate (f : ArmState → ArmState) : Nat → ArmState → ArmState
  | 0, s => s
  | n + 1, s => iterate f n (f s)

/-- Stronger than the AAPCS64 frame: q0 is the sole SIMD clobber. -/
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
    read_err (instruction k s) = read_err s := instruction_frame k s .ERR trivial

theorem prefix_state_frame (s : ArmState) (f : StateField) (h : Preserved f) :
    r f (prefix_state s) = r f s := by
  simp [prefix_state, prefix_entry, instruction_frame _ _ _ h, apply_ite]

theorem prefix_state_program (s : ArmState) : (prefix_state s).program = s.program := by
  simp [prefix_state, prefix_entry, instruction_program, apply_ite]

theorem bulk_frame (s : ArmState) (f : StateField) (h : Preserved f) :
    r f (bulk s) = r f s := by
  simp only [bulk, instruction_frame _ _ _ h]

theorem byte_frame (s : ArmState) (f : StateField) (h : Preserved f) :
    r f (byte s) = r f s := by
  simp only [byte, instruction_frame _ _ _ h]

theorem tail_state_frame (big : Bool) (s : ArmState) (f : StateField) (h : Preserved f) :
    r f (tail_state big s) = r f s := by
  simp [tail_state, instruction_frame _ _ _ h, apply_ite]

theorem tail_state_program (big : Bool) (s : ArmState) :
    (tail_state big s).program = s.program := by
  simp [tail_state, instruction_program, apply_ite]

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
    r (.GPR 1) (prefix_state s) = r (.GPR 1) s + r (.GPR 2) s -
      (if 16 ≤ (r (.GPR 2) s).toNat then 16#64 else 0#64) ∧
    r (.GPR 2) (prefix_state s) = r (.GPR 2) s ∧
    r (.GPR 3) (prefix_state s) = r (.GPR 0) s + r (.GPR 2) s -
      (if 16 ≤ (r (.GPR 2) s).toNat then 16#64 else 0#64) := by
  by_cases h : 16 ≤ (r (.GPR 2) s).toNat
  · simp only [prefix_state, if_pos h]
    simp_all (config := {decide := true, instances := true})
      [prefix_entry, instruction, state_simp_rules, apply_ite]
  · simp only [prefix_state, if_neg h]
    simp_all (config := {decide := true, instances := true})
      [prefix_entry, instruction, state_simp_rules, apply_ite]

theorem bulk_data (s : ArmState) :
    (bulk s).mem = (write_mem_bytes 16 (r (.GPR 3) s)
      (read_mem_bytes 16 (r (.GPR 1) s) s) s).mem ∧
    r (.GPR 1) (bulk s) = r (.GPR 1) s - 16#64 ∧
    r (.GPR 2) (bulk s) = r (.GPR 2) s - 16#64 ∧
    r (.GPR 3) (bulk s) = r (.GPR 3) s - 16#64 := by
  constructor
  · simp [bulk, instruction, state_simp_rules, apply_ite,
      Memory.write_mem_bytes_eq_mem_write_bytes]
  · simp [bulk, instruction, state_simp_rules, apply_ite]

theorem byte_data (s : ArmState) :
    (byte s).mem = (write_mem_bytes 1 (r (.GPR 3) s)
      (read_mem_bytes 1 (r (.GPR 1) s) s) s).mem ∧
    r (.GPR 1) (byte s) = r (.GPR 1) s - 1#64 ∧
    r (.GPR 2) (byte s) = r (.GPR 2) s - 1#64 ∧
    r (.GPR 3) (byte s) = r (.GPR 3) s - 1#64 := by
  constructor
  · simp [byte, instruction, state_simp_rules,
      BitVec.setWidth_setWidth_of_le, Memory.write_mem_bytes_eq_mem_write_bytes]
  · simp [byte, instruction, state_simp_rules]

theorem tail_state_data (big : Bool) (s : ArmState) :
    (tail_state big s).mem = s.mem ∧
    r (.GPR 2) (tail_state big s) = r (.GPR 2) s ∧
    (r (.GPR 2) s ≠ 0#64 →
      r (.GPR 1) (tail_state big s) =
        (if big then r (.GPR 1) s + 15#64 else r (.GPR 1) s - 1#64) ∧
      r (.GPR 3) (tail_state big s) =
        (if big then r (.GPR 3) s + 15#64 else r (.GPR 3) s - 1#64)) := by
  cases big <;> by_cases hz : r (.GPR 2) s = 0#64
  all_goals
    simp only [tail_state, hz, Bool.false_eq_true, ite_false, ite_true]
    simp_all (config := {decide := true, instances := true})
      [instruction, state_simp_rules]

/-- Exact terminating-state expression for nonzero internal entries. The outer
dispatcher returns before entering this block when the original count is zero. -/
def result (s : ArmState) : ArmState :=
  let n := (r (.GPR 2) s).toNat
  instruction 21 (iterate byte (n % 16)
    (tail_state (decide (16 ≤ n)) (iterate bulk (n / 16) (prefix_state s))))

def fuel (n : Nat) : Nat :=
  prefix_fuel n + (5 * (n / 16) + (tail_fuel (decide (16 ≤ n)) (n % 16) +
    (4 * (n % 16) + 1)))

end SszArm.Memmove.Backward
