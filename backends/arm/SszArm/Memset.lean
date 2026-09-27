import Arm.Insts.DPSFP.Advanced_simd_copy
import SszArm.Memcpy

/-!
The literal instructions of `asm/arm/memset.s`. The instruction map is separate
from the total ordinary byte memory in LNSym; mapping, permissions, devices and
concurrent interference are not represented by this contract.
-/
namespace SszArm.Memset

open BitVec

set_option maxRecDepth 8192

/-- Object words, in increasing address order. -/
def program : List (BitVec 32) :=
  [0xaa0003e3#32, 0xf100405f#32, 0x540000c3#32, 0x4e010c20#32,
   0x3c810460#32, 0xd1004042#32, 0xf100405f#32, 0x54ffffa2#32,
   0xb4000082#32, 0x38001461#32, 0xd1000442#32, 0xb5ffffc2#32,
   0xd65f03c0#32]

/-- The pinned DUP-general operation, at precisely sixteen eight-bit lanes. -/
def repeatedByte (b : BitVec 8) : BitVec 128 :=
  DPSFP.dup_aux 0 16 8 b (BitVec.zero 128)
/-- Small-step effects. All memory accesses retain the pinned model operations. -/
def instruction (k : Nat) (s : ArmState) : ArmState :=
  match k with
  | 0 => w .PC (read_pc s + 4#64) (w (.GPR 3) (r (.GPR 0) s) s)
  | 1 | 6 => write_pstate (AddWithCarry (r (.GPR 2) s) (~~~16#64) 1#1).2
      (w .PC (read_pc s + 4#64) s)
  | 2 => if r (.FLAG .C) s = 1#1 then w .PC (read_pc s + 4#64) s
      else w .PC (read_pc s + 24#64) s
  | 3 => w .PC (read_pc s + 4#64)
      (w (.SFP 0) (repeatedByte ((r (.GPR 1) s).setWidth 8)) s)
  | 4 => w .PC (read_pc s + 4#64)
      (w (.GPR 3) (r (.GPR 3) s + 16#64)
        (write_mem_bytes 16 (r (.GPR 3) s) (r (.SFP 0) s) s))
  | 5 => w (.GPR 2) (r (.GPR 2) s - 16#64) (w .PC (read_pc s + 4#64) s)
  | 7 => if r (.FLAG .C) s = 1#1 then w .PC (read_pc s - 12#64) s
      else w .PC (read_pc s + 4#64) s
  | 8 => w .PC (if r (.GPR 2) s = 0#64 then read_pc s + 16#64
      else read_pc s + 4#64) s
  | 9 => w .PC (read_pc s + 4#64)
      (w (.GPR 3) (r (.GPR 3) s + 1#64)
        (write_mem_bytes 1 (r (.GPR 3) s) ((r (.GPR 1) s).setWidth 8) s))
  | 10 => w (.GPR 2) (r (.GPR 2) s - 1#64) (w .PC (read_pc s + 4#64) s)
  | 11 => w .PC (if r (.GPR 2) s = 0#64 then read_pc s + 4#64
      else read_pc s - 8#64) s
  | 12 => w .PC (r (.GPR 30) s) s
  | _ => s

/-- Decoding and executing every literal word, without a native decision oracle. -/
theorem step_word (s : ArmState) (k : Nat) (hk : k < 13)
    (herr : read_err s = .None)
    (hf : s.program.find? (read_pc s) = some program[k]) :
    stepi s = instruction k s := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _
  | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ =>
    simp [program] at hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ herr rfl
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true}) [instruction, exec_inst,
      state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
      BitVec.sub_eq_add_neg]
    all_goals first
      | rfl
      | exact w_of_w_commute (by decide)

set_option maxHeartbeats 1000000 in
@[simp] theorem repeatedByte_extract (b : BitVec 8) (i : Nat) (hi : i < 16) :
    (repeatedByte b).extractLsByte i = b := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ =>
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
      simp (config := {decide := true}) [repeatedByte, DPSFP.dup_aux,
        elem_set, BitVec.partInstall, BitVec.extractLsByte, bitvec_rules]
  | i + 16, h => omega

/-- The short path branches around DUP; only the bulk path initializes q0. -/
def prefix_state (s : ArmState) : ArmState :=
  let guarded := instruction 2 (instruction 1 (instruction 0 s))
  if 16 ≤ (r (.GPR 2) s).toNat then instruction 3 guarded else guarded

def prefix_fuel (n : Nat) : Nat := if 16 ≤ n then 4 else 3
def bulk (s : ArmState) : ArmState := instruction 7 (instruction 6 (instruction 5 (instruction 4 s)))
def byte (s : ArmState) : ArmState := instruction 11 (instruction 10 (instruction 9 s))

def iterate (f : ArmState → ArmState) : Nat → ArmState → ArmState
  | 0, s => s
  | n + 1, s => iterate f n (f s)

/-- Fields not clobbered by the AAPCS64 implementation; stronger than the ABI frame. -/
def Preserved : StateField → Prop
  | .GPR i => i ≠ 2#5 ∧ i ≠ 3#5
  | .SFP i => i ≠ 0#5
  | .PC | .FLAG _ => False
  | .ERR => True

/-- All instructions preserve every field outside their explicit clobber set. -/
theorem instruction_frame (k : Nat) (s : ArmState) (f : StateField)
    (h : Preserved f) : r f (instruction k s) = r f s := by
  cases f <;> simp only [Preserved] at h
  · rcases h with ⟨h2, h3⟩
    unfold instruction
    split <;> simp [state_simp_rules, h2, h3, apply_ite]
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
  unfold prefix_state
  split <;> simp only [instruction_frame _ _ _ h]

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


theorem prefix_state_program (s : ArmState) :
    (prefix_state s).program = s.program := by
  by_cases h : 16 ≤ (r (.GPR 2) s).toNat
  · simp only [prefix_state, if_pos h, instruction_program]
  · simp only [prefix_state, if_neg h, instruction_program]

theorem prefix_state_data (s : ArmState) :
    (prefix_state s).mem = s.mem ∧
    r (.GPR 1) (prefix_state s) = r (.GPR 1) s ∧
    r (.GPR 2) (prefix_state s) = r (.GPR 2) s ∧
    r (.GPR 3) (prefix_state s) = r (.GPR 0) s ∧
    (16 ≤ (r (.GPR 2) s).toNat →
      r (.SFP 0) (prefix_state s) = repeatedByte ((r (.GPR 1) s).setWidth 8)) := by
  unfold prefix_state
  split <;> rename_i h
  all_goals simp_all (config := {instances := true})
    [instruction, state_simp_rules, apply_ite] <;> (intro hlarge; omega)

theorem bulk_data (s : ArmState) :
    (bulk s).mem = (write_mem_bytes 16 (r (.GPR 3) s) (r (.SFP 0) s) s).mem ∧
    r (.GPR 2) (bulk s) = r (.GPR 2) s - 16#64 ∧
    r (.GPR 3) (bulk s) = r (.GPR 3) s + 16#64 ∧
    r (.SFP 0) (bulk s) = r (.SFP 0) s := by
  constructor
  · simp [bulk, instruction, state_simp_rules, apply_ite,
      Memory.write_mem_bytes_eq_mem_write_bytes]
  · simp [bulk, instruction, state_simp_rules, apply_ite]

theorem byte_data (s : ArmState) :
    (byte s).mem = (write_mem_bytes 1 (r (.GPR 3) s)
      ((r (.GPR 1) s).setWidth 8) s).mem ∧
    r (.GPR 2) (byte s) = r (.GPR 2) s - 1#64 ∧
    r (.GPR 3) (byte s) = r (.GPR 3) s + 1#64 ∧
    r (.SFP 0) (byte s) = r (.SFP 0) s := by
  constructor
  · simp [byte, instruction, state_simp_rules,
      Memory.write_mem_bytes_eq_mem_write_bytes]
  · simp [byte, instruction, state_simp_rules]
/-- The exact terminating-state expression, with no postulated loop behavior. -/
def result (s : ArmState) : ArmState :=
  let n := (r (.GPR 2) s).toNat
  let q := n / 16
  let t := n % 16
  instruction 12 (iterate byte t (instruction 8 (iterate bulk q (prefix_state s))))

/-- Exact fuel for the full control flow. -/
def fuel (n : Nat) : Nat := prefix_fuel n + 2 + 4 * (n / 16) + 3 * (n % 16)

end SszArm.Memset
