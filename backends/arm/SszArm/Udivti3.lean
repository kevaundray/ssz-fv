import SszArm.Proofs

namespace SszArm.Udivti3

open BitVec

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- The 65 object words of `asm/arm/udivti3.s`, including all four returns. -/
def program : List (BitVec 32) :=
  [0xeb03003f#32, 0x540007a3#32, 0x54000068#32, 0xeb02001f#32,
   0x54000743#32, 0xb5000463#32, 0xf100045f#32, 0x540006c0#32,
   0xaa0003e4#32, 0xaa1f03e0#32, 0xd2800807#32, 0xeb02003f#32,
   0x540000c2#32, 0xaa0103e6#32, 0xaa0403e5#32, 0xaa1f03e1#32,
   0xaa1f03e8#32, 0x14000005#32, 0xaa1f03e6#32, 0xaa0103e5#32,
   0xaa1f03e1#32, 0xd2800028#32, 0x8b000000#32, 0xab0500a5#32,
   0xba0600c6#32, 0x54000062#32, 0xeb0200df#32, 0x54000063#32,
   0xcb0200c6#32, 0x91000400#32, 0xf10004e7#32, 0x54fffee1#32,
   0xb40000e8#32, 0xaa0003e1#32, 0xaa1f03e0#32, 0xaa0403e5#32,
   0xd2800807#32, 0xaa1f03e8#32, 0x17fffff0#32, 0xd65f03c0#32,
   0xaa0003e4#32, 0xaa0103e5#32, 0xaa1f03e6#32, 0xaa1f03e0#32,
   0xd2800807#32, 0x8b000000#32, 0xab040084#32, 0xba0500a5#32,
   0x9a0600c6#32, 0xeb0300df#32, 0x54000088#32, 0x540000c3#32,
   0xeb0200bf#32, 0x54000083#32, 0xeb0200a5#32, 0xda0300c6#32,
   0x91000400#32, 0xf10004e7#32, 0x54fffe61#32, 0xaa1f03e1#32,
   0xd65f03c0#32, 0xd65f03c0#32, 0xaa1f03e0#32, 0xaa1f03e1#32,
   0xd65f03c0#32]

/-- Code is separate from the ordinary data memory in the pinned ARM model. -/
def CodeAt (s : ArmState) (base : BitVec 64) : Prop :=
  SszArm.CodeAt s base program

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (i : BitVec 5) (v : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR i) v (next s)

def compare (a b : BitVec 64) (s : ArmState) : ArmState :=
  write_pstate (AddWithCarry a (~~~b) 1#1).2 (next s)

def flagged (i : BitVec 5) (a b : BitVec 64) (c : BitVec 1)
    (s : ArmState) : ArmState :=
  let v := AddWithCarry a b c
  w (.GPR i) v.1 (write_pstate v.2 (next s))

def branch (p : Prop) [Decidable p] (offset : BitVec 64) (s : ArmState) : ArmState :=
  w .PC (read_pc s + if p then offset else 4#64) s

/-- Register and flag effects of the actual decoded instructions. -/
def instruction (k : Nat) (s : ArmState) : ArmState :=
  match k with
  | 0 => compare (r (.GPR 1) s) (r (.GPR 3) s) s
  | 1 => branch (r (.FLAG .C) s ≠ 1#1) 244#64 s
  | 2 => branch (r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1) 12#64 s
  | 3 => compare (r (.GPR 0) s) (r (.GPR 2) s) s
  | 4 => branch (r (.FLAG .C) s ≠ 1#1) 232#64 s
  | 5 => branch (r (.GPR 3) s ≠ 0#64) 140#64 s
  | 6 => compare (r (.GPR 2) s) 1#64 s
  | 7 => branch (r (.FLAG .Z) s = 1#1) 216#64 s
  | 8 | 40 => put 4 (r (.GPR 0) s) s
  | 9 | 34 | 43 | 62 => put 0 0#64 s
  | 10 | 36 | 44 => put 7 64#64 s
  | 11 => compare (r (.GPR 1) s) (r (.GPR 2) s) s
  | 12 => branch (r (.FLAG .C) s = 1#1) 24#64 s
  | 13 => put 6 (r (.GPR 1) s) s
  | 14 | 35 => put 5 (r (.GPR 4) s) s
  | 15 | 20 | 59 | 63 => put 1 0#64 s
  | 16 | 37 => put 8 0#64 s
  | 17 => w .PC (read_pc s + 20#64) s
  | 18 | 42 => put 6 0#64 s
  | 19 | 41 => put 5 (r (.GPR 1) s) s
  | 21 => put 8 1#64 s
  | 22 | 45 => put 0 (r (.GPR 0) s + r (.GPR 0) s) s
  | 23 => flagged 5 (r (.GPR 5) s) (r (.GPR 5) s) 0#1 s
  | 24 => flagged 6 (r (.GPR 6) s) (r (.GPR 6) s) (r (.FLAG .C) s) s
  | 25 => branch (r (.FLAG .C) s = 1#1) 12#64 s
  | 26 => compare (r (.GPR 6) s) (r (.GPR 2) s) s
  | 27 => branch (r (.FLAG .C) s ≠ 1#1) 12#64 s
  | 28 => put 6 (r (.GPR 6) s - r (.GPR 2) s) s
  | 29 | 56 => put 0 (r (.GPR 0) s + 1#64) s
  | 30 | 57 => flagged 7 (r (.GPR 7) s) (~~~1#64) 1#1 s
  | 31 => branch (r (.FLAG .Z) s ≠ 1#1) (-36#64) s
  | 32 => branch (r (.GPR 8) s = 0#64) 28#64 s
  | 33 => put 1 (r (.GPR 0) s) s
  | 38 => w .PC (read_pc s - 64#64) s
  | 39 | 60 | 61 | 64 => w .PC (r (.GPR 30) s) s
  | 46 => flagged 4 (r (.GPR 4) s) (r (.GPR 4) s) 0#1 s
  | 47 => flagged 5 (r (.GPR 5) s) (r (.GPR 5) s) (r (.FLAG .C) s) s
  | 48 => put 6 (AddWithCarry (r (.GPR 6) s) (r (.GPR 6) s) (r (.FLAG .C) s)).1 s
  | 49 => compare (r (.GPR 6) s) (r (.GPR 3) s) s
  | 50 => branch (r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1) 16#64 s
  | 51 => branch (r (.FLAG .C) s ≠ 1#1) 24#64 s
  | 52 => compare (r (.GPR 5) s) (r (.GPR 2) s) s
  | 53 => branch (r (.FLAG .C) s ≠ 1#1) 16#64 s
  | 54 => flagged 5 (r (.GPR 5) s) (~~~r (.GPR 2) s) 1#1 s
  | 55 => put 6 (AddWithCarry (r (.GPR 6) s) (~~~r (.GPR 3) s) (r (.FLAG .C) s)).1 s
  | 58 => branch (r (.FLAG .Z) s ≠ 1#1) (-52#64) s
  | _ => s

/-- Decoder certificates for all 65 emitted words, without a native oracle. -/
theorem step_word (s : ArmState) (k : Nat) (hk : k < 65)
    (he : read_err s = .None)
    (hf : s.program.find? (read_pc s) = some program[k]) :
    stepi s = instruction k s := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _
  | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _
  | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _
  | 32, _ | 33, _ | 34, _ | 35, _ | 36, _ | 37, _ | 38, _ | 39, _
  | 40, _ | 41, _ | 42, _ | 43, _ | 44, _ | 45, _ | 46, _ | 47, _
  | 48, _ | 49, _ | 50, _ | 51, _ | 52, _ | 53, _ | 54, _ | 55, _
  | 56, _ | 57, _ | 58, _ | 59, _ | 60, _ | 61, _ | 62, _ | 63, _ | 64, _ =>
    simp [program] at hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true})
      [instruction, next, put, compare, flagged, branch, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
       BitVec.sub_eq_add_neg, apply_ite]
    all_goals try (split <;> simp_all)
    all_goals apply w_of_w_commute <;> decide
  | k + 65, hk => omega

theorem step_code (s : ArmState) (base : BitVec 64) (k : Nat) (hk : k < 65)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 (4 * k))
    (he : read_err s = .None) : stepi s = instruction k s := by
  apply step_word s k hk he
  rw [hp]
  exact hc k hk

/-- Stronger than AAPCS64: x2, x3, x9--x30, SP and every SIMD register survive. -/
def Preserved : StateField → Prop
  | .GPR i => i ≠ 0#5 ∧ i ≠ 1#5 ∧ i ≠ 4#5 ∧ i ≠ 5#5 ∧
      i ≠ 6#5 ∧ i ≠ 7#5 ∧ i ≠ 8#5
  | .SFP _ | .ERR => True
  | .PC | .FLAG _ => False

instance (f : StateField) : Decidable (Preserved f) := by
  cases f <;> dsimp [Preserved] <;> infer_instance

theorem instruction_frame (k : Nat) (s : ArmState) (f : StateField)
    (h : Preserved f) : r f (instruction k s) = r f s := by
  cases f <;> simp only [Preserved] at h
  · rcases h with ⟨h0, h1, h4, h5, h6, h7, h8⟩
    unfold instruction
    split <;> simp [next, put, compare, flagged, branch, state_simp_rules,
      h0, h1, h4, h5, h6, h7, h8, apply_ite]
  · unfold instruction
    split <;> simp [next, put, compare, flagged, branch, state_simp_rules, apply_ite]
  · unfold instruction
    split <;> simp [next, put, compare, flagged, branch, state_simp_rules, apply_ite]

theorem instruction_program (k : Nat) (s : ArmState) :
    (instruction k s).program = s.program := by
  unfold instruction
  split <;> simp [next, put, compare, flagged, branch, state_simp_rules, apply_ite]

theorem instruction_memory (k : Nat) (s : ArmState) :
    (instruction k s).mem = s.mem := by
  unfold instruction
  split <;> simp [next, put, compare, flagged, branch, state_simp_rules, apply_ite]

theorem instruction_err (k : Nat) (s : ArmState) :
    read_err (instruction k s) = read_err s := instruction_frame k s .ERR trivial

/-- Executing an explicit path never substitutes for instruction execution:
`follows_run` below proves each fetched word and its PC along the path. -/
def block : List Nat → ArmState → ArmState
  | [], s => s
  | k :: ks, s => block ks (instruction k s)

def Follows (base : BitVec 64) : List Nat → ArmState → Prop
  | [], _ => True
  | k :: ks, s => k < 65 ∧ read_pc s = base + BitVec.ofNat 64 (4 * k) ∧
      Follows base ks (instruction k s)

theorem block_append (xs ys : List Nat) (s : ArmState) :
    block (xs ++ ys) s = block ys (block xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem follows_append (base : BitVec 64) (xs ys : List Nat) (s : ArmState) :
    Follows base (xs ++ ys) s ↔ Follows base xs s ∧ Follows base ys (block xs s) := by
  induction xs generalizing s with
  | nil => simp [Follows, block]
  | cons x xs ih => simp only [List.cons_append, Follows, block, ih, _root_.and_assoc]

theorem block_frame (ks : List Nat) (s : ArmState) (f : StateField)
    (hf : Preserved f) : r f (block ks s) = r f s := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih => rw [block, ih, instruction_frame _ _ _ hf]

theorem block_program (ks : List Nat) (s : ArmState) :
    (block ks s).program = s.program := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih => rw [block, ih, instruction_program]

theorem block_memory (ks : List Nat) (s : ArmState) :
    (block ks s).mem = s.mem := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih => rw [block, ih, instruction_memory]

theorem block_err (ks : List Nat) (s : ArmState) :
    read_err (block ks s) = read_err s := block_frame ks s .ERR trivial

theorem follows_run (base : BitVec 64) (ks : List Nat) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (hf : Follows base ks s) :
    run ks.length s = block ks s := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    rcases hf with ⟨hk, hp, hf⟩
    rw [List.length_cons, run_opener_general, step_code s base k hk hc hp he]
    exact ih (instruction k s)
      (by simpa only [CodeAt, SszArm.CodeAt, instruction_program] using hc)
      (by simpa only [instruction_err] using he) hf

end SszArm.Udivti3
