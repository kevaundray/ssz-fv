import SszArm.UintByteMemory
import SszArm.UintShifts

namespace SszArm.UintCodec.Large

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The complete contiguous store/outer/inner loop window in the linked image. -/
def words : List (BitVec 32) :=
  [0xd10043ff#32, 0xf90003e9#32, 0xaa0e03e9#32, 0xd37df129#32,
   0x8b090189#32, 0xf9000121#32, 0xf94003e9#32, 0x910043ff#32,
   0xeb0b01df#32, 0x910005ce#32, 0x910021ad#32, 0xaa1003e8#32,
   0x54ffb340#32, 0xf1002110#32, 0xaa1f03e1#32, 0x9a8f3111#32,
   0xeb0d0068#32, 0x9a8833f2#32, 0xeb0e0d3f#32, 0x54fffda0#32,
   0xaa1f03e4#32, 0xaa1f03e1#32, 0xaa0d03e8#32, 0xb4005b52#32,
   0xd10043ff#32, 0xf90003e9#32, 0xaa0803e9#32, 0x8b090049#32,
   0x39400125#32, 0xf94003e9#32, 0x910043ff#32, 0xd1000631#32,
   0xd1000652#32, 0x91000508#32, 0x9ac420a5#32, 0x91002084#32,
   0xaa0100a1#32, 0xb5fffe51#32, 0x17ffffda#32]

/-- SUBS retains the subtraction result and the architectural comparison flags. -/
def subtract (dst : BitVec 5) (a b : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR dst) (a - b) (Udivti3.compare a b s)

open Udivti3 in
/-- These effects are certified against the literal decoder below. -/
def instruction (k : Nat) (s : ArmState) : ArmState :=
  match k with
  | 0 | 24 => put 31 (r (.GPR 31) s - 16#64) s
  | 1 | 25 => next (write_mem_bytes 8 (r (.GPR 31) s) (r (.GPR 9) s) s)
  | 2 => put 9 (r (.GPR 14) s) s
  | 3 => put 9 (r (.GPR 9) s <<< 3) s
  | 4 => put 9 (r (.GPR 12) s + r (.GPR 9) s) s
  | 5 => next (write_mem_bytes 8 (r (.GPR 9) s) (r (.GPR 1) s) s)
  | 6 | 29 => put 9 (read_mem_bytes 8 (r (.GPR 31) s) s) s
  | 7 | 30 => put 31 (r (.GPR 31) s + 16#64) s
  | 8 => compare (r (.GPR 14) s) (r (.GPR 11) s) s
  | 9 => put 14 (r (.GPR 14) s + 1#64) s
  | 10 => put 13 (r (.GPR 13) s + 8#64) s
  | 11 => put 8 (r (.GPR 16) s) s
  | 12 => branch (r (.FLAG .Z) s = 1#1) (-2456#64) s
  | 13 => subtract 16 (r (.GPR 8) s) 8#64 s
  | 14 | 21 => put 1 0#64 s
  | 15 => put 17 (if r (.FLAG .C) s ≠ 1#1 then r (.GPR 8) s else r (.GPR 15) s) s
  | 16 => subtract 8 (r (.GPR 3) s) (r (.GPR 13) s) s
  | 17 => put 18 (if r (.FLAG .C) s ≠ 1#1 then 0#64 else r (.GPR 8) s) s
  | 18 => compare (r (.GPR 9) s) (r (.GPR 14) s <<< 3) s
  | 19 => branch (r (.FLAG .Z) s = 1#1) (-76#64) s
  | 20 => put 4 0#64 s
  | 22 => put 8 (r (.GPR 13) s) s
  | 23 => branch (r (.GPR 18) s = 0#64) 2920#64 s
  | 26 => put 9 (r (.GPR 8) s) s
  | 27 => put 9 (r (.GPR 2) s + r (.GPR 9) s) s
  | 28 => put 5 ((read_mem_bytes 1 (r (.GPR 9) s) s).setWidth 64) s
  | 31 => put 17 (r (.GPR 17) s - 1#64) s
  | 32 => put 18 (r (.GPR 18) s - 1#64) s
  | 33 => put 8 (r (.GPR 8) s + 1#64) s
  | 34 => put 5 (r (.GPR 5) s <<<
      (BitVec.ofInt 6 ((r (.GPR 4) s).toInt % 64)).toNat) s
  | 35 => put 4 (r (.GPR 4) s + 8#64) s
  | 36 => put 1 (r (.GPR 5) s ||| r (.GPR 1) s) s
  | 37 => branch (r (.GPR 17) s ≠ 0#64) (-56#64) s
  | 38 => w .PC (read_pc s - 152#64) s
  | _ => s

/-- Each row is fetched from `CodeAt`; no surrogate program is assumed. -/
theorem step_instruction (s : ArmState) (base : BitVec 64) (k : Nat) (hk : k < 39)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 (6868 + 4*k))
    (he : read_err s = .None) (ha : CheckSPAlignment s) :
    stepi s = instruction k s := by
  have rows : ∀ i : Fin 39, (6868 + 4*i.val, words[i.val]) ∈ program := by decide
  have hf := hc _ (rows ⟨k, hk⟩)
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _
  | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _
  | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _
  | 32, _ | 33, _ | 34, _ | 35, _ | 36, _ | 37, _ | 38, _ =>
    simp only [words, List.getElem_cons_zero, List.getElem_cons_succ] at hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true})
      [instruction, subtract, Udivti3.next, Udivti3.put, Udivti3.compare,
       Udivti3.branch, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_and_ones, uint_lsl3_mask,
       ha, apply_ite]
    all_goals try (split <;> simp_all)
    all_goals try (apply w_of_w_commute <;> decide)
  | k + 39, hk => omega

@[simp] theorem instruction_program (k : Nat) (s : ArmState) :
    (instruction k s).program = s.program := by
  unfold instruction
  split <;> simp [subtract, Udivti3.next, Udivti3.put, Udivti3.compare,
    Udivti3.branch, state_simp_rules, apply_ite]

@[simp] theorem instruction_err (k : Nat) (s : ArmState) :
    read_err (instruction k s) = read_err s := by
  unfold instruction
  split <;> simp [subtract, Udivti3.next, Udivti3.put, Udivti3.compare,
    Udivti3.branch, state_simp_rules, apply_ite]

def block : List Nat → ArmState → ArmState
  | [], s => s
  | k :: ks, s => block ks (instruction k s)

def Follows (base : BitVec 64) : List Nat → ArmState → Prop
  | [], _ => True
  | k :: ks, s => k < 39 ∧ read_pc s = base + BitVec.ofNat 64 (6868 + 4*k) ∧
      Follows base ks (instruction k s)

theorem instruction_aligned (k : Nat) (s : ArmState) (ha : CheckSPAlignment s) :
    CheckSPAlignment (instruction k s) := by
  unfold instruction
  split <;> simp [subtract, Udivti3.next, Udivti3.put, Udivti3.compare,
    Udivti3.branch, state_simp_rules, apply_ite, ha]
  all_goals first
    | exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s ha)
    | exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s ha)

theorem follows_run (base : BitVec 64) (ks : List Nat) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : Follows base ks s) : run ks.length s = block ks s := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    rcases hf with ⟨hk, hp, hf⟩
    rw [List.length_cons, run_opener_general, step_instruction s base k hk hc hp he ha]
    exact ih _ (by simpa only [CodeAt, instruction_program] using hc)
      (by simpa only [instruction_err] using he) (instruction_aligned k s ha) hf

end SszArm.UintCodec.Large
