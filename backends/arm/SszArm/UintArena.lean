import SszArm.UintExec
import SszArm.Udivti3Arithmetic
import SszArena

namespace SszArm.UintCodec

open BitVec
open SszArm.Udivti3 (next put compare flagged branch)

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- The contiguous reservation block, including its actual overflow branches. -/
def arenaWords : List (BitVec 32) :=
  [0xf940026c#32, 0xf9400a6e#32, 0xab0c01cf#32, 0x54ffc262#32,
   0xb10021ff#32, 0x54ffc228#32, 0x91001df0#32, 0x927df210#32,
   0xcb0f020f#32, 0xab0e01ef#32, 0x54ffc182#32, 0xab0d01f0#32,
   0x54ffc142#32, 0xf940066d#32, 0xeb0d021f#32, 0x54ffc0e8#32,
   0xaa1f03ed#32, 0xaa1f03ee#32, 0x91000508#32, 0x8b0f018c#32,
   0x5280010f#32, 0xf9000a70#32, 0x1400000e#32]

def arenaInstruction (k : Nat) (s : ArmState) : ArmState :=
  match k with
  | 0 => put 12 (read_mem_bytes 8 (r (.GPR 19) s) s) s
  | 1 => put 14 (read_mem_bytes 8 (r (.GPR 19) s + 16#64) s) s
  | 2 => flagged 15 (r (.GPR 14) s) (r (.GPR 12) s) 0#1 s
  | 3 => branch (r (.FLAG .C) s = 1#1) (-1972#64) s
  | 4 => write_pstate (AddWithCarry (r (.GPR 15) s) 8#64 0#1).2 (next s)
  | 5 => branch (r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1) (-1980#64) s
  | 6 => put 16 (r (.GPR 15) s + 7#64) s
  | 7 => put 16 (r (.GPR 16) s &&& ~~~7#64) s
  | 8 => put 15 (r (.GPR 16) s - r (.GPR 15) s) s
  | 9 => flagged 15 (r (.GPR 15) s) (r (.GPR 14) s) 0#1 s
  | 10 => branch (r (.FLAG .C) s = 1#1) (-2000#64) s
  | 11 => flagged 16 (r (.GPR 15) s) (r (.GPR 13) s) 0#1 s
  | 12 => branch (r (.FLAG .C) s = 1#1) (-2008#64) s
  | 13 => put 13 (read_mem_bytes 8 (r (.GPR 19) s + 8#64) s) s
  | 14 => Udivti3.compare (r (.GPR 16) s) (r (.GPR 13) s) s
  | 15 => branch (r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1) (-2020#64) s
  | 16 => put 13 0#64 s
  | 17 => put 14 0#64 s
  | 18 => put 8 (r (.GPR 8) s + 1#64) s
  | 19 => put 12 (r (.GPR 12) s + r (.GPR 15) s) s
  | 20 => put 15 8#64 s
  | 21 => next (write_mem_bytes 8 (r (.GPR 19) s + 16#64) (r (.GPR 16) s) s)
  | 22 => w .PC (read_pc s + 56#64) s
  | _ => s

theorem arena_step_word (s : ArmState) (k : Nat) (hk : k < 23)
    (he : read_err s = .None)
    (hf : s.program.find? (read_pc s) = some arenaWords[k]) :
    stepi s = arenaInstruction k s := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _
  | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ =>
    simp [arenaWords] at hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true})
      [arenaInstruction, next, put, Udivti3.compare, flagged, branch, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
       BitVec.sub_eq_add_neg, apply_ite]
    all_goals try (split <;> simp_all)
    all_goals apply w_of_w_commute <;> decide
  | k + 23, hk => omega

theorem arena_step (s : ArmState) (base : BitVec 64) (k : Nat) (hk : k < 23)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 (6776 + 4 * k))
    (he : read_err s = .None) : stepi s = arenaInstruction k s := by
  have rows : ∀ i : Fin 23, (6776 + 4 * i.val, arenaWords[i.val]) ∈ program := by decide
  apply arena_step_word s k hk he
  rw [hp]
  exact hc _ (rows ⟨k, hk⟩)

theorem arenaInstruction_program (k : Nat) (s : ArmState) :
    (arenaInstruction k s).program = s.program := by
  unfold arenaInstruction
  split <;> simp [next, put, Udivti3.compare, flagged, branch, state_simp_rules]

theorem arenaInstruction_error (k : Nat) (s : ArmState) :
    read_err (arenaInstruction k s) = read_err s := by
  unfold arenaInstruction
  split <;> simp [next, put, Udivti3.compare, flagged, branch, state_simp_rules]

theorem arenaInstruction_code (k : Nat) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) : CodeAt (arenaInstruction k s) base := by
  intro row hr
  simpa only [arenaInstruction_program] using hc row hr

def ArenaPreserved : StateField → Prop
  | .GPR i => i ≠ 8#5 ∧ i ≠ 12#5 ∧ i ≠ 13#5 ∧ i ≠ 14#5 ∧ i ≠ 15#5 ∧ i ≠ 16#5
  | .ERR | .SFP _ => True
  | .PC | .FLAG _ => False

instance (f : StateField) : Decidable (ArenaPreserved f) := by
  cases f <;> dsimp [ArenaPreserved] <;> infer_instance

theorem arenaInstruction_field (k : Nat) (s : ArmState) (f : StateField)
    (hf : ArenaPreserved f) : r f (arenaInstruction k s) = r f s := by
  unfold arenaInstruction
  split <;> cases f <;>
    simp_all (config := {decide := true})
      [ArenaPreserved, next, put, Udivti3.compare, flagged, branch, state_simp_rules]

theorem arenaInstruction_memory (k : Nat) (s : ArmState) (hk : k ≠ 21) :
    (arenaInstruction k s).mem = s.mem := by
  unfold arenaInstruction
  split <;> simp_all [next, put, Udivti3.compare, flagged, branch, state_simp_rules]

def arenaBlock : List Nat → ArmState → ArmState
  | [], s => s
  | k :: ks, s => arenaBlock ks (arenaInstruction k s)

def ArenaFollows (base : BitVec 64) : List Nat → ArmState → Prop
  | [], _ => True
  | k :: ks, s => k < 23 ∧ read_pc s = base + BitVec.ofNat 64 (6776 + 4 * k) ∧
      ArenaFollows base ks (arenaInstruction k s)

theorem arena_block_run (ks : List Nat) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (hf : ArenaFollows base ks s) :
    run ks.length s = arenaBlock ks s := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    obtain ⟨hk, hp, ht⟩ := hf
    rw [List.length_cons, Nat.add_comm ks.length 1, run_plus]
    change run ks.length (stepi s) = arenaBlock ks (arenaInstruction k s)
    rw [arena_step s base k hk hc hp he]
    exact ih _ (arenaInstruction_code k s base hc)
      ((arenaInstruction_error k s).trans he) ht

end SszArm.UintCodec
