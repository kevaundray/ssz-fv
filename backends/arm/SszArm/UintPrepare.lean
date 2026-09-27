import SszArm.UintShifts
import SszArm.BoolBlocks
import SszArm.BoolResultMemory
import SszArena

namespace SszArm.UintCodec

open BoolCodec (StoreOp)
open Udivti3 (next put branch)

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def prepareWords : List (BitVec 32) :=
  [0xd343fd0b#32,0x9100056a#32,0xd37df14d#32,0xd10043ff#32,
   0xf90003e9#32,0x924101a9#32,0xb4000089#32,0xf94003e9#32,
   0x910043ff#32,0x14000004#32,0xf94003e9#32,0x910043ff#32,0x140001eb#32]

def prepareInstruction (k : Nat) (s : ArmState) : ArmState :=
  match k with
  | 0 => put 11 (r (.GPR 8) s >>> 3) s
  | 1 => put 10 (r (.GPR 11) s + 1#64) s
  | 2 => put 13 (r (.GPR 10) s <<< 3) s
  | 3 => StoreOp.subSp16.effect s
  | 4 => StoreOp.strX9Sp.effect s
  | 5 => put 9 (r (.GPR 13) s &&& 9223372036854775808#64) s
  | 6 => branch (r (.GPR 9) s = 0#64) 16#64 s
  | 7 | 10 => StoreOp.ldrX9Sp.effect s
  | 8 | 11 => StoreOp.addSp16.effect s
  | 9 => w .PC (read_pc s + 16#64) s
  | 12 => w .PC (read_pc s + 1964#64) s
  | _ => s

theorem prepare_step_word (s : ArmState) (k : Nat) (hk : k < 13)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some prepareWords[k]) :
    stepi s = prepareInstruction k s := by
  match k, hk with
  | 3, _ => exact BoolCodec.step_word s .subSp16 he ha hf
  | 4, _ => exact BoolCodec.step_word s .strX9Sp he ha hf
  | 7, _ | 10, _ => exact BoolCodec.step_word s .ldrX9Sp he ha hf
  | 8, _ | 11, _ => exact BoolCodec.step_word s .addSp16 he ha hf
  | 0, _ | 1, _ | 2, _ | 5, _ | 6, _ | 9, _ | 12, _ =>
    simp [prepareWords] at hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true})
      [prepareInstruction, put, next, branch, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, BitVec.setWidth_eq, uint_and_ones,
       uint_lsl3_mask, uint_lsr3_mask, apply_ite]
    all_goals first | rfl | exact w_of_w_commute (by decide)
  | k + 13, hk => omega

theorem prepare_step (s : ArmState) (base : BitVec 64) (k : Nat) (hk : k < 13)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 (4764 + 4*k))
    (he : read_err s = .None) (ha : CheckSPAlignment s) :
    stepi s = prepareInstruction k s := by
  have rows : ∀ i : Fin 13, (4764 + 4*i.val, prepareWords[i.val]) ∈ program := by decide
  apply prepare_step_word s k hk he ha
  rw [hp]
  exact hc _ (rows ⟨k,hk⟩)

theorem prepareInstruction_program (k : Nat) (s : ArmState) :
    (prepareInstruction k s).program = s.program := by
  unfold prepareInstruction
  split <;> simp [put, next, branch, StoreOp.effect, state_simp_rules]

theorem prepareInstruction_error (k : Nat) (s : ArmState) :
    read_err (prepareInstruction k s) = read_err s := by
  unfold prepareInstruction
  split <;> simp [put, next, branch, StoreOp.effect, state_simp_rules]

theorem prepareInstruction_aligned (k : Nat) (s : ArmState) (ha : CheckSPAlignment s) :
    CheckSPAlignment (prepareInstruction k s) := by
  unfold prepareInstruction
  split <;> first
    | exact StoreOp.effect_aligned _ s ha
    | simpa [put, next, branch, state_simp_rules] using ha

def prepareBlock : List Nat → ArmState → ArmState
  | [], s => s
  | k :: ks, s => prepareBlock ks (prepareInstruction k s)

def PrepareFollows (base : BitVec 64) : List Nat → ArmState → Prop
  | [], _ => True
  | k :: ks, s => k < 13 ∧ read_pc s = base + BitVec.ofNat 64 (4764 + 4*k) ∧
      PrepareFollows base ks (prepareInstruction k s)

theorem prepare_block_run (ks : List Nat) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (hp : PrepareFollows base ks s)
    (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run ks.length s = prepareBlock ks s := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    obtain ⟨hk, hpc, ht⟩ := hp
    rw [List.length_cons, Nat.add_comm ks.length 1, run_plus]
    change run ks.length (stepi s) = prepareBlock ks (prepareInstruction k s)
    rw [prepare_step s base k hk hc hpc he ha]
    apply ih _ _ ht ((prepareInstruction_error k s).trans he) (prepareInstruction_aligned k s ha)
    intro row hr
    simpa only [prepareInstruction_program] using hc row hr

end SszArm.UintCodec
