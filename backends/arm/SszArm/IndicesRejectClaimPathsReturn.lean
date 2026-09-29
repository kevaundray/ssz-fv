import SszArm.IndicesLinkedRejectClaimPaths
import SszArm.DispatchBlocks
import SszArm.BoolMemory
import SszArm.DelimitedMemory

namespace SszArm.Indices.RejectClaimPaths.Return

open Dispatch.Block (next put)

inductive Pair where
  | x20x19 | x22x21 | x24x23 | x26x25 | x28x27 | x29x30
  deriving DecidableEq

def Pair.offset : Pair → Nat
  | .x20x19 => 908 | .x22x21 => 912 | .x24x23 => 916
  | .x26x25 => 920 | .x28x27 => 924 | .x29x30 => 928

def Pair.slot : Pair → BitVec 64
  | .x20x19 => 144 | .x22x21 => 128 | .x24x23 => 112
  | .x26x25 => 96 | .x28x27 => 80 | .x29x30 => 64

def Pair.first : Pair → BitVec 5
  | .x20x19 => 20 | .x22x21 => 22 | .x24x23 => 24
  | .x26x25 => 26 | .x28x27 => 28 | .x29x30 => 29

def Pair.second : Pair → BitVec 5
  | .x20x19 => 19 | .x22x21 => 21 | .x24x23 => 23
  | .x26x25 => 25 | .x28x27 => 27 | .x29x30 => 30

def Pair.word : Pair → BitVec 32
  | .x20x19 => 0xa9494ff4 | .x22x21 => 0xa94857f6 | .x24x23 => 0xa9475ff8
  | .x26x25 => 0xa94667fa | .x28x27 => 0xa9456ffc | .x29x30 => 0xa9447bfd

def restore (pair : Pair) (s : ArmState) : ArmState :=
  next (w (.GPR pair.second)
    (read_mem_bytes 8 (r (.GPR 31#5) s + pair.slot + 8#64) s)
    (w (.GPR pair.first) (read_mem_bytes 8 (r (.GPR 31#5) s + pair.slot) s) s))

theorem restore_step (pair : Pair) (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 pair.offset) :
    stepi s = restore pair s := by
  have fetched := Linked.RejectClaimPaths.chunk3_codeAt code
    (pair.offset, pair.word) (by cases pair <;> decide)
  cases pair
  all_goals
    simp only [Pair.offset, Pair.word] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [restore, Pair.first, Pair.second, Pair.slot, next, exec_inst,
        state_simp_rules, bitvec_rules, minimal_theory, aligned,
        BoolCodec.pair_read_low, BoolCodec.pair_read_high, BitVec.add_assoc]
  all_goals first | rfl | exact w_of_w_commute (by decide)

def release (s : ArmState) : ArmState := put 31 (r (.GPR 31#5) s + 160#64) s

def ret (s : ArmState) : ArmState := w .PC (r (.GPR 30#5) s) s

theorem release_step (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 932#64) : stepi s = release s := by
  have fetched := Linked.RejectClaimPaths.chunk3_codeAt code (932, 0x910283ff#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [release, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem ret_step (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 936#64) : stepi s = ret s := by
  have fetched := Linked.RejectClaimPaths.chunk3_codeAt code (936, 0xd65f03c0#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [ret, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

def pairs : List Pair := [.x20x19, .x22x21, .x24x23, .x26x25, .x28x27, .x29x30]

def restored (s : ArmState) : ArmState := pairs.foldl (fun t pair => restore pair t) s

def finish (s : ArmState) : ArmState := ret (release (restored s))

def Control (base : BitVec 64) : List Pair → ArmState → Prop
  | [], _ => True
  | pair :: rest, s => read_pc s = base + BitVec.ofNat 64 pair.offset ∧
      Control base rest (restore pair s)

private theorem restore_list (ps : List Pair) (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (control : Control base ps s) :
    run ps.length s = ps.foldl (fun t pair => restore pair t) s := by
  induction ps generalizing s with
  | nil => rfl
  | cons pair rest ih =>
      change run (rest.length + 1) s = rest.foldl (fun t pair => restore pair t) (restore pair s)
      rw [run, restore_step pair s base code error aligned control.1]
      apply ih
      · exact Codec.Linked.WordsAt.preserve code (by simp [restore, next, state_simp_rules])
      · simpa [restore, next, state_simp_rules] using error
      · cases pair <;>
          simpa [restore, Pair.first, Pair.second, next, CheckSPAlignment,
            state_simp_rules] using aligned
      · exact control.2

/-- The one real shared epilogue restores all twelve callee-save GPRs. -/
theorem finish_run (s : ArmState) (base : BitVec 64)
    (code : Linked.RejectClaimPaths.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 908#64) :
    run 8 s = finish s := by
  have first : run 6 s = restored s := by
    apply restore_list pairs s base code error aligned
    change r .PC s = _ at pc
    simp [Control, pairs, restore, Pair.offset, next, state_simp_rules, pc, BitVec.add_assoc]
  have second := release_step (restored s) base
    (Codec.Linked.WordsAt.preserve code (by
      simp [restored, pairs, restore, next, state_simp_rules]))
    (by simpa [restored, pairs, restore, next, state_simp_rules] using error)
    (by simp [restored, pairs, restore, next, state_simp_rules, pc, BitVec.add_assoc])
  have third := ret_step (release (restored s)) base
    (Codec.Linked.WordsAt.preserve code (by
      simp [release, restored, pairs, restore, put, next, state_simp_rules]))
    (by simpa [release, restored, pairs, restore, put, next, state_simp_rules] using error)
    (by simp [release, restored, pairs, restore, put, next, state_simp_rules,
      pc, BitVec.add_assoc])
  rw [show 8 = 6 + 2 by decide, run_plus, first]
  change stepi (stepi (restored s)) = _
  rw [second, third]
  rfl

@[simp] theorem finish_memory (s : ArmState) : (finish s).mem = s.mem := by
  simp [finish, ret, release, restored, pairs, restore, put, next, state_simp_rules]

@[simp] theorem finish_program (s : ArmState) : (finish s).program = s.program := by
  simp [finish, ret, release, restored, pairs, restore, put, next, state_simp_rules]

@[simp] theorem finish_error (s : ArmState) : read_err (finish s) = read_err s := by
  simp [finish, ret, release, restored, pairs, restore, put, next, state_simp_rules]

@[simp] theorem finish_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (finish s) = r (.SFP reg) s := by
  simp [finish, ret, release, restored, pairs, restore, put, next, state_simp_rules]

/-- Save-slot facts are internal loop invariants, not original-entry premises. -/
structure Saved (original s : ArmState) : Prop where
  sp : r (.GPR 31#5) s + 160#64 = r (.GPR 31#5) original
  first : ∀ pair : Pair, read_mem_bytes 8 (r (.GPR 31#5) s + pair.slot) s =
    r (.GPR pair.first) original
  second : ∀ pair : Pair, read_mem_bytes 8 (r (.GPR 31#5) s + pair.slot + 8#64) s =
    r (.GPR pair.second) original
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) s).setWidth 64 = (r (.SFP reg) original).setWidth 64

theorem finish_returned (original s : ArmState) (saved : Saved original s)
    (error : read_err s = .None) : Delimited.Returned original (finish s) := by
  constructor
  · simpa [finish, ret, release, restored, pairs, restore, Pair.first, Pair.second,
      Pair.slot, put, next, state_simp_rules] using saved.second .x29x30
  · simpa using error
  · simpa [finish, ret, release, restored, pairs, restore, Pair.first, Pair.second,
      put, next, state_simp_rules] using saved.sp
  · intro reg lower upper
    have alternatives : reg = 19#5 ∨ reg = 20#5 ∨ reg = 21#5 ∨ reg = 22#5 ∨
        reg = 23#5 ∨ reg = 24#5 ∨ reg = 25#5 ∨ reg = 26#5 ∨ reg = 27#5 ∨
        reg = 28#5 ∨ reg = 29#5 ∨ reg = 30#5 := by
      have numerals : reg.toNat = 19 ∨ reg.toNat = 20 ∨ reg.toNat = 21 ∨
          reg.toNat = 22 ∨ reg.toNat = 23 ∨ reg.toNat = 24 ∨ reg.toNat = 25 ∨
          reg.toNat = 26 ∨ reg.toNat = 27 ∨ reg.toNat = 28 ∨ reg.toNat = 29 ∨
          reg.toNat = 30 := by omega
      simpa only [← BitVec.toNat_inj, BitVec.toNat_ofNat] using numerals
    rcases alternatives with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals subst reg
    all_goals
      simp only [finish, ret, release, restored, pairs, List.foldl_cons, List.foldl_nil,
        restore, Pair.first, Pair.second, Pair.slot, put, next, state_simp_rules]
      first
      | exact saved.first .x20x19
      | exact saved.first .x22x21
      | exact saved.first .x24x23
      | exact saved.first .x26x25
      | exact saved.first .x28x27
      | exact saved.first .x29x30
      | exact saved.second .x20x19
      | exact saved.second .x22x21
      | exact saved.second .x24x23
      | exact saved.second .x26x25
      | exact saved.second .x28x27
      | exact saved.second .x29x30
  · intro reg lower upper
    simpa using saved.vectors reg lower upper

end SszArm.Indices.RejectClaimPaths.Return
