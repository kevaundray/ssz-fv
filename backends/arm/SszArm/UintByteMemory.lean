import SszArm.UintExec
import SszArm.BoolAlignment
import SszArm.BoolResultMemory
import SszArm.Udivti3Arithmetic
import SszWordDecode

namespace SszArm.UintCodec.Small

open SszNative.WordDecode

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The contiguous, literal instruction window at 4320--4456. -/
def words : List (BitVec 32) :=
  [0xd100044a#32, 0xaa0303e8#32, 0xb40003e8#32, 0xd10043ff#32,
   0xf90003e9#32, 0xaa0803e9#32, 0x8b090149#32, 0x3940012b#32,
   0xf94003e9#32, 0x910043ff#32, 0xaa0803e9#32, 0xd1000508#32,
   0x34fffecb#32, 0xf100253f#32, 0x54000c22#32, 0xaa1f03e8#32,
   0xaa1f03ea#32, 0xaa1f03eb#32, 0xd10043ff#32, 0xf90003e9#32,
   0xaa0b03e9#32, 0x8b090049#32, 0x3940012c#32, 0xf94003e9#32,
   0x910043ff#32, 0x927d090d#32, 0x9100056b#32, 0xeb0b013f#32,
   0x91002108#32, 0x9acd218c#32, 0xaa0a018a#32, 0x54fffe61#32,
   0x14000002#32, 0xaa1f03ea#32, 0xaa1f03ec#32]

open Udivti3 in
/-- Architectural effects, including the real spill and restore instructions. -/
def instruction (k : Nat) (s : ArmState) : ArmState :=
  match k with
  | 0 => put 10 (r (.GPR 2) s - 1#64) s
  | 1 => put 8 (r (.GPR 3) s) s
  | 2 => branch (r (.GPR 8) s = 0#64) 124#64 s
  | 3 | 18 => put 31 (r (.GPR 31) s - 16#64) s
  | 4 | 19 => next (write_mem_bytes 8 (r (.GPR 31) s) (r (.GPR 9) s) s)
  | 5 | 10 => put 9 (r (.GPR 8) s) s
  | 6 => put 9 (r (.GPR 10) s + r (.GPR 9) s) s
  | 7 => put 11 ((read_mem_bytes 1 (r (.GPR 9) s) s).setWidth 64) s
  | 8 | 23 => put 9 (read_mem_bytes 8 (r (.GPR 31) s) s) s
  | 9 | 24 => put 31 (r (.GPR 31) s + 16#64) s
  | 11 => put 8 (r (.GPR 8) s - 1#64) s
  | 12 => branch ((r (.GPR 11) s).setWidth 32 = 0#32) (-40#64) s
  | 13 => compare (r (.GPR 9) s) 9#64 s
  | 14 => branch (r (.FLAG .C) s = 1#1) 388#64 s
  | 15 => put 8 0#64 s
  | 16 | 33 => put 10 0#64 s
  | 17 => put 11 0#64 s
  | 20 => put 9 (r (.GPR 11) s) s
  | 21 => put 9 (r (.GPR 2) s + r (.GPR 9) s) s
  | 22 => put 12 ((read_mem_bytes 1 (r (.GPR 9) s) s).setWidth 64) s
  | 25 => put 13 (r (.GPR 8) s &&& 56#64) s
  | 26 => put 11 (r (.GPR 11) s + 1#64) s
  | 27 => compare (r (.GPR 9) s) (r (.GPR 11) s) s
  | 28 => put 8 (r (.GPR 8) s + 8#64) s
  | 29 => put 12 (r (.GPR 12) s <<<
      (BitVec.ofInt 6 ((r (.GPR 13) s).toInt % 64)).toNat) s
  | 30 => put 10 (r (.GPR 12) s ||| r (.GPR 10) s) s
  | 31 => branch (r (.FLAG .Z) s ≠ 1#1) (-52#64) s
  | 32 => w .PC (read_pc s + 8#64) s
  | 34 => put 12 0#64 s
  | _ => s

/-- A closed decoder certificate, using the linked image rather than a substitute program. -/
theorem step_instruction (s : ArmState) (base : BitVec 64) (k : Nat) (hk : k < 35)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 (4320 + 4*k))
    (he : read_err s = .None) (ha : CheckSPAlignment s) :
    stepi s = instruction k s := by
  have rows : ∀ i : Fin 35, (4320 + 4*i.val, words[i.val]) ∈ program := by decide
  have hf := hc _ (rows ⟨k, hk⟩)
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _
  | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _
  | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _
  | 32, _ | 33, _ | 34, _ =>
    simp only [words, List.getElem_cons_zero, List.getElem_cons_succ] at hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true})
      [instruction, Udivti3.next, Udivti3.put, Udivti3.compare, Udivti3.branch,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, apply_ite]
    all_goals try (split <;> simp_all)
    all_goals exact w_of_w_commute (by decide)
  | k + 35, hk => omega

@[simp] theorem instruction_program (k : Nat) (s : ArmState) :
    (instruction k s).program = s.program := by
  unfold instruction
  split <;> simp [Udivti3.next, Udivti3.put, Udivti3.compare, Udivti3.branch,
    state_simp_rules, apply_ite]

@[simp] theorem instruction_err (k : Nat) (s : ArmState) :
    read_err (instruction k s) = read_err s := by
  unfold instruction
  split <;> simp [Udivti3.next, Udivti3.put, Udivti3.compare, Udivti3.branch,
    state_simp_rules, apply_ite]

def block : List Nat → ArmState → ArmState
  | [], s => s
  | k :: ks, s => block ks (instruction k s)

def Follows (base : BitVec 64) : List Nat → ArmState → Prop
  | [], _ => True
  | k :: ks, s => k < 35 ∧ read_pc s = base + BitVec.ofNat 64 (4320 + 4*k) ∧
      Follows base ks (instruction k s)

theorem instruction_aligned (k : Nat) (s : ArmState) (ha : CheckSPAlignment s) :
    CheckSPAlignment (instruction k s) := by
  unfold instruction
  split <;> simp [Udivti3.next, Udivti3.put, Udivti3.compare, Udivti3.branch,
    state_simp_rules, apply_ite, ha]
  all_goals first
    | exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s ha)
    | exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s ha)

theorem follows_run (base : BitVec 64) (ks : List Nat) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : Follows base ks s) :
    run ks.length s = block ks s := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    rcases hf with ⟨hk, hp, hf⟩
    rw [List.length_cons, run_opener_general, step_instruction s base k hk hc hp he ha]
    exact ih _ (by simpa only [CodeAt, instruction_program] using hc)
      (by simpa only [instruction_err] using he) (instruction_aligned k s ha) hf

/-- Input bytes and the sole temporary lowering frame are caller-owned and disjoint. -/
structure Input (s : ArmState) (data : Ssz.Bytes) : Prop where
  length : r (.GPR 3) s = BitVec.ofNat 64 data.size
  bounded : data.size < 2^63
  range : (r (.GPR 2) s).toNat + data.size ≤ 2^64
  stack : 16 ≤ (r (.GPR 31) s).toNat
  separated : data.size = 0 ∨
    (r (.GPR 2) s).toNat + data.size ≤ (r (.GPR 31) s).toNat - 16 ∨
    (r (.GPR 31) s).toNat ≤ (r (.GPR 2) s).toNat
  bytes : ∀ i, i < data.size → read_mem_bytes 1 (r (.GPR 2) s + BitVec.ofNat 64 i) s =
    (data[i]?.getD 0).toBitVec
/-- Every live argument and saved register is untouched. Only x8--x13 and flags die. -/
def Live (i : BitVec 5) : Prop :=
  i ≠ 8#5 ∧ i ≠ 9#5 ∧ i ≠ 10#5 ∧ i ≠ 11#5 ∧ i ≠ 12#5 ∧ i ≠ 13#5

instance (i : BitVec 5) : Decidable (Live i) := by
  unfold Live
  infer_instance

structure Stable (s t : ArmState) : Prop where
  program : t.program = s.program
  err : read_err t = read_err s
  regs : ∀ i, Live i → r (.GPR i) t = r (.GPR i) s
  simd : ∀ i, r (.SFP i) t = r (.SFP i) s
  frame : ∀ a, a.toNat < (r (.GPR 31) s).toNat - 16 ∨ (r (.GPR 31) s).toNat ≤ a.toNat →
    t.mem a = s.mem a

theorem Stable.refl (s : ArmState) : Stable s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem Stable.trans {s t u : ArmState} (h : Stable s t) (g : Stable t u) : Stable s u := by
  refine ⟨g.program.trans h.program, g.err.trans h.err,
    fun i hi => (g.regs i hi).trans (h.regs i hi),
    fun i => (g.simd i).trans (h.simd i), ?_⟩
  intro a ha
  rw [g.frame a (by simpa only [h.regs 31 (by decide)] using ha), h.frame a ha]

theorem Stable.code {s t : ArmState} {base : BitVec 64} (h : Stable s t)
    (hc : CodeAt s base) : CodeAt t base := by simpa only [CodeAt, h.program] using hc

theorem Stable.aligned {s t : ArmState} (h : Stable s t) (ha : CheckSPAlignment s) :
    CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, bitvec_rules, minimal_theory,
    h.regs 31#5 (by decide)] using ha

theorem Stable.input {s t : ArmState} {data : Ssz.Bytes} (h : Stable s t)
    (hi : Input s data) : Input t data := by
  have h2 := h.regs 2 (by decide)
  have h3 := h.regs 3 (by decide)
  have h31 := h.regs 31 (by decide)
  refine ⟨h3.trans hi.length, hi.bounded, ?_, ?_, ?_, ?_⟩
  · simpa only [h2] using hi.range
  · simpa only [h31] using hi.stack
  · simpa only [h2, h31] using hi.separated
  · intro i hin
    rw [h2, BoolCodec.read_one]
    change t.mem (r (.GPR 2) s + BitVec.ofNat 64 i) = _
    rw [h.frame _ (by have := hi.range; have := hi.separated; bv_omega)]
    simpa only [BoolCodec.read_one, read_mem, read_store] using hi.bytes i hin

/-- The spilled x9 is restored exactly, even after arbitrarily many loop visits. -/
theorem scratch_restore (s : ArmState) (hs : 16 ≤ (r (.GPR 31) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31) s - 16#64)
      (write_mem_bytes 8 (r (.GPR 31) s - 16#64) (r (.GPR 9) s) s) = r (.GPR 9) s := by
  apply BoolCodec.read_mem_bytes_write_mem_bytes_same
  bv_omega

/-- A byte load cannot observe the lowering spill. -/
theorem scratch_byte (s : ArmState) (data : Ssz.Bytes) (hi : Input s data)
    (i : Nat) (hin : i < data.size) :
    read_mem_bytes 1 (r (.GPR 2) s + BitVec.ofNat 64 i)
      (write_mem_bytes 8 (r (.GPR 31) s - 16#64) (r (.GPR 9) s) s) =
        (data[i]?.getD 0).toBitVec := by
  rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]
  · exact hi.bytes i hin
  · have := hi.range; bv_omega
  · have := hi.stack; bv_omega
  · have := hi.range; have := hi.stack; have := hi.separated; bv_omega

end SszArm.UintCodec.Small
