import SszArm.Proofs

/-!
Literal bytewise memcmp. LNSym keeps code separate from its total ordinary byte
memory; data mapping, access permissions, devices and concurrency are outside
this contract. The two read views need not be disjoint. No data access is made
on the zero-count path.
-/
namespace SszArm.Memcmp

open BitVec

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def program : List (BitVec 32) :=
  [0xaa0003e3#32, 0x2a1f03e0#32, 0xb40000e2#32, 0x38401464#32,
   0x38401425#32, 0x6b050080#32, 0x54000061#32, 0xd1000442#32,
   0xb5ffff62#32, 0xd65f03c0#32]

/-- Small-step effects retain the pinned byte loads and flag-setting subtraction. -/
def instruction (k : Nat) (s : ArmState) : ArmState :=
  match k with
  | 0 => w .PC (read_pc s + 4#64) (w (.GPR 3) (r (.GPR 0) s) s)
  | 1 => w .PC (read_pc s + 4#64) (w (.GPR 0) 0#64 s)
  | 2 => w .PC (if r (.GPR 2) s = 0#64 then read_pc s + 28#64
      else read_pc s + 4#64) s
  | 3 => w .PC (read_pc s + 4#64)
      (w (.GPR 3) (r (.GPR 3) s + 1#64)
        (w (.GPR 4) ((read_mem_bytes 1 (r (.GPR 3) s) s).setWidth 64) s))
  | 4 => w .PC (read_pc s + 4#64)
      (w (.GPR 1) (r (.GPR 1) s + 1#64)
        (w (.GPR 5) ((read_mem_bytes 1 (r (.GPR 1) s) s).setWidth 64) s))
  | 5 =>
      let v := AddWithCarry ((r (.GPR 4) s).setWidth 32)
        (~~~((r (.GPR 5) s).setWidth 32)) 1#1
      w (.GPR 0) (v.1.setWidth 64)
        (write_pstate v.2 (w .PC (read_pc s + 4#64) s))
  | 6 => if r (.FLAG .Z) s = 1#1 then w .PC (read_pc s + 4#64) s
      else w .PC (read_pc s + 12#64) s
  | 7 => w (.GPR 2) (r (.GPR 2) s - 1#64) (w .PC (read_pc s + 4#64) s)
  | 8 => w .PC (if r (.GPR 2) s = 0#64 then read_pc s + 4#64
      else read_pc s - 20#64) s
  | 9 => w .PC (r (.GPR 30) s) s
  | _ => s

/-- Every literal word is decoded and executed in the pinned ISA model. -/
theorem step_word (s : ArmState) (k : Nat) (hk : k < 10)
    (he : read_err s = .None)
    (hf : s.program.find? (read_pc s) = some program[k]) :
    stepi s = instruction k s := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ =>
    simp [program] at hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true}) [instruction, exec_inst,
      state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
      BitVec.sub_eq_add_neg]
    all_goals first
      | rfl
      | (apply w_of_w_commute; decide)

/-- Every AAPCS64 callee-saved field, SP, and all SIMD fields are preserved. -/
def Preserved : StateField → Prop
  | .GPR i => i ≠ 0#5 ∧ i ≠ 1#5 ∧ i ≠ 2#5 ∧ i ≠ 3#5 ∧ i ≠ 4#5 ∧ i ≠ 5#5
  | .PC | .FLAG _ => False
  | .SFP _ | .ERR => True

theorem instruction_frame (k : Nat) (s : ArmState) (f : StateField)
    (h : Preserved f) : r f (instruction k s) = r f s := by
  cases f <;> simp only [Preserved] at h
  · rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
    unfold instruction
    split <;> simp [state_simp_rules, h0, h1, h2, h3, h4, h5, apply_ite]
  · unfold instruction
    split <;> simp [state_simp_rules, apply_ite]
  · unfold instruction
    split <;> simp [state_simp_rules, apply_ite]

theorem instruction_program (k : Nat) (s : ArmState) :
    (instruction k s).program = s.program := by
  unfold instruction
  split <;> simp [state_simp_rules, apply_ite]
theorem instruction_memory (k : Nat) (s : ArmState) :
    (instruction k s).mem = s.mem := by
  unfold instruction
  split <;> simp [state_simp_rules, apply_ite]
theorem instruction_err (k : Nat) (s : ArmState) :
    read_err (instruction k s) = read_err s := instruction_frame k s .ERR trivial

def entry (s : ArmState) : ArmState := instruction 2 (instruction 1 (instruction 0 s))
def compare (s : ArmState) : ArmState := instruction 6 (instruction 5 (instruction 4 (instruction 3 s)))
def advance (s : ArmState) : ArmState := instruction 8 (instruction 7 s)

/-- Exact read-only state frame, including the program and error fields. -/
def Frame (s t : ArmState) : Prop :=
  t.mem = s.mem ∧ t.program = s.program ∧ (∀ f, Preserved f → r f t = r f s)

theorem frame_refl (s : ArmState) : Frame s s := ⟨rfl, rfl, fun _ _ => rfl⟩
theorem frame_trans {s t u : ArmState} (h : Frame s t) (h' : Frame t u) : Frame s u :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1,
    fun f hf => (h'.2.2 f hf).trans (h.2.2 f hf)⟩
theorem instruction_full_frame (k : Nat) (s : ArmState) : Frame s (instruction k s) :=
  ⟨instruction_memory k s, instruction_program k s, instruction_frame k s⟩
theorem entry_frame (s : ArmState) : Frame s (entry s) := by
  exact frame_trans (instruction_full_frame 0 s)
    (frame_trans (instruction_full_frame 1 _) (instruction_full_frame 2 _))
theorem compare_frame (s : ArmState) : Frame s (compare s) := by
  exact frame_trans (instruction_full_frame 3 s)
    (frame_trans (instruction_full_frame 4 _)
      (frame_trans (instruction_full_frame 5 _) (instruction_full_frame 6 _)))
theorem advance_frame (s : ArmState) : Frame s (advance s) :=
  frame_trans (instruction_full_frame 7 s) (instruction_full_frame 8 _)

abbrev Bytes := List (BitVec 8 × BitVec 8)

/-- Unsigned C-int subtraction at the first unequal pair, or zero. -/
def spec : Bytes → Int
  | [] => 0
  | (a, b) :: xs => if a = b then spec xs else (a.toNat : Int) - b.toNat

/-- Independent, possibly overlapping views of the total model memory. -/
def Reads (m : Memory) (p q : BitVec 64) : Bytes → Prop
  | [] => True
  | (a, b) :: xs => m.read_bytes 1 p = a ∧ m.read_bytes 1 q = b ∧
      Reads m (p + 1) (q + 1) xs

theorem spec_equal_prefix (pre suffix : Bytes)
    (h : ∀ ab ∈ pre, ab.1 = ab.2) : spec (pre ++ suffix) = spec suffix := by
  induction pre with
  | nil => rfl
  | cons ab xs ih =>
    rcases ab with ⟨a, b⟩
    have hab : a = b := h (a, b) (by simp)
    rw [List.cons_append, spec, if_pos hab]
    exact ih (fun ab hm => h ab (by simp [hm]))

theorem spec_first_difference (pre suffix : Bytes) (a b : BitVec 8)
    (h : ∀ ab ∈ pre, ab.1 = ab.2) (hne : a ≠ b) :
    spec (pre ++ (a, b) :: suffix) = (a.toNat : Int) - b.toNat := by
  rw [spec_equal_prefix pre _ h]
  simp [spec, hne]
theorem spec_all_equal (xs : Bytes) (h : ∀ ab ∈ xs, ab.1 = ab.2) : spec xs = 0 := by
  simpa only [List.append_nil, spec] using spec_equal_prefix xs [] h

theorem byte_difference (a b : BitVec 8) :
    (a.setWidth 32 - b.setWidth 32).toInt = (a.toNat : Int) - b.toNat := by
  have widen (v : BitVec 8) : (v.setWidth 32).toInt = (v.toNat : Int) := by
    rw [BitVec.toInt_setWidth]
    have hv := v.isLt
    exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [BitVec.toInt_sub, widen a, widen b]
  have ha := a.isLt
  have hb := b.isLt
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- Kernel-proved zero flag characterization, without a decision oracle. -/
theorem sub_equal (a b : BitVec 32) :
    (AddWithCarry a (~~~b) 1#1).2.z = 1#1 ↔ a = b := by
  have hv : (AddWithCarry a (~~~b) 1#1).1 = a - b := by
    simp only [fst_AddWithCarry_eq_sub_neg, BitVec.not_not]
  change (if (AddWithCarry a (~~~b) 1#1).1 = 0#32 then 1#1 else 0#1) = 1#1 ↔ _
  rw [hv]
  by_cases h : a = b
  · simp [h]
  · have hz : a - b ≠ 0#32 := by bv_omega
    simp [hz, h]

end SszArm.Memcmp
