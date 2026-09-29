import SszArm.IndicesLinkedNatShr
import SszArm.IndicesLinkedCeilShift
import SszArm.MeasureUintClz

set_option autoImplicit false

namespace SszArm.Indices.NatShr.Clz

/-- Three actual consecutive instructions inside each original function. This
is an instruction slice, not an invented callable CLZ helper. -/
def rows : List (Nat × BitVec 32) :=
  [(0, 0xd100054a#32), (4, 0xd341fd29#32), (8, 0xb5ffffc9#32)]

def CodeAt (s : ArmState) (pc : BitVec 64) : Prop := Codec.Linked.WordsAt rows s pc

theorem shr_code (s : ArmState) (base : BitVec 64) (code : Linked.NatShr.CodeAt s base) :
    CodeAt s (base + 124#64) := by
  intro row member
  simp only [rows, List.mem_cons, List.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · simpa only [BitVec.add_zero] using
      Linked.NatShr.chunk0_codeAt code (124, 0xd100054a#32) (by decide)
  · simpa only [BitVec.add_assoc] using
      Linked.NatShr.chunk0_codeAt code (128, 0xd341fd29#32) (by decide)
  · simpa only [BitVec.add_assoc] using
      Linked.NatShr.chunk0_codeAt code (132, 0xb5ffffc9#32) (by decide)

theorem ceil_code (s : ArmState) (base : BitVec 64) (code : Linked.CeilShift.CodeAt s base) :
    CodeAt s (base + 204#64) := by
  intro row member
  simp only [rows, List.mem_cons, List.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · simpa only [BitVec.add_zero] using
      Linked.CeilShift.chunk0_codeAt code (204, 0xd100054a#32) (by decide)
  · simpa only [BitVec.add_assoc] using
      Linked.CeilShift.chunk0_codeAt code (208, 0xd341fd29#32) (by decide)
  · simpa only [BitVec.add_assoc] using
      Linked.CeilShift.chunk0_codeAt code (212, 0xb5ffffc9#32) (by decide)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def decrement (s : ArmState) : ArmState :=
  w (.GPR 10#5) (r (.GPR 10#5) s - 1#64) (next s)

def shift (s : ArmState) : ArmState :=
  w (.GPR 9#5) (r (.GPR 9#5) s >>> 1) (next s)

def branch (s : ArmState) : ArmState :=
  w .PC (if r (.GPR 9#5) s = 0#64 then read_pc s + 4#64 else read_pc s - 8#64) s

def round (s : ArmState) : ArmState := branch (shift (decrement s))

theorem decrement_step (s : ArmState) (pc : BitVec 64)
    (code : CodeAt s pc) (error : read_err s = .None) (entry : read_pc s = pc) :
    stepi s = decrement s := by
  have fetched := code (0, 0xd100054a#32) (by decide)
  simp only [BitVec.add_zero] at fetched
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [decrement, next, exec_inst, state_simp_rules, bitvec_rules,
      minimal_theory, BitVec.sub_eq_add_neg]

theorem shift_step (s : ArmState) (pc : BitVec 64)
    (code : CodeAt s pc) (error : read_err s = .None) (entry : read_pc s = pc + 4#64) :
    stepi s = shift s := by
  have fetched := code (4, 0xd341fd29#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [shift, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem branch_step (s : ArmState) (pc : BitVec 64)
    (code : CodeAt s pc) (error : read_err s = .None) (entry : read_pc s = pc + 8#64) :
    stepi s = branch s := by
  have fetched := code (8, 0xb5ffffc9#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [branch, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BitVec.sub_eq_add_neg]

theorem round_frame (s : ArmState) : Measure.Uint.ClzFrame s (round s) := by
  constructor
  · simp [round, branch, shift, decrement, next, state_simp_rules]
  · simp [round, branch, shift, decrement, next, state_simp_rules]
  · intro reg notInput notCounter
    simp [round, branch, shift, decrement, next, state_simp_rules, notInput, notCounter]
  · intro reg
    simp [round, branch, shift, decrement, next, state_simp_rules]
  · intro flag
    simp [round, branch, shift, decrement, next, state_simp_rules]
  · simp [round, branch, shift, decrement, next, state_simp_rules]

theorem round_run (s : ArmState) (pc : BitVec 64)
    (code : CodeAt s pc) (error : read_err s = .None) (entry : read_pc s = pc) :
    run 3 s = round s := by
  have dc : CodeAt (decrement s) pc := by
    simpa only [CodeAt, Codec.Linked.WordsAt, decrement, next, state_simp_rules] using code
  have de : read_err (decrement s) = .None := by
    simpa [decrement, next, state_simp_rules] using error
  have dp : read_pc (decrement s) = pc + 4#64 := by
    simp [decrement, next, state_simp_rules, entry]
  have sc : CodeAt (shift (decrement s)) pc := by
    simpa only [CodeAt, Codec.Linked.WordsAt, shift, decrement, next, state_simp_rules] using code
  have se : read_err (shift (decrement s)) = .None := by
    simpa [shift, decrement, next, state_simp_rules] using error
  have sp : read_pc (shift (decrement s)) = pc + 8#64 := by
    simp [shift, decrement, next, state_simp_rules, entry, BitVec.add_assoc]
  change run 2 (stepi s) = _
  rw [decrement_step s pc code error entry]
  change run 1 (stepi (decrement s)) = _
  rw [shift_step _ pc dc de dp]
  change stepi (shift (decrement s)) = _
  exact branch_step _ pc sc se sp

theorem round_input (s : ArmState) :
    r (.GPR 9#5) (round s) = r (.GPR 9#5) s >>> 1 := by
  simp [round, branch, shift, decrement, next, state_simp_rules]

theorem round_counter (s : ArmState) :
    r (.GPR 10#5) (round s) = r (.GPR 10#5) s - 1#64 := by
  simp [round, branch, shift, decrement, next, state_simp_rules]

theorem round_pc (s : ArmState) (pc : BitVec 64) (entry : read_pc s = pc) :
    read_pc (round s) = if r (.GPR 9#5) s >>> 1 = 0#64 then pc + 12#64 else pc := by
  simp [round, branch, shift, decrement, next, state_simp_rules, entry,
    BitVec.add_assoc, BitVec.sub_eq_add_neg]

/-- Finite actual execution, with loop termination supplied by a physical limb's
bit length at the call site rather than an assumed continuation result. -/
theorem loop (pc : BitVec 64) :
    ∀ n (s : ArmState), CodeAt s pc → read_err s = .None →
      read_pc s = (if n = 0 then pc + 12#64 else pc) →
      (∀ i < n, r (.GPR 9#5) s >>> i ≠ 0#64) →
      r (.GPR 9#5) s >>> n = 0#64 →
      ∃ t, run (3 * n) s = t ∧ Measure.Uint.ClzFrame s t ∧
        read_pc t = pc + 12#64 ∧ r (.GPR 9#5) t = 0#64 ∧
        r (.GPR 10#5) t = r (.GPR 10#5) s - BitVec.ofNat 64 n := by
  intro n
  induction n with
  | zero =>
      intro s code error entry before zero
      exact ⟨s, rfl, Measure.Uint.ClzFrame.refl s, by simpa using entry,
        by simpa using zero, by simp⟩
  | succ n ih =>
      intro s code error entry before zero
      have pcNow : read_pc s = pc := by simpa using entry
      have executed := round_run s pc code error pcNow
      have frame := round_frame s
      have nextPC : read_pc (round s) = if n = 0 then pc + 12#64 else pc := by
        rw [round_pc s pc pcNow]
        by_cases empty : n = 0
        · subst n
          simpa using congrArg (fun value : BitVec 64 =>
            if value = 0#64 then pc + 12#64 else pc) zero
        · simp [empty, before 1 (by omega)]
      have nextBefore : ∀ i < n, r (.GPR 9#5) (round s) >>> i ≠ 0#64 := by
        intro i bound
        rw [round_input, Measure.Uint.count_shift_add]
        exact before (1 + i) (by omega)
      have nextZero : r (.GPR 9#5) (round s) >>> n = 0#64 := by
        rw [round_input, Measure.Uint.count_shift_add, Nat.add_comm 1 n]
        exact zero
      have nextCode : CodeAt (round s) pc := Codec.Linked.WordsAt.preserve code frame.program
      obtain ⟨t, runTail, tailFrame, tailPC, tailZero, tailCounter⟩ :=
        ih _ nextCode (frame.error.trans error) nextPC nextBefore nextZero
      refine ⟨t, ?_, frame.trans tailFrame, tailPC, tailZero, ?_⟩
      · rw [show 3 * (n + 1) = 3 + 3 * n by omega, run_plus, executed, runTail]
      · rw [tailCounter, round_counter]
        simp [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.add_comm, BitVec.add_left_comm]

end SszArm.Indices.NatShr.Clz
