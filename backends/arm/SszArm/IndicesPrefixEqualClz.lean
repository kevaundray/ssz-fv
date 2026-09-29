import SszArm.IndicesLinkedPrefixEqual
import SszArm.MeasureUintClz

namespace SszArm.Indices.PrefixEqual.Clz

/-- Both lowered CLZ loops in the complete comparator image. -/
inductive Side where
  | left | right
  deriving DecidableEq

def Side.input : Side → BitVec 5
  | .left => 10
  | .right => 9

def Side.counter : Side → BitVec 5
  | .left => 11
  | .right => 10

def Side.offset : Side → Nat
  | .left => 132
  | .right => 352

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def decrement (side : Side) (s : ArmState) : ArmState :=
  w (.GPR side.counter) (r (.GPR side.counter) s - 1#64) (next s)

def shift (side : Side) (s : ArmState) : ArmState :=
  w (.GPR side.input) (r (.GPR side.input) s >>> 1) (next s)

def branch (side : Side) (s : ArmState) : ArmState :=
  w .PC (if r (.GPR side.input) s = 0#64 then read_pc s + 4#64 else read_pc s - 8#64) s

def round (side : Side) (s : ArmState) : ArmState :=
  branch side (shift side (decrement side s))

structure Frame (side : Side) (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ≠ side.input → reg ≠ side.counter →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  flags : ∀ flag, r (.FLAG flag) t = r (.FLAG flag) s
  memory : t.mem = s.mem

theorem Frame.refl (side : Side) (s : ArmState) : Frame side s s :=
  ⟨rfl, rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

theorem Frame.trans {side : Side} {s t u : ArmState}
    (first : Frame side s t) (second : Frame side t u) : Frame side s u :=
  ⟨second.program.trans first.program, second.error.trans first.error,
    fun reg a b => (second.registers reg a b).trans (first.registers reg a b),
    fun reg => (second.vectors reg).trans (first.vectors reg),
    fun flag => (second.flags flag).trans (first.flags flag),
    second.memory.trans first.memory⟩

theorem decrement_step (side : Side) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 side.offset) :
    stepi s = decrement side s := by
  cases side with
  | left =>
      have fetched := Linked.PrefixEqual.chunk0_codeAt code (132, 0xd100056b#32) (by decide)
      rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
        (fetch_inst_from_program.trans fetched) rfl]
      simp (config := {decide := true, instances := true})
        [decrement, Side.counter, next, exec_inst, state_simp_rules, bitvec_rules,
          minimal_theory, BitVec.sub_eq_add_neg]
  | right =>
      have fetched := Linked.PrefixEqual.chunk1_codeAt code (352, 0xd100054a#32) (by decide)
      rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
        (fetch_inst_from_program.trans fetched) rfl]
      simp (config := {decide := true, instances := true})
        [decrement, Side.counter, next, exec_inst, state_simp_rules, bitvec_rules,
          minimal_theory, BitVec.sub_eq_add_neg]

theorem shift_step (side : Side) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 (side.offset + 4)) :
    stepi s = shift side s := by
  cases side with
  | left =>
      have fetched := Linked.PrefixEqual.chunk0_codeAt code (136, 0xd341fd4a#32) (by decide)
      rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
        (fetch_inst_from_program.trans fetched) rfl]
      simp (config := {decide := true, instances := true})
        [shift, Side.input, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  | right =>
      have fetched := Linked.PrefixEqual.chunk1_codeAt code (356, 0xd341fd29#32) (by decide)
      rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
        (fetch_inst_from_program.trans fetched) rfl]
      simp (config := {decide := true, instances := true})
        [shift, Side.input, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem branch_step (side : Side) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 (side.offset + 8)) :
    stepi s = branch side s := by
  cases side with
  | left =>
      have fetched := Linked.PrefixEqual.chunk0_codeAt code (140, 0xb5ffffca#32) (by decide)
      rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
        (fetch_inst_from_program.trans fetched) rfl]
      simp (config := {decide := true, instances := true})
        [branch, Side.input, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
          BitVec.sub_eq_add_neg]
  | right =>
      have fetched := Linked.PrefixEqual.chunk1_codeAt code (360, 0xb5ffffc9#32) (by decide)
      rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
        (fetch_inst_from_program.trans fetched) rfl]
      simp (config := {decide := true, instances := true})
        [branch, Side.input, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
          BitVec.sub_eq_add_neg]

theorem round_frame (side : Side) (s : ArmState) : Frame side s (round side s) := by
  constructor
  · simp [round, branch, shift, decrement, next, state_simp_rules]
  · simp [round, branch, shift, decrement, next, state_simp_rules]
  · intro reg input counter
    simp [round, branch, shift, decrement, next, state_simp_rules, input, counter]
  · intro reg
    simp [round, branch, shift, decrement, next, state_simp_rules]
  · intro flag
    simp [round, branch, shift, decrement, next, state_simp_rules]
  · simp [round, branch, shift, decrement, next, state_simp_rules]

theorem round_run (side : Side) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 side.offset) :
    run 3 s = round side s := by
  have dc : Linked.PrefixEqual.CodeAt (decrement side s) base := by
    simpa only [Linked.PrefixEqual.CodeAt, Codec.Linked.WordsAt, decrement, next,
      state_simp_rules] using code
  have de : read_err (decrement side s) = .None := by
    simpa [decrement, next, state_simp_rules] using error
  have dp : read_pc (decrement side s) = base + BitVec.ofNat 64 (side.offset + 4) := by
    simp [decrement, next, state_simp_rules, pc, BitVec.ofNat_add, BitVec.add_assoc]
  have sc : Linked.PrefixEqual.CodeAt (shift side (decrement side s)) base := by
    simpa only [Linked.PrefixEqual.CodeAt, Codec.Linked.WordsAt, shift, decrement, next,
      state_simp_rules] using code
  have se : read_err (shift side (decrement side s)) = .None := by
    simpa [shift, decrement, next, state_simp_rules] using error
  have sp : read_pc (shift side (decrement side s)) =
      base + BitVec.ofNat 64 (side.offset + 8) := by
    simp [shift, decrement, next, state_simp_rules, pc, BitVec.ofNat_add, BitVec.add_assoc]
  change run 2 (stepi s) = _
  rw [decrement_step side s base code error pc]
  change run 1 (stepi (decrement side s)) = _
  rw [shift_step side _ base dc de dp]
  change stepi (shift side (decrement side s)) = _
  exact branch_step side _ base sc se sp

theorem round_input (side : Side) (s : ArmState) :
    r (.GPR side.input) (round side s) = r (.GPR side.input) s >>> 1 := by
  cases side <;> simp [round, branch, shift, decrement, next, Side.input, Side.counter,
    state_simp_rules]

theorem round_counter (side : Side) (s : ArmState) :
    r (.GPR side.counter) (round side s) = r (.GPR side.counter) s - 1#64 := by
  cases side <;> simp [round, branch, shift, decrement, next, Side.input, Side.counter,
    state_simp_rules]

theorem round_pc (side : Side) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 side.offset) :
    read_pc (round side s) = if r (.GPR side.input) s >>> 1 = 0#64 then
      base + BitVec.ofNat 64 (side.offset + 12) else base + BitVec.ofNat 64 side.offset := by
  cases side <;> simp [round, branch, shift, decrement, next, Side.input, Side.counter,
    Side.offset, state_simp_rules, pc, BitVec.add_assoc, BitVec.sub_eq_add_neg]

/-- Exact finite execution of either real loop. No future execution or frame
premise is used: the bound is discharged from the supplied limb's bit length. -/
theorem loop (side : Side) (base : BitVec 64) :
    ∀ n (s : ArmState), Linked.PrefixEqual.CodeAt s base → read_err s = .None →
      read_pc s = (if n = 0 then base + BitVec.ofNat 64 (side.offset + 12)
        else base + BitVec.ofNat 64 side.offset) →
      (∀ i < n, r (.GPR side.input) s >>> i ≠ 0#64) →
      r (.GPR side.input) s >>> n = 0#64 →
      ∃ t, run (3 * n) s = t ∧ Frame side s t ∧
        read_pc t = base + BitVec.ofNat 64 (side.offset + 12) ∧
        r (.GPR side.input) t = 0#64 ∧
        r (.GPR side.counter) t = r (.GPR side.counter) s - BitVec.ofNat 64 n := by
  intro n
  induction n with
  | zero =>
      intro s code error pc before zero
      exact ⟨s, rfl, Frame.refl side s, by simpa using pc,
        by simpa using zero, by simp⟩
  | succ n ih =>
      intro s code error pc before zero
      have entry : read_pc s = base + BitVec.ofNat 64 side.offset := by simpa using pc
      have executed := round_run side s base code error entry
      have frame := round_frame side s
      have nextPC : read_pc (round side s) =
          if n = 0 then base + BitVec.ofNat 64 (side.offset + 12)
          else base + BitVec.ofNat 64 side.offset := by
        rw [round_pc side s base entry]
        by_cases empty : n = 0
        · subst n
          simpa using congrArg (fun value : BitVec 64 =>
            if value = 0#64 then base + BitVec.ofNat 64 (side.offset + 12)
            else base + BitVec.ofNat 64 side.offset) zero
        · simp [empty, before 1 (by omega)]
      have nextBefore : ∀ i < n, r (.GPR side.input) (round side s) >>> i ≠ 0#64 := by
        intro i bound
        rw [round_input, Measure.Uint.count_shift_add]
        exact before (1 + i) (by omega)
      have nextZero : r (.GPR side.input) (round side s) >>> n = 0#64 := by
        rw [round_input, Measure.Uint.count_shift_add, Nat.add_comm 1 n]
        exact zero
      have nextCode : Linked.PrefixEqual.CodeAt (round side s) base :=
        Codec.Linked.WordsAt.preserve code frame.program
      obtain ⟨t, runTail, tailFrame, tailPC, tailZero, tailCounter⟩ :=
        ih _ nextCode (frame.error.trans error) nextPC nextBefore nextZero
      refine ⟨t, ?_, frame.trans tailFrame, tailPC, tailZero, ?_⟩
      · rw [show 3 * (n + 1) = 3 + 3 * n by omega, run_plus, executed, runTail]
      · rw [tailCounter, round_counter]
        simp [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.add_comm, BitVec.add_left_comm]

end SszArm.Indices.PrefixEqual.Clz
