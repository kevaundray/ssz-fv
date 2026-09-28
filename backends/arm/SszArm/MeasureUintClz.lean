import SszArm.MeasureUintCountExec

namespace SszArm.Measure.Uint

structure ClzFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ≠ 9#5 → reg ≠ 10#5 →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  flags : ∀ flag, r (.FLAG flag) t = r (.FLAG flag) s
  memory : t.mem = s.mem

theorem ClzFrame.refl (s : ArmState) : ClzFrame s s :=
  ⟨rfl, rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

theorem ClzFrame.trans {s t u : ArmState} (left : ClzFrame s t) (right : ClzFrame t u) :
    ClzFrame s u :=
  ⟨right.program.trans left.program, right.error.trans left.error,
   fun reg h9 h10 => (right.registers reg h9 h10).trans (left.registers reg h9 h10),
   fun reg => (right.vectors reg).trans (left.vectors reg),
   fun flag => (right.flags flag).trans (left.flags flag), right.memory.trans left.memory⟩

theorem ClzFrame.aligned {s t : ArmState} (frame : ClzFrame s t)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  have stack := frame.registers 31#5 (by decide) (by decide)
  simpa only [CheckSPAlignment, state_simp_rules, stack] using aligned

def clzRoundOps : List CountOp := [.p2228, .p2232, .p2236]

theorem clz_round (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2228#64) :
    run 3 s = countBlock base clzRoundOps s ∧ ClzFrame s (countBlock base clzRoundOps s) := by
  constructor
  · apply count_run base clzRoundOps s code error aligned
    have pc' : r .PC s = base + 2228#64 := pc
    simp [clzRoundOps, CountFollows, CountOp.row, CountOp.effect, put, next,
      Emit.Dispatch.next, state_simp_rules, pc', BitVec.add_assoc]
  · constructor
    · simp [countBlock, clzRoundOps]
    · simp [countBlock, clzRoundOps]
    · intro reg h9 h10
      simp [countBlock, clzRoundOps, CountOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules, h9, h10]
    · intro reg
      simp [countBlock, clzRoundOps, CountOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules]
    · intro flag
      simp [countBlock, clzRoundOps, CountOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules]
    · simp [countBlock, clzRoundOps, CountOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules]

theorem count_shift_add (limbWord : BitVec 64) (left right : Nat) :
    (limbWord >>> left) >>> right = limbWord >>> (left + right) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index bound
  simp [Nat.add_comm, Nat.add_left_comm]

/-- Executes the shipped one-bit shift loop, not an abstract CLZ instruction. -/
theorem clz_loop (base : BitVec 64) :
    ∀ n (s : ArmState), CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = (if n = 0 then base + 2240#64 else base + 2228#64) →
      (∀ i < n, r (.GPR 9#5) s >>> i ≠ 0#64) →
      r (.GPR 9#5) s >>> n = 0#64 →
      ∃ t, run (3 * n) s = t ∧ ClzFrame s t ∧
        read_pc t = base + 2240#64 ∧ r (.GPR 9#5) t = 0#64 ∧
        r (.GPR 10#5) t = r (.GPR 10#5) s - BitVec.ofNat 64 n := by
  intro n
  induction n with
  | zero =>
    intro s code error aligned pc before zero
    refine ⟨s, rfl, ClzFrame.refl s, ?_, ?_, ?_⟩
    · simpa using pc
    · simpa using zero
    · simp
  | succ n ih =>
    intro s code error aligned pc before zero
    let u := countBlock base clzRoundOps s
    obtain ⟨executed, frame⟩ := clz_round s base code error aligned (by simpa using pc)
    have shift : r (.GPR 9#5) u = r (.GPR 9#5) s >>> 1 := by
      simp [u, countBlock, clzRoundOps, CountOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules]
    have counter : r (.GPR 10#5) u = r (.GPR 10#5) s - 1#64 := by
      simp [u, countBlock, clzRoundOps, CountOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules]
    have nextPC : read_pc u = if n = 0 then base + 2240#64 else base + 2228#64 := by
      by_cases empty : n = 0
      · subst n
        simp only [Nat.zero_add] at zero
        simp [u, countBlock, clzRoundOps, CountOp.effect, put, next, Emit.Dispatch.next,
          state_simp_rules, zero]
      · have nonzero := before 1 (by omega)
        simp [u, countBlock, clzRoundOps, CountOp.effect, put, next, Emit.Dispatch.next,
          state_simp_rules, empty, nonzero]
    have nextBefore : ∀ i < n, r (.GPR 9#5) u >>> i ≠ 0#64 := by
      intro i bound
      rw [shift, count_shift_add]
      exact before (1 + i) (by omega)
    have nextZero : r (.GPR 9#5) u >>> n = 0#64 := by
      rw [shift, count_shift_add, Nat.add_comm 1 n]
      exact zero
    obtain ⟨t, resultRun, resultFrame, resultPC, resultZero, resultCounter⟩ :=
      ih u (code.congr frame.program) (frame.error.trans error) (frame.aligned aligned)
        nextPC nextBefore nextZero
    refine ⟨t, ?_, frame.trans resultFrame, resultPC, resultZero, ?_⟩
    · rw [show 3 * (n + 1) = 3 + 3 * n by omega, run_plus, executed, resultRun]
    · rw [resultCounter, counter]
      bv_omega

theorem bitLength_shift_facts (limbWord : BitVec 64) :
    let bits := SszNative.Serialize.bitLength limbWord.toNat
    bits ≤ 64 ∧ limbWord >>> bits = 0#64 ∧ ∀ i < bits, limbWord >>> i ≠ 0#64 := by
  dsimp
  by_cases zero : limbWord.toNat = 0
  · have wordZero : limbWord = 0#64 := BitVec.eq_of_toNat_eq (by simpa using zero)
    simp [SszNative.Serialize.bitLength, zero, wordZero]
  · have upper := limbWord.isLt
    have logBound : limbWord.toNat.log2 < 64 := (Nat.log2_lt zero).2 upper
    simp only [SszNative.Serialize.bitLength, zero, ↓reduceIte]
    refine ⟨by omega, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.zero_mod,
        Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt Nat.lt_log2_self
    · intro i bound shifted
      have power : 2 ^ i ≤ limbWord.toNat := (Nat.le_log2 zero).1 (by omega)
      have shiftedNat := congrArg BitVec.toNat shifted
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.zero_mod,
        Nat.shiftRight_eq_div_pow] at shiftedNat
      have positive : 0 < limbWord.toNat / 2 ^ i := Nat.div_pos power (Nat.two_pow_pos i)
      omega

end SszArm.Measure.Uint
