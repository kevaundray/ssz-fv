import SszArm.CodecDecodeNatCmpRead

namespace SszArm.Codec.Decode.NatCmpUsize

open SszNative.Limbs

/-- Actual pc72 returns Greater directly; pc120 runs the wide comparison. -/
def Ready (base : BitVec 64) (operand : SszNative.NatOperand) (s : ArmState) : Prop :=
  (read_pc s = base + 72#64 ∧ 2 ^ 128 ≤ operand.value) ∨
  (read_pc s = base + 120#64 ∧ wideValue s = operand.value)

theorem large_entry_scan (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (owned : Owned s (.large pointer words))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
      read_pc t = base + BitVec.ofNat 64 (if sigWords words = 0 then 80 else 60) ∧
      (sigWords words ≠ 0 → r (.GPR 8#5) t = BitVec.ofNat 64 (sigWords words - 1)) := by
  have pointerAt : r (.GPR 0#5) s = pointer := owned.operandPointer
  have countAt : r (.GPR 1#5) s = BitVec.ofNat 64 words.length := owned.operandPayload
  have nonzero : pointer ≠ 0#64 := by
    intro equal
    have positive := owned.operandAt.1
    simp [equal] at positive
  let ops : List Op := [.p0, .p4]
  let u := block base ops s
  change r .PC s = base at pc
  have follows : Follows base ops s := by
    simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      pc, pointerAt, nonzero, BitVec.add_assoc]
  have execution : run 2 s = u := block_run base ops s code error aligned follows
  have frame : NatNarrow.Frame s u := scan_pure_frame base ops s (by decide)
  have nextPC : read_pc u = base + 8#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, pointerAt, nonzero, BitVec.add_assoc]
  have nextPointer : r (.GPR 0#5) u = pointer := (frame.registers _ (by decide)).trans pointerAt
  have nextIndex : r (.GPR 9#5) u = BitVec.ofNat 64 words.length - 1#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, countAt]
  obtain ⟨fuel, t, runScan, scanFrame, keep, target, count⟩ :=
    significant_scan base pointer words words.length u (Nat.le_refl _)
      (frame_code frame code) (frame.error.trans error) (frame.aligned aligned)
      nextPC nextPointer nextIndex (frame.source _ _ owned.large_source)
      (frame.words _ _ owned.large_source owned.large_words)
  refine ⟨2 + fuel, t, ?_, frame.trans scanFrame, target, count⟩
  rw [run_plus, execution, runScan]

/-- Raw input representation determines a finite continuation. The proof
performs the actual descending loop; no canonicality or future-run premise. -/
theorem entry_ready (s : ArmState) (base : BitVec 64) (operand : SszNative.NatOperand)
    (owned : Owned s operand) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready base operand t := by
  cases operand with
  | small scalar =>
    have pointerAt : r (.GPR 0#5) s = 0#64 := owned.operandPointer
    have countAt : r (.GPR 1#5) s = scalar := owned.operandPayload
    let ops : List Op := [.p0, .p104, .p108]
    change r .PC s = base at pc
    have follows : Follows base ops s := by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
        pc, pointerAt, BitVec.add_assoc]
    refine ⟨3, block base ops s, block_run base ops s code error aligned follows,
      readonly_frame base ops s (by decide), Or.inr ⟨?_, ?_⟩⟩
    · simp [ops, block, Op.effect, put, next, state_simp_rules]
    · simp [wideValue, Measure.Uint.pairValue, ops, block, Op.effect, put, next,
        state_simp_rules, countAt, SszNative.NatOperand.value, SszNative.NatOperand.words, value]
  | large pointer words =>
    obtain ⟨fuel, u, execution, frame, nextPC, count⟩ :=
      large_entry_scan s base pointer words owned code error aligned pc
    have pointerAt : r (.GPR 0#5) u = pointer :=
      (frame.registers _ (by decide)).trans owned.operandPointer
    have countAt : r (.GPR 1#5) u = BitVec.ofNat 64 words.length :=
      (frame.registers _ (by decide)).trans owned.operandPayload
    have source := frame.source _ _ owned.large_source
    have stored := frame.words _ _ owned.large_source owned.large_words
    have countBound : words.length < 2 ^ 64 := by have := source.2.1; omega
    have finishRead (v : ArmState) (steps : Nat) (executed : run steps u = v)
        (phase : NatNarrow.Frame u v) (target : read_pc v = base + 84#64)
        (nonempty : 0 < words.length) (fits : sigWords words ≤ 2) :
        ∃ total t, run total s = t ∧ Frame s t ∧ Ready base (.large pointer words) t := by
      obtain ⟨rest, t, decoded, resultFrame, returnedPC, result⟩ :=
        large_read v base pointer words nonempty fits (frame_code (frame.trans phase) code)
          ((frame.trans phase).error.trans error) ((frame.trans phase).aligned aligned) target
          ((phase.registers _ (by decide)).trans pointerAt)
          ((phase.registers _ (by decide)).trans countAt)
          (phase.source _ _ source) (phase.words _ _ source stored)
      refine ⟨fuel + steps + rest, t, ?_,
        (scan_frame (frame.trans phase)).trans resultFrame, Or.inr ⟨returnedPC, result⟩⟩
      rw [run_plus, run_plus, execution, executed, decoded]
    by_cases zero : sigWords words = 0
    · have target : read_pc u = base + 80#64 := by simpa [zero] using nextPC
      let v := block base [.p80] u
      have executed : run 1 u = v := block_run base [.p80] u (frame_code frame code)
        (frame.error.trans error) (frame.aligned aligned)
        (by simpa [Follows, Op.row] using target)
      have phase : NatNarrow.Frame u v := scan_pure_frame base [.p80] u (by decide)
      by_cases empty : words.length = 0
      · have nil : words = [] := List.eq_nil_of_length_eq_zero empty
        let ops : List Op := [.p104, .p108]
        have vPC : read_pc v = base + 104#64 := by
          simp [v, block, Op.effect, state_simp_rules, countAt, empty]
        have follows : Follows base ops v := by
          change r .PC v = _ at vPC
          simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules, vPC, BitVec.add_assoc]
        have finish := block_run base ops v (frame_code (frame.trans phase) code)
          ((frame.trans phase).error.trans error) ((frame.trans phase).aligned aligned) follows
        change run 2 v = block base ops v at finish
        refine ⟨fuel + 1 + 2, block base ops v, ?_,
          (scan_frame (frame.trans phase)).trans (readonly_frame base ops v (by decide)),
          Or.inr ⟨?_, ?_⟩⟩
        · rw [run_plus, run_plus, execution, executed, finish]
        · simp [ops, block, Op.effect, put, next, state_simp_rules]
        · simp [wideValue, Measure.Uint.pairValue, ops, v, block, Op.effect, put, next,
            state_simp_rules, countAt, nil, SszNative.NatOperand.value,
            SszNative.NatOperand.words, value]
      · have countNonzero : BitVec.ofNat 64 words.length ≠ 0#64 := by bv_omega
        exact finishRead v 1 executed phase
          (by simp [v, block, Op.effect, state_simp_rules, countAt, countNonzero])
          (by omega) (by omega)
    · have target : read_pc u = base + 60#64 := by simpa [zero] using nextPC
      have observed := count zero
      have sigBound : sigWords words < 2 ^ 64 := by have := sigWords_le_length words; omega
      have increment : BitVec.ofNat 64 (sigWords words - 1) + 1#64 =
          BitVec.ofNat 64 (sigWords words) := by bv_omega
      let ops : List Op := [.p60, .p64, .p68]
      let v := block base ops u
      change r .PC u = _ at target
      have executed : run 3 u = v := block_run base ops u (frame_code frame code)
        (frame.error.trans error) (frame.aligned aligned)
        (by simp [ops, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
          Udivti3.next, state_simp_rules, target, BitVec.add_assoc])
      have phase : NatNarrow.Frame u v := scan_pure_frame base ops u (by decide)
      have carry : (AddWithCarry (BitVec.ofNat 64 (sigWords words)) (~~~3#64) 1#1).2.c = 1#1 ↔
          3 ≤ sigWords words := by
        rw [Udivti3.cmp_carry]
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sigBound]
      change (AddWithCarry (BitVec.ofNat 64 (sigWords words)) 18446744073709551612#64 1#1).2.c =
        1#1 ↔ 3 ≤ sigWords words at carry
      by_cases fits : sigWords words ≤ 2
      · exact finishRead v 3 executed phase
          (by simp [v, ops, block, Op.effect, put, next, Udivti3.compare,
            Udivti3.next, state_simp_rules, observed, increment, carry,
            show ¬ 3 ≤ sigWords words by omega])
          (by have := sigWords_le_length words; omega) fits
      · refine ⟨fuel + 3, v, ?_, scan_frame (frame.trans phase), Or.inl ⟨?_, ?_⟩⟩
        · rw [run_plus, execution, executed]
        · simp [v, ops, block, Op.effect, put, next, Udivti3.compare,
            Udivti3.next, state_simp_rules, observed, increment, carry,
            show 3 ≤ sigWords words by omega]
        · apply (SszNative.NatNarrow.toU128_none_iff _).mp
          simp [SszNative.NatNarrow.toU128, SszNative.NatOperand.wordCount,
            SszNative.NatOperand.words, fits]

end SszArm.Codec.Decode.NatCmpUsize
