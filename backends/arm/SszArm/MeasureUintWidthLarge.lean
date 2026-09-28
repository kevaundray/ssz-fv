import SszArm.MeasureUintWidthRead

namespace SszArm.Measure.Uint

open SszNative.Limbs

/-- The actual scan distinguishes widths requiring more than two limbs, without
restricting the descriptor's logical value or its physical high-zero padding. -/
theorem width_large_ready (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2748#64)
    (pointerReg : r (.GPR 21#5) s = pointer)
    (countReg : r (.GPR 20#5) s = BitVec.ofNat 64 words.length)
    (index : r (.GPR 11#5) s = BitVec.ofNat 64 words.length - 1#64)
    (source : NatCompare.Source s pointer words) (memory : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
      read_pc t = (if 2 < sigWords words then base + 4144#64 else base + 3912#64) ∧
      (sigWords words ≤ 2 →
        pairValue (r (.GPR 10#5) t) (r (.GPR 11#5) t) = SszNative.Limbs.value words) ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s := by
  obtain ⟨fuel, u, executed, frame, nextPointer, nextPC, top, nextLow, nextHigh⟩ :=
    width_scan base pointer words words.length s (Nat.le_refl _) code error aligned
      pc pointerReg index source memory
  have nextCount : r (.GPR 20#5) u = BitVec.ofNat 64 words.length :=
    (frame.registers 20#5 (by decide)).trans countReg
  have bound : words.length < 2^64 := by have := source.2.1; omega
  have finishRead (v : ArmState) (extra : Nat) (runPrefix : run extra u = v)
      (prefixFrame : NatNarrow.Frame u v) (readPC : read_pc v = base + 2880#64)
      (nonempty : 0 < words.length) (fits : sigWords words ≤ 2)
      (low : r (.GPR 8#5) v = r (.GPR 8#5) u)
      (high : r (.GPR 9#5) v = r (.GPR 9#5) u) :
      ∃ total t, run total s = t ∧ NatNarrow.Frame s t ∧
        read_pc t = (if 2 < sigWords words then base + 4144#64 else base + 3912#64) ∧
        (sigWords words ≤ 2 →
          pairValue (r (.GPR 10#5) t) (r (.GPR 11#5) t) = SszNative.Limbs.value words) ∧
        r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s := by
    have totalFrame := frame.trans prefixFrame
    obtain ⟨t, readRun, readFrame, resultPC, resultValue, resultLow, resultHigh⟩ :=
      width_read v base pointer words (code.congr totalFrame.program)
        (totalFrame.error.trans error) (totalFrame.aligned aligned) readPC
        ((prefixFrame.registers 21#5 (by decide)).trans nextPointer)
        ((prefixFrame.registers 20#5 (by decide)).trans nextCount)
        (totalFrame.source _ _ source) (totalFrame.words _ _ source memory) nonempty fits
    refine ⟨fuel + extra + 5, t, ?_, totalFrame.trans readFrame, ?_, fun _ => resultValue,
      resultLow.trans (low.trans nextLow), resultHigh.trans (high.trans nextHigh)⟩
    · rw [run_plus, run_plus, executed, runPrefix, readRun]
    · simpa [show ¬ 2 < sigWords words by omega] using resultPC
  change read_pc u = base + BitVec.ofNat 64 (if sigWords words = 0 then 2876 else 2800) at nextPC
  by_cases zero : sigWords words = 0
  · have zeroPC : read_pc u = base + 2876#64 := by simpa only [if_pos zero] using nextPC
    have zeroPC' : r .PC u = base + 2876#64 := zeroPC
    by_cases empty : words.length = 0
    · have wordsEmpty : words = [] := List.eq_nil_of_length_eq_zero empty
      let ops : List WidthOp := [.p2876, .p3904, .p3908]
      let t := widthBlock base ops u
      have follows : WidthFollows base ops u := by
        simp [ops, WidthFollows, WidthOp.row, WidthOp.effect, put, next, Emit.Dispatch.next,
          state_simp_rules, zeroPC', nextCount, empty, BitVec.add_assoc]
      have tailRun : run 3 u = t := width_run base ops u (code.congr frame.program)
        (frame.error.trans error) (frame.aligned aligned) follows
      refine ⟨fuel + 3, t, ?_, frame.trans (width_pure_frame base _ u (by decide)), ?_, ?_, ?_, ?_⟩
      · rw [run_plus, executed, tailRun]
      · simp [t, ops, widthBlock, WidthOp.effect, put, next, Emit.Dispatch.next,
          state_simp_rules, nextCount, empty, zero, BitVec.add_assoc]
      · intro fits
        simp [t, ops, widthBlock, WidthOp.effect, put, next, Emit.Dispatch.next,
          state_simp_rules, wordsEmpty, pairValue, SszNative.Limbs.value]
      · simpa [t, ops, widthBlock, WidthOp.effect, put, next, Emit.Dispatch.next,
          state_simp_rules] using nextLow
      · simpa [t, ops, widthBlock, WidthOp.effect, put, next, Emit.Dispatch.next,
          state_simp_rules] using nextHigh
    · have nonzero : BitVec.ofNat 64 words.length ≠ 0#64 := by bv_omega
      let v := widthBlock base [.p2876] u
      have tailRun : run 1 u = v := width_run base [.p2876] u (code.congr frame.program)
        (frame.error.trans error) (frame.aligned aligned) ⟨zeroPC, trivial⟩
      apply finishRead v 1 tailRun (width_pure_frame base _ u (by decide))
      · simp [v, widthBlock, WidthOp.effect, state_simp_rules, nextCount, nonzero]
      · omega
      · omega
      · simp [v, widthBlock, WidthOp.effect, state_simp_rules]
      · simp [v, widthBlock, WidthOp.effect, state_simp_rules]
  · have count : r (.GPR 10#5) u = BitVec.ofNat 64 (sigWords words - 1) := top zero
    have positive : 0 < sigWords words := by omega
    have sigBound : sigWords words < 2^64 := by have := sigWords_le_length words; omega
    have increment : BitVec.ofNat 64 (sigWords words - 1) + 1#64 =
        BitVec.ofNat 64 (sigWords words) := by bv_omega
    have carry : (AddWithCarry (BitVec.ofNat 64 (sigWords words)) (~~~3#64) 1#1).2.c = 1#1 ↔
        3 ≤ sigWords words := by
      rw [Udivti3.cmp_carry]
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sigBound]
    have branchCarry :
        (AddWithCarry (BitVec.ofNat 64 (sigWords words)) 18446744073709551612#64 1#1).2.c = 1#1 ↔
          3 ≤ sigWords words := carry
    have scanPC : read_pc u = base + 2800#64 := by simpa only [if_neg zero] using nextPC
    have scanPC' : r .PC u = base + 2800#64 := scanPC
    by_cases fits : sigWords words ≤ 2
    · let ops : List WidthOp := [.p2800, .p2804, .p2808, .p2812]
      let v := widthBlock base ops u
      have follows : WidthFollows base ops u := by
        simp [ops, WidthFollows, WidthOp.row, WidthOp.effect, put, next, compare64,
          Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules, scanPC',
          count, increment, branchCarry, show ¬ 3 ≤ sigWords words by omega, BitVec.add_assoc]
      have tailRun : run 4 u = v := width_run base ops u (code.congr frame.program)
        (frame.error.trans error) (frame.aligned aligned) follows
      apply finishRead v 4 tailRun (width_pure_frame base _ u (by decide))
      · simp [v, ops, widthBlock, WidthOp.effect, put, next, compare64,
          Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules]
      · have := sigWords_le_length words; omega
      · exact fits
      · simp [v, ops, widthBlock, WidthOp.effect, put, next, compare64,
          Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules]
      · simp [v, ops, widthBlock, WidthOp.effect, put, next, compare64,
          Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules]
    · let ops : List WidthOp := [.p2800, .p2804, .p2808]
      let t := widthBlock base ops u
      have follows : WidthFollows base ops u := by
        simp [ops, WidthFollows, WidthOp.row, WidthOp.effect, put, next, compare64,
          Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules, scanPC', BitVec.add_assoc]
      have tailRun : run 3 u = t := width_run base ops u (code.congr frame.program)
        (frame.error.trans error) (frame.aligned aligned) follows
      refine ⟨fuel + 3, t, ?_, frame.trans (width_pure_frame base _ u (by decide)), ?_, ?_, ?_, ?_⟩
      · rw [run_plus, executed, tailRun]
      · simp [t, ops, widthBlock, WidthOp.effect, put, next, compare64,
          Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules, count, increment,
          branchCarry, show 3 ≤ sigWords words by omega, show 2 < sigWords words by omega]
      · exact fun impossible => False.elim (fits impossible)
      · simpa [t, ops, widthBlock, WidthOp.effect, put, next, compare64,
          Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules] using nextLow
      · simpa [t, ops, widthBlock, WidthOp.effect, put, next, compare64,
          Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules] using nextHigh

end SszArm.Measure.Uint
