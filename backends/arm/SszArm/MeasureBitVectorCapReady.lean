import SszArm.MeasureBitVectorCapSelect

namespace SszArm.Measure.BitVector

open SszNative.Limbs

private theorem cap_pair_value (words : List (BitVec 64)) (fits : sigWords words ≤ 2) :
    (words[0]?.getD 0#64).toNat + 2^64 * (words[1]?.getD 0#64).toNat = value words := by
  have bound := SszNative.NatDivision.value_lt_128 (SszNative.NatOperand.large 0#64 words) fits
  cases words with
  | nil => simp [value]
  | cons low rest =>
    cases rest with
    | nil => simp [value]
    | cons high rest =>
      simp only [SszNative.NatOperand.value, SszNative.NatOperand.words, value] at bound
      have zero : value rest = 0 := by omega
      simp [value, zero]

theorem cap_scanned_ready (s : ArmState) (base pointer : BitVec 64) (words : List (BitVec 64))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 592#64) (ptr : r (.GPR 11#5) s = pointer)
    (count : r (.GPR 10#5) s = BitVec.ofNat 64 words.length)
    (index : r (.GPR 13#5) s = BitVec.ofNat 64 words.length - 1#64)
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ CapFrame s t ∧
      read_pc t = (if 2 < sigWords words then base + 3320#64 else base + 3268#64) ∧
      (sigWords words ≤ 2 →
        (r (.GPR 10#5) t).toNat + 2^64 * (r (.GPR 11#5) t).toNat = value words) := by
  obtain ⟨fuel, u, executed, scanFrame, high, nextPC, top⟩ :=
    significant_scan base pointer words words.length s (Nat.le_refl _) code error aligned
      pc ptr index source stored
  change read_pc u = base + BitVec.ofNat 64
    (if sigWords words = 0 then 2828 else 644) at nextPC
  change (sigWords words ≠ 0 →
    r (.GPR 12#5) u = BitVec.ofNat 64 (sigWords words - 1)) at top
  have frame := CapFrame.of_scan scanFrame high
  have nextPointer : r (.GPR 11#5) u = pointer :=
    (scanFrame.registers 11#5 (by decide)).trans ptr
  have nextCount : r (.GPR 10#5) u = BitVec.ofNat 64 words.length :=
    (scanFrame.registers 10#5 (by decide)).trans count
  have bound : words.length < 2^64 := by have := source.2.1; omega
  have finishRead (v : ArmState) (extra : Nat) (prefixRun : run extra u = v)
      (prefixFrame : CapFrame u v) (readPC : read_pc v = base + 2832#64)
      (readPointer : r (.GPR 11#5) v = pointer)
      (readCount : r (.GPR 10#5) v = BitVec.ofNat 64 words.length)
      (nonempty : 0 < words.length) (fits : sigWords words ≤ 2) :
      ∃ total t, run total s = t ∧ CapFrame s t ∧
        read_pc t = (if 2 < sigWords words then base + 3320#64 else base + 3268#64) ∧
        (sigWords words ≤ 2 →
          (r (.GPR 10#5) t).toNat + 2^64 * (r (.GPR 11#5) t).toNat = value words) := by
    have totalFrame := frame.trans prefixFrame
    obtain ⟨readRun, readFrame, finalPC, low, high⟩ := cap_read v base pointer words
      (code.congr totalFrame.program) (totalFrame.error.trans error) readPC readPointer readCount
      (totalFrame.source _ _ source) (totalFrame.words _ _ source stored) nonempty
    let t := capReadResult v words.length
    refine ⟨fuel + extra + (capReadOps words.length).length, t, ?_, totalFrame.trans readFrame,
      ?_, fun _ => ?_⟩
    · rw [run_plus, run_plus, executed, prefixRun, readRun]
    · simpa [show ¬2 < sigWords words by omega] using finalPC
    · rw [low, high]
      exact cap_pair_value words fits
  by_cases zero : sigWords words = 0
  · have zeroPC : read_pc u = base + 2828#64 := by
      simpa only [zero, ↓reduceIte] using nextPC
    have runZero := zero_run u base (code.congr frame.program) (frame.error.trans error) zeroPC
    let v := zeroResult u base
    have vf := zero_frame u base
    by_cases empty : words.length = 0
    · have wordsEmpty : words = [] := List.eq_nil_of_length_eq_zero empty
      refine ⟨fuel + (zeroOps (decide (r (.GPR 10#5) u = 0#64))).length, v,
        ?_, frame.trans vf, ?_, ?_⟩
      · rw [run_plus, executed, runZero]
      · simp [v, zeroResult, state_simp_rules, nextCount, empty, zero]
      · intro fits
        simp [v, zeroResult, state_simp_rules, nextCount, empty, wordsEmpty, value]
    · have nonzero : BitVec.ofNat 64 words.length ≠ 0#64 := by bv_omega
      apply finishRead v _ runZero vf
      · simp [v, zeroResult, state_simp_rules, nextCount, nonzero]
      · simpa [v, zeroResult, state_simp_rules, nextCount, nonzero] using nextPointer
      · simpa [v, zeroResult, state_simp_rules, nextCount, nonzero] using nextCount
      · omega
      · omega
  · have selectedCount := top zero
    have positive : 0 < sigWords words := by omega
    have sigBound : sigWords words < 2^64 := by have := sigWords_le_length words; omega
    have increment : BitVec.ofNat 64 (sigWords words - 1) + 1#64 =
        BitVec.ofNat 64 (sigWords words) := by bv_omega
    have countNat : (r (.GPR 12#5) u + 1#64).toNat = sigWords words := by
      rw [selectedCount, increment]
      exact Nat.mod_eq_of_lt sigBound
    have selectPC : read_pc u = base + 644#64 := by
      simpa only [zero, ↓reduceIte] using nextPC
    have runSelect := select_run u base (code.congr frame.program) (frame.error.trans error) selectPC
    let v := selected u base
    have vf := selected_frame u base
    by_cases wide : 2 < sigWords words
    · refine ⟨fuel + (selectOps (decide (3 ≤ (r (.GPR 12#5) u + 1#64).toNat))).length,
        v, ?_, frame.trans vf, ?_, ?_⟩
      · rw [run_plus, executed, runSelect]
      · simp [v, selected, state_simp_rules, countNat, wide, show 3 ≤ sigWords words by omega]
      · intro fits
        omega
    · apply finishRead v _ runSelect vf
      · simp [v, selected, state_simp_rules, countNat, show ¬3 ≤ sigWords words by omega]
      · exact (selected_register u base 11#5 (by decide)).trans nextPointer
      · exact (selected_register u base 10#5 (by decide)).trans nextCount
      · have := sigWords_le_length words
        omega
      · omega

end SszArm.Measure.BitVector
