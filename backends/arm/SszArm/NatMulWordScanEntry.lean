import SszArm.NatMulWordScanSmall

namespace SszArm.NatMulWord

/-- The original general-factor dispatch chooses by significant count while
retaining the raw operand for every later native indexed read. -/
def GeneralReady (base : BitVec 64) (operand : SszNative.NatOperand) (t : ArmState) : Prop :=
  if operand.wordCount ≤ 1 then
    read_pc t = base + 928#64 ∧ r (.GPR 2#5) t = SszNative.NatMul.lowWord operand
  else
    read_pc t = base + 320#64 ∧ r (.GPR 2#5) t = operand.payload ∧
    r (.GPR 9#5) t = BitVec.ofNat 64 operand.wordCount ∧
    r (.GPR 12#5) t = BitVec.ofNat 64 (operand.wordCount - 1) ∧
    r (.GPR 8#5) t = trimBias operand.words - BitVec.ofNat 64 (8 * (operand.wordCount - 1))

theorem general_ready (s : ArmState) (base factor : BitVec 64)
    (operand : SszNative.NatOperand)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (owned : Owned s operand factor)
    (factorZero : factor ≠ 0#64) (factorOne : factor ≠ 1#64) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ r (.GPR 1#5) t = operand.pointer ∧
      GeneralReady base operand t := by
  cases operand with
  | small word =>
    obtain ⟨fuel, t, ht, htf, htp, ht1, ht2, htk⟩ :=
      general_small_ready s base word factor hc he ha hp owned factorZero factorOne
    have count : (SszNative.NatOperand.small word).wordCount ≤ 1 := by
      have h := SszNative.Limbs.sigWords_le_length [word]
      simpa [SszNative.NatOperand.wordCount, SszNative.NatOperand.words] using h
    refine ⟨fuel, t, ht, htf, ht1, ?_⟩
    simp only [GeneralReady, count, ↓reduceIte]
    exact ⟨htp, by simpa [SszNative.NatMul.lowWord, SszNative.NatAdd.lowWord,
      SszNative.NatOperand.words] using ht2⟩
  | large pointer words =>
    obtain ⟨fuel, t, ht, htf, ht1, ht8, ready⟩ :=
      general_large_ready s base pointer factor words hc he ha hp owned factorZero factorOne
    refine ⟨fuel, t, ht, htf, ht1, ?_⟩
    by_cases small : SszNative.Limbs.sigWords words ≤ 1
    · simp only [small, ↓reduceIte] at ready
      simpa [GeneralReady, SszNative.NatOperand.wordCount, SszNative.NatOperand.words,
        SszNative.NatMul.lowWord, SszNative.NatAdd.lowWord, small] using ready
    · simp only [small, ↓reduceIte] at ready
      simpa [GeneralReady, SszNative.NatOperand.wordCount, SszNative.NatOperand.words,
        SszNative.NatOperand.payload, small] using
        And.intro ready.1 (And.intro ready.2.1 (And.intro ready.2.2.1 (And.intro ready.2.2.2 ht8)))

end SszArm.NatMulWord
