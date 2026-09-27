import SszArm.NatAddLargeLoop

namespace SszArm.NatAdd.LargeLoop

open SszNative

/-- The initial physical store followed by the proved PC1692 suffix is exactly
the frozen shared native write list. Neither original operand is trimmed here. -/
theorem native_words (left right : NatOperand) :
    let first := LimbAdd.step (left.words[0]?.getD 0) (right.words[0]?.getD 0) 0
    first.1 :: (LimbAdd.loop (SszNative.NatAdd.count left right)
      (left.words.drop 1) (right.words.drop 1) first.2).1 =
      SszNative.NatAdd.writtenWords left right := by
  rw [SszNative.NatAdd.writtenWords_native_loop]
  have equation := LimbAdd.loop_indexed_succ
    (SszNative.NatAdd.count left right) 0 left.words right.words 0
  simpa only [List.drop_zero, Nat.zero_add] using (congrArg Prod.fst equation).symm

/-- At actual PC1692, a correctly stored low word and the initial carry give
all exact native writes, zero final carry, and the precise physical suffix
frame needed by the final normalization and ABI return proof. -/
theorem native_entry_run (s : ArmState) (base stack output : BitVec 64)
    (left right : NatOperand)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1692#64)
    (inv : Invariant s stack output left.words right.words 1
      (SszNative.NatAdd.count left right)
      (LimbAdd.step (left.words[0]?.getD 0) (right.words[0]?.getD 0) 0).2)
    (low : read_mem_bytes 8 output s =
      (LimbAdd.step (left.words[0]?.getD 0) (right.words[0]?.getD 0) 0).1) :
    ∃ fuel t, run fuel s = t ∧
      LoopFrame (suffixWrites stack output 1 (SszNative.NatAdd.count left right)) s t ∧
      read_pc t = base + 2044#64 ∧
      r (.GPR 12#5) t = 0#64 ∧ r (.GPR 14#5) t = 0#64 ∧
      r (.GPR 15#5) t = BitVec.ofNat 64 (SszNative.NatAdd.count left right + 1) ∧
      r (.GPR 13#5) t = r (.GPR 13#5) s ∧
      NatCompare.Words t output (SszNative.NatAdd.writtenWords left right) := by
  have hl : (Limbs.trim left.words).length ≤ SszNative.NatAdd.count left right := by
    simp only [SszNative.NatAdd.count, ← NatOperand.wordCount_eq_trim_length]
    exact Nat.le_max_left _ _
  have hr : (Limbs.trim right.words).length ≤ SszNative.NatAdd.count left right := by
    simp only [SszNative.NatAdd.count, ← NatOperand.wordCount_eq_trim_length]
    exact Nat.le_max_right _ _
  obtain ⟨fuel, t, runEq, frame, pc, carry, remaining, index, small, words⟩ :=
    entry_run s base stack output _ left.words right.words
      (SszNative.NatAdd.count left right) _ hc he ha hp inv hl hr low
  refine ⟨fuel, t, runEq, frame, pc, carry, remaining, index, small, ?_⟩
  simpa only [native_words left right] using words

end SszArm.NatAdd.LargeLoop
