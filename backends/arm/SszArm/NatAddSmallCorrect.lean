import SszArm.NatAddSmallCorrectLoad

namespace SszArm.NatAdd

open UintCodec SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Complete nonzero one-word phase from +384 through the actual RET. Physical
Large inputs may retain arbitrary redundant high zero limbs. Low-word loads,
all reservation checks, cursor/payload writes and the complete return image are
composed without replacing any architectural instruction by a native operation. -/
theorem one_word_correct (s : ArmState) (base : BitVec 64) (left right : NatOperand)
    (owned : Owned s left right) (hc : CodeAt s base)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 384#64)
    (hleftNonzero : left.wordCount ≠ 0) (hrightNonzero : right.wordCount ≠ 0)
    (hsmall : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1)
    (htag : r (.GPR 9#5) s = if right.pointer = 0#64 then 0#64 else 1#64) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  have hl : left.wordCount = 1 := by omega
  have hr : right.wordCount = 1 := by omega
  let a := SszNative.NatAdd.lowWord left
  let b := SszNative.NatAdd.lowWord right
  let u := oneWordLoadResult s base a b
  have observations := SmallCorrect.load_observations s left right owned hleftNonzero hrightNonzero
  have runLoad : run (oneWordLoadOps (r (.GPR 1#5) s) (r (.GPR 3#5) s)).length s = u :=
    one_word_load s base a b hc he ha hp owned.stackBound
      (by simpa only [owned.rightPointer] using htag) observations.1 observations.2
  have loadFrame : ZeroFrame s u := SmallCorrect.load_prefix s base a b owned.stackBound
  have up : read_pc u = base + 980#64 := by
    simp [u, oneWordLoadResult, state_simp_rules]
  have u2 : r (.GPR 2#5) u = a := by simp [u, oneWordLoadResult, state_simp_rules]
  have u4 : r (.GPR 4#5) u = b := by simp [u, oneWordLoadResult, state_simp_rules]
  have u8 : r (.GPR 8#5) u = 0#64 := by simp [u, oneWordLoadResult, state_simp_rules]
  obtain ⟨runSum, sumFrame, sumOut, sum9, sum8, sumPC⟩ :=
    one_word_sum u base .normalized a b (loadFrame.code hc) (loadFrame.error.trans he)
      (loadFrame.aligned ha) up u2 u4 (fun _ => u8)
  let v := block base (SumPath.normalized.ops (sumOverflow a b)) u
  have sumPrefix : ZeroFrame u v := ZeroFrame.of_scan sumFrame sumOut
    (by rw [loadFrame.sp]; exact owned.stackBound)
  have prefix := SmallCorrect.prefix_trans loadFrame sumPrefix
  apply SmallCorrect.finish_sum s v base left right owned hc he ha hl hr
    ((oneWordLoadOps (r (.GPR 1#5) s) (r (.GPR 3#5) s)).length +
      (SumPath.normalized.ops (sumOverflow a b)).length)
  · rw [run_plus, runLoad, runSum]
  · exact prefix
  · exact (sumFrame.registers 5#5 (by decide)).trans
      (SmallCorrect.load_arena_register s base a b)
  · exact sum9
  · exact sumPC

/-- Complete immediate/immediate phase from +544 through RET. Pointer zero is
interpreted using the original physical operand representation, not an added
word-count register premise. Both carry outcomes use the same exact Post. -/
theorem immediate_correct (s : ArmState) (base : BitVec 64) (left right : NatOperand)
    (owned : Owned s left right) (hc : CodeAt s base)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 544#64)
    (hleftNonzero : left.wordCount ≠ 0) (hrightNonzero : right.wordCount ≠ 0)
    (hleftPtr : left.pointer = 0#64) (hrightPtr : right.pointer = 0#64) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  obtain ⟨a, leftSmall⟩ := SmallCorrect.small_of_pointer_zero s left owned.leftAt hleftPtr
  obtain ⟨b, rightSmall⟩ := SmallCorrect.small_of_pointer_zero s right owned.rightAt hrightPtr
  subst left
  subst right
  have hl : (NatOperand.small a).wordCount = 1 := by
    have bound := Limbs.sigWords_le_length [a]
    change Limbs.sigWords [a] ≠ 0 at hleftNonzero
    change Limbs.sigWords [a] = 1
    simp only [List.length_cons, List.length_nil] at bound
    omega
  have hr : (NatOperand.small b).wordCount = 1 := by
    have bound := Limbs.sigWords_le_length [b]
    change Limbs.sigWords [b] ≠ 0 at hrightNonzero
    change Limbs.sigWords [b] = 1
    simp only [List.length_cons, List.length_nil] at bound
    omega
  obtain ⟨runSum, sumFrame, sumOut, sum9, sum8, sumPC⟩ :=
    one_word_sum s base .immediate a b hc he ha hp owned.leftPayload owned.rightPayload
      (by intro impossible; cases impossible)
  let t := block base (SumPath.immediate.ops (sumOverflow a b)) s
  have prefix : ZeroFrame s t := ZeroFrame.of_scan sumFrame sumOut owned.stackBound
  apply SmallCorrect.finish_sum s t base (.small a) (.small b) owned hc he ha hl hr
    (SumPath.immediate.ops (sumOverflow a b)).length runSum prefix
    (sumFrame.registers 5#5 (by decide))
  · simpa [SmallCorrect.low, SszNative.NatAdd.lowWord, NatOperand.words] using sum9
  · simpa [SszNative.NatAdd.lowWord, NatOperand.words] using sumPC

end SszArm.NatAdd
