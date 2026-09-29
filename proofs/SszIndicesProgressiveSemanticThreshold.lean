import SszIndicesProgressiveSemanticAlgebra
import SszIndicesProgressive
import SszIndicesArithmeticSemanticWords
import SszLimbOrder

set_option autoImplicit false

namespace SszNative.Indices.ProgressiveSemantic

theorem alternatingWord_bit (bit : Nat) (inside : bit < 64) :
    alternatingWord.getLsbD bit = decide (bit % 2 = 0) := by
  have finite : ∀ i : Fin 64,
      alternatingWord.getLsbD i.val = decide (i.val % 2 = 0) := by decide
  exact finite ⟨bit, inside⟩

theorem thresholdWord_bit (bits position bit : Nat) (inside : bit < 64) :
    (thresholdWord bits position).getLsbD bit =
      decide (64 * position + bit < bits ∧ (64 * position + bit) % 2 = 0) := by
  rw [thresholdWord, BitVec.getLsbD_and, alternatingWord_bit bit inside,
    rangeWord_bit position 0 bits bit inside]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem thresholdWord_digit (bits position : Nat) :
    (thresholdWord bits position).toNat =
      (offset ((bits + 1) / 2) / 2 ^ (64 * position)) % 2 ^ 64 := by
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases inside : bit < 64
  · rw [BitVec.testBit_toNat, thresholdWord_bit bits position bit inside, offset_testBit]
    simp only [inside, decide_true, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (thresholdWord bits position).isLt
      (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp [inside]

theorem thresholdWord_even (level position : Nat) :
    (thresholdWord (2 * level) position).toNat =
      (offset level / 2 ^ (64 * position)) % 2 ^ 64 := by
  simpa only [show (2 * level + 1) / 2 = level by omega] using
    thresholdWord_digit (2 * level) position

/-- Taking raw input limbs has the expected truncation value, even for a padded
or empty Large input. This is an observation, not an operational allocation. -/
theorem prefix_value (words : List (BitVec 64)) (count : Nat) :
    Limbs.value (words.take count) = Limbs.value words % 2 ^ (64 * count) := by
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [NatShift.limbs_testBit, Nat.testBit_mod_two_pow, NatShift.limbs_testBit,
    List.getElem?_take]
  by_cases inside : bit / 64 < count
  · simp [inside, show bit < 64 * count by omega]
  · simp [inside, show ¬bit < 64 * count by omega]

theorem thresholdWords_value (bits count : Nat) (enough : bits ≤ 64 * count) :
    Limbs.value (List.ofFn (fun i : Fin count => thresholdWord bits i.val)) =
      offset ((bits + 1) / 2) := by
  apply NatShift.generated_value
  · intro position bit inside
    rw [thresholdWord_bit bits position bit inside, offset_testBit]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  · intro bit beyond
    rw [offset_testBit]
    simp only [decide_eq_false_iff_not]
    omega

theorem thresholdCompareWords_scan (chunk : NatOperand) (bits count : Nat) :
    thresholdCompareWords chunk bits count =
      Limbs.scanDesc chunk.words (List.ofFn (fun i : Fin count => thresholdWord bits i.val)) count := by
  have scan : ∀ remaining, remaining ≤ count → thresholdCompareWords chunk bits remaining =
      Limbs.scanDesc chunk.words (List.ofFn (fun i : Fin count => thresholdWord bits i.val)) remaining := by
    intro remaining
    induction remaining with
    | zero => intro _; rfl
    | succ remaining ih =>
        intro bound
        simp only [thresholdCompareWords, Limbs.scanDesc, word_eq,
          List.getElem?_ofFn, show remaining < count by omega, ↓reduceDIte, Option.getD_some]
        cases order : compare (chunk.words[remaining]?.getD 0).toNat
            (thresholdWord bits remaining).toNat with
        | eq => exact ih (by omega)
        | lt => rfl
        | gt => rfl
  exact scan count (Nat.le_refl _)

theorem thresholdCompareWords_value (chunk : NatOperand) (bits count : Nat)
    (enough : bits ≤ 64 * count) (width : bitLength chunk ≤ 64 * count) :
    thresholdCompareWords chunk bits count = compare chunk.value (offset ((bits + 1) / 2)) := by
  rw [thresholdCompareWords_scan, Limbs.scanDesc_value, prefix_value,
    List.take_of_length_le (by simp), thresholdWords_value bits count enough]
  have bound : chunk.value < 2 ^ (64 * count) := by
    rw [bitLength_value] at width
    unfold Serialize.bitLength at width
    split at width
    · rename_i zero
      simpa [zero] using Nat.two_pow_pos (64 * count)
    · exact Nat.lt_of_lt_of_le Nat.lt_log2_self
        (Nat.pow_le_pow_right (by decide) (by omega))
  rw [show Limbs.value chunk.words = chunk.value from rfl, Nat.mod_eq_of_lt bound]

theorem offset_bitLength (level : Nat) :
    Serialize.bitLength (offset (level + 1)) = 2 * level + 1 := by
  have capacity := offset_capacity level
  have power := Nat.two_pow_pos (2 * level)
  have lower : 2 ^ (2 * level) ≤ offset (level + 1) := by
    rw [offset_succ, ← width_eq]
    omega
  have upper : offset (level + 1) < 2 ^ (2 * level + 1) := by
    rw [offset_succ, Nat.pow_succ, ← width_eq]
    omega
  have nonzero : offset (level + 1) ≠ 0 := by omega
  have logarithm := (Nat.log2_eq_iff nonzero).mpr ⟨lower, upper⟩
  simp [Serialize.bitLength, nonzero, logarithm]

theorem bitLength_compare (left right : Nat)
    (different : Serialize.bitLength left ≠ Serialize.bitLength right) :
    compare (Serialize.bitLength left) (Serialize.bitLength right) = compare left right := by
  have mono : ∀ a b, Serialize.bitLength a < Serialize.bitLength b → a < b := by
    intro a b ordered
    by_cases result : a < b
    · exact result
    · have le : b ≤ a := by omega
      by_cases az : a = 0
      · subst a
        have bz : b = 0 := by omega
        simp [bz] at ordered
      · by_cases bz : b = 0
        · simp [bz, Serialize.bitLength] at ordered
        · have logs := (Nat.le_log2 az).mpr (Nat.le_trans (Nat.log2_self_le bz) le)
          simp only [Serialize.bitLength, az, bz, ↓reduceIte] at ordered
          omega
  cases order : compare (Serialize.bitLength left) (Serialize.bitLength right) with
  | eq => exact False.elim (different (Nat.compare_eq_eq.mp order))
  | lt => exact (Nat.compare_eq_lt.mpr (mono left right (Nat.compare_eq_lt.mp order))).symm
  | gt => exact (Nat.compare_eq_gt.mpr (mono right left (Nat.compare_eq_gt.mp order))).symm

theorem thresholdCompare_value (chunk : NatOperand) (level count : Nat)
    (enough : 2 * level + 1 ≤ 64 * count) :
    thresholdCompare chunk (2 * level + 1) count = compare chunk.value (offset (level + 1)) := by
  unfold thresholdCompare
  cases order : compare (bitLength chunk) (2 * level + 1) with
  | eq =>
      have same := Nat.compare_eq_eq.mp order
      simpa only [show (2 * level + 1 + 1) / 2 = level + 1 by omega] using
        thresholdCompareWords_value chunk (2 * level + 1) count enough (by omega)
  | lt =>
      have different : Serialize.bitLength chunk.value ≠ Serialize.bitLength (offset (level + 1)) := by
        rw [← bitLength_value, offset_bitLength]
        exact Nat.ne_of_lt (Nat.compare_eq_lt.mp order)
      simpa only [← bitLength_value, offset_bitLength, order] using
        bitLength_compare chunk.value (offset (level + 1)) different
  | gt =>
      have different : Serialize.bitLength chunk.value ≠ Serialize.bitLength (offset (level + 1)) := by
        rw [← bitLength_value, offset_bitLength]
        exact Nat.ne_of_gt (Nat.compare_eq_gt.mp order)
      simpa only [← bitLength_value, offset_bitLength, order] using
        bitLength_compare chunk.value (offset (level + 1)) different

theorem progressiveDepth_interval (chunk : NatOperand) (count : Nat)
    (enough : depth chunk / 2 * 2 + 1 ≤ 64 * count) :
    let level := progressiveDepth chunk count / 2
    progressiveDepth chunk count = 2 * level ∧
      offset level ≤ chunk.value ∧ chunk.value < offset (level + 1) := by
  have compareValue := thresholdCompare_value chunk (chunk.value.log2 / 2) count
    (by simpa only [depth_value, Nat.mul_comm] using enough)
  let selected := if chunk.value < offset (chunk.value.log2 / 2 + 1)
    then chunk.value.log2 / 2 else chunk.value.log2 / 2 + 1
  have depthEq : progressiveDepth chunk count = 2 * selected := by
    dsimp only [selected]
    simp only [progressiveDepth, depth_value, Nat.mul_comm (chunk.value.log2 / 2) 2,
      compareValue, Nat.compare_eq_lt]
    split <;> omega
  have half : progressiveDepth chunk count / 2 = selected := by
    rw [depthEq]
    omega
  have bounds : offset selected ≤ chunk.value ∧ chunk.value < offset (selected + 1) :=
    selected_interval chunk.value
  dsimp only
  simp only [half]
  exact ⟨depthEq, bounds⟩

end SszNative.Indices.ProgressiveSemantic
