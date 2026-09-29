import SszNatMul
import SszNatDivision

set_option autoImplicit false

namespace SszNative.Indices

/-- A physical limb slice bound, not a bound on the represented natural. -/
def Physical (operand : NatOperand) : Prop := operand.words.length < 2^64

theorem small_physical (word : BitVec 64) : Physical (.small word) := by
  simp [Physical, NatOperand.words]

theorem fromWords_physical (pointer : BitVec 64) (words : List (BitVec 64))
    (physical : words.length < 2^64) : Physical (NatOperand.fromWords pointer words) := by
  have bound := Limbs.sigWords_le_length words
  rw [← Limbs.trim_length] at bound
  unfold NatOperand.fromWords
  cases trimmed : Limbs.trim words with
  | nil => exact small_physical _
  | cons first rest =>
      cases rest with
      | nil => exact small_physical _
      | cons second rest =>
          simp only [Physical, NatOperand.words]
          rw [trimmed] at bound
          simpa only [List.length_cons] using Nat.lt_of_le_of_lt bound physical

theorem normalized_physical (operand : NatOperand) (physical : Physical operand) :
    Physical operand.normalized :=
  fromWords_physical operand.pointer operand.words physical

theorem fromWide_physical (base capacity used : Nat) (wide : BitVec 128)
    (result : NatOperand)
    (success : (NatArithmetic.fromWide base capacity used wide).result = .ok result) :
    Physical result := by
  unfold NatArithmetic.fromWide at success
  split at success
  · cases success
    exact small_physical _
  · split at success
    · cases success
    · cases success
      apply fromWords_physical
      simp

theorem add_physical (left right : NatOperand) (base capacity used : Nat)
    (leftPhysical : Physical left) (rightPhysical : Physical right) (result : NatOperand)
    (success : (NatAdd.run left right base capacity used).result = .ok result) :
    Physical result := by
  unfold NatAdd.run at success
  dsimp only at success
  split at success
  · cases success
    exact normalized_physical right rightPhysical
  · split at success
    · cases success
      exact normalized_physical left leftPhysical
    · split at success
      · exact fromWide_physical _ _ _ _ result success
      · split at success
        · rename_i countBound
          split at success
          · cases success
          · cases success
            apply fromWords_physical
            rw [NatAdd.writtenWords_length]
            exact countBound
        · cases success

theorem mulWord_physical (operand : NatOperand) (factor : BitVec 64)
    (base capacity used : Nat) (physical : Physical operand) (result : NatOperand)
    (success : (NatMul.runWord operand factor base capacity used).result = .ok result) :
    Physical result := by
  by_cases zero : factor = 0
  · subst factor
    rw [NatMul.runWord_zero] at success
    cases success
    exact small_physical _
  by_cases one : factor = 1
  · subst factor
    rw [NatMul.runWord_one] at success
    cases success
    exact normalized_physical operand physical
  by_cases small : operand.wordCount ≤ 1
  · rw [NatMul.runWord_small operand factor base capacity used zero one small] at success
    exact fromWide_physical _ _ _ _ result success
  · rw [NatMul.runWord_large operand factor base capacity used zero one (by omega)] at success
    split at success
    · rename_i countBound
      split at success
      · cases success
      · cases success
        apply fromWords_physical
        rw [NatMul.wordWritten_length]
        exact countBound
    · cases success

theorem mul_physical (left right : NatOperand) (base capacity used : Nat)
    (leftPhysical : Physical left) (rightPhysical : Physical right) (result : NatOperand)
    (success : (NatMul.run left right base capacity used).result = .ok result) :
    Physical result := by
  by_cases zero : left.wordCount = 0 ∨ right.wordCount = 0
  · rw [NatMul.run_zero left right base capacity used zero] at success
    cases success
    exact small_physical _
  have leftNonzero : left.wordCount ≠ 0 := by omega
  have rightNonzero : right.wordCount ≠ 0 := by omega
  by_cases rightOne : right.wordCount = 1
  · rw [NatMul.run_right_one left right base capacity used leftNonzero rightOne] at success
    exact mulWord_physical _ _ _ _ _ leftPhysical result success
  by_cases leftOne : left.wordCount = 1
  · rw [NatMul.run_left_one left right base capacity used leftOne rightNonzero rightOne] at success
    exact mulWord_physical _ _ _ _ _ rightPhysical result success
  rw [NatMul.run_large left right base capacity used (by omega) (by omega)] at success
  split at success
  · rename_i countBound
    split at success
    · cases success
    · cases success
      apply fromWords_physical
      rw [NatMul.writtenWords_length]
      exact countBound
  · cases success

theorem divide_physical (operand : NatOperand) (divisor : BitVec 64)
    (base capacity used : Nat) (physical : Physical operand) (result : NatOperand × BitVec 64)
    (success : (NatDivision.run operand divisor base capacity used).result = .ok result) :
    Physical result.1 := by
  unfold NatDivision.run at success
  split at success
  · cases success
  · split at success
    · cases success
      exact normalized_physical operand physical
    · split at success
      · cases wide : (NatArithmetic.fromWide base capacity used
          (NatDivision.wideQuotient operand divisor)).result with
        | error reason => simp only [wide, Except.map] at success; cases success
        | ok quotient =>
            simp only [wide, Except.map, Except.ok.injEq] at success
            subst result
            exact fromWide_physical _ _ _ _ quotient wide
      · split at success
        · cases success
        · cases success
          apply fromWords_physical
          rw [LimbDivision.divideWords_length, Limbs.trim_length]
          exact Nat.lt_of_le_of_lt (Limbs.sigWords_le_length operand.words) physical

end SszNative.Indices
