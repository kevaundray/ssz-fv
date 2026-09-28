import SszX86.NatMulWordLoopMath

namespace SszX86.NatMulWord
open SszNative

def firstResult (operand : NatOperand) (factor : BitVec 64) : BitVec 64 × Nat :=
  LimbMul.step factor (SszNative.NatMul.lowWord operand) 0 0

def pairedResult (operand : NatOperand) (factor : BitVec 64) : List (BitVec 64) × Nat :=
  LimbMul.inner (2*(operand.wordCount/2)) factor (operand.words.drop 1) []
    (firstResult operand factor).2

theorem initial_step (factor limb : BitVec 64) :
    factor*limb = (LimbMul.step factor limb 0 0).1 ∧
    productHigh factor limb = BitVec.ofNat 64 (LimbMul.step factor limb 0 0).2 := by
  have arithmetic := word_carry_step factor limb 0 (by decide)
  have noCarry : (Udivti3.addFlags (factor*limb) (BitVec.ofNat 64 0)).cf = false := by
    rw [Udivti3.addFlags_cf]
    simp only [show (BitVec.ofNat 64 0).toNat = 0 by rfl, Nat.add_zero, Udivti3.radix]
    exact decide_eq_false (by have := (factor*limb).isLt; omega)
  rw [noCarry] at arithmetic
  simpa only [Bool.toNat_false, show BitVec.ofNat 64 0 = 0#64 by rfl,
    BitVec.add_zero] using arithmetic

private theorem inner_empty_succ (remaining index : Nat) (factor : BitVec 64)
    (words : List (BitVec 64)) (carry : Nat) :
    LimbMul.inner (remaining+1) factor (words.drop index) [] carry =
      let next := LimbMul.step factor (words[index]?.getD 0) 0 carry
      let rest := LimbMul.inner remaining factor (words.drop (index+1)) [] next.2
      (next.1::rest.1, rest.2) := by
  simpa only [List.drop_nil, List.getElem?_nil, Option.getD_none] using
    LimbMul.inner_indexed_succ remaining index factor words [] carry

theorem inner_split (front rest index : Nat) (factor : BitVec 64)
    (words : List (BitVec 64)) (carry : Nat) :
    LimbMul.inner (front+rest) factor (words.drop index) [] carry =
      let first := LimbMul.inner front factor (words.drop index) [] carry
      let last := LimbMul.inner rest factor (words.drop (index+front)) [] first.2
      (first.1++last.1, last.2) := by
  induction front generalizing index carry with
  | zero => simp only [Nat.zero_add, Nat.add_zero, LimbMul.inner, List.nil_append]
  | succ front ih =>
    rw [show front+1+rest = (front+rest)+1 by omega, inner_empty_succ]
    dsimp only
    rw [ih, inner_empty_succ front index factor words carry]
    dsimp only
    simp only [List.cons_append, Nat.add_assoc, Nat.add_comm 1 front]

theorem word_written_first (operand : NatOperand) (factor : BitVec 64) :
    SszNative.NatMul.wordWritten operand factor = (firstResult operand factor).1 ::
      (LimbMul.inner operand.wordCount factor (operand.words.drop 1) []
        (firstResult operand factor).2).1 := by
  rw [SszNative.NatMul.wordWritten_native_loop]
  have equation := LimbMul.inner_indexed_succ operand.wordCount 0 factor operand.words [] 0
  simpa only [List.drop_zero, List.getElem?_nil, Option.getD_none, List.drop_nil,
    firstResult, SszNative.NatMul.lowWord, SszNative.NatAdd.lowWord] using congrArg Prod.fst equation

theorem paired_carry_bound (operand : NatOperand) (factor : BitVec 64) :
    (pairedResult operand factor).2 < 2^64 :=
  LimbMul.inner_carry_lt _ _ _ _ _ (LimbMul.step_carry_lt _ _ _ _ (by decide))

theorem word_written_pairs (operand : NatOperand) (factor : BitVec 64) :
    SszNative.NatMul.wordWritten operand factor =
      (firstResult operand factor).1 :: ((pairedResult operand factor).1 ++
        if operand.wordCount%2 = 0 then [] else [BitVec.ofNat 64 (pairedResult operand factor).2]) := by
  rw [word_written_first]
  have countDecomposition : 2*(operand.wordCount/2)+operand.wordCount%2 = operand.wordCount := by omega
  have split := inner_split (2*(operand.wordCount/2)) (operand.wordCount%2) 1 factor
    operand.words (firstResult operand factor).2
  rw [countDecomposition] at split
  rw [split]
  change (firstResult operand factor).1 :: ((pairedResult operand factor).1 ++ _) = _
  by_cases even : operand.wordCount%2 = 0
  · simp only [even, LimbMul.inner, ↓reduceIte]
  · have odd : operand.wordCount%2 = 1 := by omega
    have index : 1+2*(operand.wordCount/2) = operand.wordCount := by omega
    have tail := inner_empty_succ 0 operand.wordCount factor operand.words
      (pairedResult operand factor).2
    rw [final_input_zero, final_step _ _ (paired_carry_bound operand factor)] at tail
    change LimbMul.inner 1 factor (operand.words.drop operand.wordCount) []
      (pairedResult operand factor).2 = ([BitVec.ofNat 64 (pairedResult operand factor).2], 0) at tail
    simp only [odd, index, show ¬ (1 : Nat) = 0 by decide, ite_false]
    change (firstResult operand factor).1 :: ((pairedResult operand factor).1 ++
      (LimbMul.inner 1 factor (operand.words.drop operand.wordCount) [] (pairedResult operand factor).2).1) = _
    rw [tail]

end SszX86.NatMulWord
