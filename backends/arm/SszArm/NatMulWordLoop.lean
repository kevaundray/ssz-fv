import SszArm.NatMulWordLoopRound
import SszNatMul

namespace SszArm.NatMulWord

open Delimited (Protected MemoryFrame)
open NatCompare (Words)

private theorem inner_index_step (remaining index : Nat) (factor : BitVec 64)
    (words : List (BitVec 64)) (carry : Nat) :
    SszNative.LimbMul.inner (remaining + 1) factor (words.drop index) [] carry =
      let next := SszNative.LimbMul.step factor (words[index]?.getD 0#64) 0#64 carry
      let rest := SszNative.LimbMul.inner remaining factor (words.drop (index + 1)) [] next.2
      (next.1 :: rest.1, rest.2) := by
  have step := SszNative.LimbMul.inner_indexed_succ remaining index factor words [] carry
  simp only [List.drop_nil, List.getElem?_nil, Option.getD_none] at step
  arm_word_nf at step ⊢
  exact step

/-- Induction counts all remaining stores, including the last zero-extended
input word. No logical bound is used: representable counters follow from the
current physical output span. The only stop is the real compare at804/808. -/
theorem loop_runs_remaining (remaining : Nat) (s : ArmState)
    (base raw pointer factor : BitVec 64) (words doneWords : List (BitVec 64))
    (count index : Nat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (head : LoopHeadAt s base raw pointer factor words count index)
    (positive : 0 < index) (amount : count = index + remaining)
    (prefixLength : doneWords.length = index)
    (space : NatMul.LoopSpace (r (.GPR 31#5) s) pointer (count + 1))
    (physical : raw.toNat + 8 * words.length ≤ 2^64)
    (separate : Protected (NatMul.loopWrites (r (.GPR 31#5) s) pointer (count + 1))
      raw.toNat (8 * words.length))
    (input : Words s raw words) (written : Words s pointer doneWords) :
    ∃ fuel t, run fuel s = t ∧ LoopStable s t ∧ read_pc t = base + 1464#64 ∧
      Words t pointer (doneWords ++ (SszNative.LimbMul.inner (remaining + 1) factor
        (words.drop index) [] (r (.GPR 14#5) s).toNat).1) ∧
      MemoryFrame (NatMul.loopWrites (r (.GPR 31#5) s) pointer (count + 1)) s t := by
  induction remaining generalizing s index doneWords with
  | zero =>
    obtain ⟨fuel, t, runEq, stable, pc, indexEq, carryEq, current, frame⟩ :=
      loop_round_runs s base raw pointer factor words doneWords count index code error aligned head
        positive (by omega) prefixLength space physical separate input written
    refine ⟨fuel, t, runEq, stable, ?_, ?_, frame⟩
    · simpa only [if_pos (show index = count by omega)] using pc
    · rw [inner_index_step 0 index factor words (r (.GPR 14#5) s).toNat]
      simpa only [SszNative.LimbMul.inner] using current
  | succ remaining ih =>
    let next := SszNative.LimbMul.step factor (words[index]?.getD 0#64) 0#64
      (r (.GPR 14#5) s).toNat
    obtain ⟨fuel, u, runEq, stable, pc, indexEq, carryEq, current, frame⟩ :=
      loop_round_runs s base raw pointer factor words doneWords count index code error aligned head
        positive (by omega) prefixLength space physical separate input written
    have nextHead : LoopHeadAt u base raw pointer factor words count (index + 1) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [if_neg (by omega : index ≠ count)] using pc
      · exact (stable.registers 1#5 (by decide)).trans head.rawPointer
      · exact (stable.registers 2#5 (by decide)).trans head.rawLength
      · exact (stable.registers 3#5 (by decide)).trans head.factorReg
      · exact (stable.registers 9#5 (by decide)).trans head.countReg
      · simpa only [Nat.add_sub_cancel] using indexEq
      · exact (stable.registers 15#5 (by decide)).trans head.outputNext
    have nextSpace : NatMul.LoopSpace (r (.GPR 31#5) u) pointer (count + 1) := by
      simpa only [stable.sp] using space
    have nextSeparate : Protected (NatMul.loopWrites (r (.GPR 31#5) u) pointer (count + 1))
        raw.toNat (8 * words.length) := by simpa only [stable.sp] using separate
    have nextInput := NatMul.words_preserve frame physical separate input
    obtain ⟨restFuel, t, restRun, restStable, restPC, restWords, restFrame⟩ :=
      ih (s := u) (index := index + 1) (doneWords := doneWords ++ [next.1])
        (stable.code code) (stable.error.trans error) (stable.aligned aligned) nextHead
        (by omega) (by omega) (by simp only [List.length_append, List.length_singleton, prefixLength])
        nextSpace nextSeparate nextInput current
    refine ⟨fuel + restFuel, t, by rw [run_plus, runEq, restRun],
      stable.trans restStable, restPC, ?_, ?_⟩
    · rw [inner_index_step]
      rw [carryEq] at restWords
      simpa only [next, List.append_assoc, List.singleton_append] using restWords
    · exact frame.trans (by simpa only [stable.sp] using restFrame)

/-- Public current-state loop contract, beginning at the original812 head. -/
theorem loop_runs (s : ArmState) (base raw pointer factor : BitVec 64)
    (words doneWords : List (BitVec 64)) (count index : Nat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (head : LoopHeadAt s base raw pointer factor words count index)
    (positive : 0 < index) (within : index ≤ count) (prefixLength : doneWords.length = index)
    (space : NatMul.LoopSpace (r (.GPR 31#5) s) pointer (count + 1))
    (physical : raw.toNat + 8 * words.length ≤ 2^64)
    (separate : Protected (NatMul.loopWrites (r (.GPR 31#5) s) pointer (count + 1))
      raw.toNat (8 * words.length))
    (input : Words s raw words) (written : Words s pointer doneWords) :
    ∃ fuel t, run fuel s = t ∧ LoopStable s t ∧ read_pc t = base + 1464#64 ∧
      Words t pointer (doneWords ++ (SszNative.LimbMul.inner (count + 1 - index) factor
        (words.drop index) [] (r (.GPR 14#5) s).toNat).1) ∧
      MemoryFrame (NatMul.loopWrites (r (.GPR 31#5) s) pointer (count + 1)) s t := by
  simpa only [show count - index + 1 = count + 1 - index by omega] using
    loop_runs_remaining (count - index) s base raw pointer factor words doneWords count index
      code error aligned head positive (by omega) prefixLength space physical separate input written

theorem word_written_first (operand : SszNative.NatOperand) (factor : BitVec 64) :
    SszNative.NatMul.wordWritten operand factor =
      [operand.words[0]?.getD 0#64 * factor] ++
        (SszNative.LimbMul.inner operand.wordCount factor (operand.words.drop 1) []
          (NatMulProduct.high (operand.words[0]?.getD 0#64) factor).toNat).1 := by
  rw [SszNative.NatMul.wordWritten_native_loop]
  have decomposition := congrArg Prod.fst
    (inner_index_step operand.wordCount 0 factor operand.words 0)
  simpa only [List.drop_zero, Nat.zero_add, NatMulProduct.step_zero, BitVec.mul_comm,
    product_high_comm, List.singleton_append] using decomposition

/-- Complete c+1-limb image from the actual first stored limb and incoming
high half. The original raw list, including redundant zeros, remains the source. -/
theorem word_loop_runs (s : ArmState) (base pointer factor : BitVec 64)
    (operand : SszNative.NatOperand)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (head : LoopHeadAt s base operand.pointer pointer factor operand.words operand.wordCount 1)
    (large : 1 < operand.wordCount)
    (space : NatMul.LoopSpace (r (.GPR 31#5) s) pointer (operand.wordCount + 1))
    (physical : operand.pointer.toNat + 8 * operand.words.length ≤ 2^64)
    (separate : Protected (NatMul.loopWrites (r (.GPR 31#5) s) pointer (operand.wordCount + 1))
      operand.pointer.toNat (8 * operand.words.length))
    (input : Words s operand.pointer operand.words)
    (written : Words s pointer [operand.words[0]?.getD 0#64 * factor])
    (carry : r (.GPR 14#5) s = NatMulProduct.high (operand.words[0]?.getD 0#64) factor) :
    ∃ fuel t, run fuel s = t ∧ LoopStable s t ∧ read_pc t = base + 1464#64 ∧
      Words t pointer (SszNative.NatMul.wordWritten operand factor) ∧
      MemoryFrame (NatMul.loopWrites (r (.GPR 31#5) s) pointer (operand.wordCount + 1)) s t := by
  obtain ⟨fuel, t, runEq, stable, pc, current, frame⟩ := loop_runs s base operand.pointer pointer factor
    operand.words [operand.words[0]?.getD 0#64 * factor] operand.wordCount 1 code error aligned head
      (by decide) (by omega) rfl space physical separate input written
  refine ⟨fuel, t, runEq, stable, pc, ?_, frame⟩
  rw [word_written_first]
  simpa only [Nat.add_sub_cancel, carry] using current

end SszArm.NatMulWord
