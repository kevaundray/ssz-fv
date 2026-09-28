import SszArm.NatMulLoopRow

namespace SszArm.NatMul

open SszNative (LimbMul)
open NatCompare (Words)
open Delimited (Protected MemoryFrame)

theorem loop_operand_preserve {s t : ArmState} {writes : List Delimited.Span}
    {pointer payload : BitVec 64} {words : List (BitVec 64)}
    (memory : MemoryFrame writes s t) (stack : r (.GPR 31#5) t = r (.GPR 31#5) s)
    (owned : pointer ≠ 0#64 → Protected writes pointer.toNat (8 * words.length))
    (operand : NatCompare.Operand s pointer payload words) :
    NatCompare.Operand t pointer payload words := by
  rcases operand with small | ⟨nonnull, length, source, observed⟩
  · exact Or.inl small
  · refine Or.inr ⟨nonnull, length, ?_, words_preserve memory source.2.1 (owned nonnull) observed⟩
    simpa only [NatCompare.Source, ByteView.Source, stack] using source

private theorem loop_head_tail (words : List (BitVec 64)) (positive : 0 < words.length) :
    words.head?.getD 0#64 :: words.tail = words := by
  cases words with
  | nil => simp at positive
  | cons word words => rfl

/-- Full outer induction. `factors` identifies the remaining original indexed
left observations; the memory invariant retains the entire physical buffer.
There is no assumed future trace, output, or successful round in the interface. -/
theorem loop_rows_runs (base sp leftPointer leftPayload source dst : BitVec 64)
    (left : Nat) (leftRaw right : List (BitVec 64))
    (space : LoopSpace sp dst (left + right.length)) (rightPositive : 0 < right.length)
    (sourcePhysical : source.toNat + 8 * right.length ≤ 2^64)
    (sourceOwned : Protected (loopWrites sp dst (left + right.length)) source.toNat (8 * right.length))
    (leftOwned : leftPointer ≠ 0#64 → Protected (loopWrites sp dst (left + right.length))
      leftPointer.toNat (8 * leftRaw.length)) :
    ∀ factors : List (BitVec 64), 0 < factors.length →
    ∀ row doneWords buffer (s : ArmState), row + factors.length = left →
    (∀ k (hk : k < factors.length), factors[k] = leftRaw[row + k]?.getD 0#64) →
    doneWords.length = row → row + buffer.length = left + right.length →
    CodeAt s base → read_err s = .None → CheckSPAlignment s → read_pc s = base + 600#64 →
    r (.GPR 31#5) s = sp → r (.GPR 8#5) s = source →
    r (.GPR 9#5) s = leftPointer → r (.GPR 10#5) s = leftPayload →
    r (.GPR 11#5) s = dst + BitVec.ofNat 64 (8 * row) →
    r (.GPR 12#5) s = BitVec.ofNat 64 row →
    r (.GPR 19#5) s = BitVec.ofNat 64 (left + right.length) →
    r (.GPR 20#5) s = dst → r (.GPR 21#5) s = BitVec.ofNat 64 left →
    r (.GPR 22#5) s = BitVec.ofNat 64 right.length →
    r (.GPR 25#5) s = BitVec.ofNat 64 right.length →
    NatCompare.Operand s leftPointer leftPayload leftRaw →
    Words s source right → Words s dst (currentWords doneWords buffer) →
    ∃ fuel t, run fuel s = t ∧ LoopStable loopOuterChanged s t ∧
      MemoryFrame (loopWrites sp dst (left + right.length)) s t ∧
      read_pc t = base + 1012#64 ∧ r (.GPR 12#5) t = BitVec.ofNat 64 left ∧
      r (.GPR 11#5) t = dst + BitVec.ofNat 64 (8 * left) ∧
      Words t dst (doneWords ++ LimbMul.nativeRows factors right buffer) := by
  intro factors
  induction factors with
  | nil => intro positive; simp at positive
  | cons factor factors ih =>
    intro positive row doneWords buffer s rows indexed prefixLength bufferLength code error aligned pc
      spAt sourceAt leftPointerAt leftPayloadAt rowPointer rowAt countAt dstAt leftAt rightAt widthAt
      leftOperand rightWords bufferWords
    have rowBound : row < left := by simp only [List.length_cons] at rows; omega
    have factorEq : leftRaw[row]?.getD 0#64 = factor := by
      simpa using (indexed 0 (by simp)).symm
    obtain ⟨fuel, t, runT, stable, memory, nextPC, nextRow, nextPointer, nextWords⟩ :=
      loop_row_run s base sp source dst left row leftRaw right doneWords buffer space rowBound
        rightPositive prefixLength bufferLength sourcePhysical sourceOwned code error aligned pc
        spAt sourceAt rowPointer rowAt countAt dstAt leftAt rightAt widthAt
        (by simpa only [leftPointerAt, leftPayloadAt] using leftOperand) rightWords bufferWords
    rw [factorEq] at nextWords
    let updated := LimbMul.nativeRow factor right buffer
    have updatedLength : updated.length = buffer.length := nativeRow_length factor right buffer (by omega)
    have updatedPositive : 0 < updated.length := by rw [updatedLength]; omega
    have updatedSplit : updated.head?.getD 0#64 :: updated.tail = updated := loop_head_tail updated updatedPositive
    by_cases last : factors = []
    · subst factors
      have finalRow : row + 1 = left := by simpa using rows
      refine ⟨fuel, t, runT, stable, memory, ?_, ?_, ?_, ?_⟩
      · simpa [finalRow] using nextPC
      · simpa only [finalRow] using nextRow
      · simpa only [finalRow] using nextPointer
      · simpa only [LimbMul.nativeRows, ← updatedSplit] using nextWords
    · have more : 0 < factors.length := List.length_pos.mpr last
      have lower : row + 1 < left := by simp only [List.length_cons] at rows; omega
      have indexedTail : ∀ k (hk : k < factors.length), factors[k] = leftRaw[(row + 1) + k]?.getD 0#64 := by
        intro k hk
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 k] using indexed (k + 1) (by simp; omega)
      have prefixWords : Words t dst (currentWords (doneWords ++ [updated.head?.getD 0#64]) updated.tail) := by
        simpa only [currentWords, List.append_assoc, List.singleton_append, updatedSplit] using nextWords
      have operandT := loop_operand_preserve memory stable.sp leftOwned leftOperand
      obtain ⟨moreFuel, u, runU, finalStable, finalFrame, finalPC, finalRow, finalPointer, finalWords⟩ :=
        ih more (row + 1) (doneWords ++ [updated.head?.getD 0#64]) updated.tail t
          (by simp only [List.length_cons] at rows; omega) indexedTail
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by simp only [List.length_tail, updatedLength]; omega)
          (stable.code code) (stable.error.trans error) (stable.aligned aligned)
          (by simpa [show row + 1 ≠ left by omega] using nextPC)
          (stable.sp.trans spAt)
          ((stable.registers _ (by decide)).trans sourceAt)
          ((stable.registers _ (by decide)).trans leftPointerAt)
          ((stable.registers _ (by decide)).trans leftPayloadAt)
          nextPointer nextRow
          ((stable.registers _ (by decide)).trans countAt)
          ((stable.registers _ (by decide)).trans dstAt)
          ((stable.registers _ (by decide)).trans leftAt)
          ((stable.registers _ (by decide)).trans rightAt)
          ((stable.registers _ (by decide)).trans widthAt) operandT
          (words_preserve memory sourcePhysical sourceOwned rightWords) prefixWords
      refine ⟨fuel + moreFuel, u, by rw [run_plus, runT, runU], stable.trans finalStable,
        memory.trans finalFrame, finalPC, finalRow, finalPointer, ?_⟩
      simpa only [LimbMul.nativeRows, List.append_assoc, List.singleton_append, updated] using finalWords

end SszArm.NatMul
