import SszArm.NatMulLoopRound
import SszArm.NatMulLoopMemoryFrame
import SszArm.NatMulLoopMemoryRows

namespace SszArm.NatMul

open SszNative (LimbMul)
open NatCompare (Words)
open Delimited (Protected MemoryFrame)

/-- The row invariant is the complete allocated buffer: a finalized prefix and
an unread suffix. Its length is physical allocation size, not a logical cap. -/
def currentWords (doneWords unread : List (BitVec 64)) : List (BitVec 64) := doneWords ++ unread

/-- Natural induction over all remaining columns. Every successor invokes the
actual +680..+948 instruction execution and derives its new memory observation
from that execution's one-cell frame. -/
theorem loop_inner_runs (base sp source dst : BitVec 64) (left row : Nat)
    (right : List (BitVec 64)) (factor : BitVec 64)
    (space : LoopSpace sp dst (left + right.length))
    (rowBound : row < left)
    (sourcePhysical : source.toNat + 8 * right.length ≤ 2^64)
    (sourceOwned : Protected (loopWrites sp dst (left + right.length))
      source.toNat (8 * right.length)) :
    ∀ remaining, 0 < remaining → ∀ column doneWords old carry (s : ArmState),
    column + remaining = right.length → doneWords.length = row + column →
    doneWords.length + old.length = left + right.length → remaining ≤ old.length →
    carry < 2^64 →
    CodeAt s base → read_err s = .None → CheckSPAlignment s →
    read_pc s = base + 680#64 → r (.GPR 31#5) s = sp →
    r (.GPR 8#5) s = source → r (.GPR 11#5) s = dst + BitVec.ofNat 64 (8 * row) →
    r (.GPR 12#5) s = BitVec.ofNat 64 row → r (.GPR 14#5) s = factor →
    r (.GPR 15#5) s = BitVec.ofNat 64 carry → r (.GPR 16#5) s = BitVec.ofNat 64 column →
    r (.GPR 17#5) s = 0#64 → r (.GPR 19#5) s = BitVec.ofNat 64 (left + right.length) →
    r (.GPR 20#5) s = dst → r (.GPR 25#5) s = BitVec.ofNat 64 right.length →
    Words s source right → Words s dst (currentWords doneWords old) →
    ∃ fuel t, run fuel s = t ∧ LoopStable loopInnerChanged s t ∧
      MemoryFrame (loopWrites sp dst (left + right.length)) s t ∧
      read_pc t = base + 952#64 ∧ r (.GPR 16#5) t = BitVec.ofNat 64 right.length ∧
      r (.GPR 15#5) t = BitVec.ofNat 64 (LimbMul.inner remaining factor (right.drop column) old carry).2 ∧
      r (.GPR 17#5) t = 0#64 ∧
      Words t dst (doneWords ++ (LimbMul.inner remaining factor (right.drop column) old carry).1 ++ old.drop remaining) := by
  intro remaining
  induction remaining with
  | zero => intro positive; omega
  | succ remaining ih =>
    intro positive column doneWords old carry s width prefixLength bufferLength room carryBound
      code error aligned pc spAt sourceAt rowPointer rowAt factorAt carryAt columnAt
      zero countAt dstAt widthAt rightAt bufferAt
    cases old with
    | nil => simp only [List.length_nil] at room; omega
    | cons oldWord old =>
      have columnBound : column < right.length := by omega
      let word := right[column]?.getD 0#64
      let one := LimbMul.step factor word oldWord carry
      have carryNat : (BitVec.ofNat 64 carry).toNat = carry := by
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt carryBound]
      have sourceAddress : LoopLoadSite.right.address s = source + BitVec.ofNat 64 (8 * column) := by
        simp only [LoopLoadSite.address, LoopLoadSite.pointer, sourceAt, columnAt]
        bv_omega
      have sourceNat : (LoopLoadSite.right.address s).toNat = source.toNat + 8 * column := by
        rw [sourceAddress]
        bv_omega
      have destinationAddress : LoopStoreSite.output.address s = dst + BitVec.ofNat 64 (8 * doneWords.length) := by
        simp only [LoopStoreSite.address, LoopStoreSite.pointer, LoopStoreSite.index, rowPointer, columnAt, prefixLength]
        bv_omega
      have destinationNat : (LoopStoreSite.output.address s).toNat = dst.toNat + 8 * doneWords.length := by
        rw [destinationAddress]
        exact space.address (by simp only [List.length_cons] at bufferLength; omega)
      have sourceSeparate : (LoopLoadSite.right.address s).toNat + 8 ≤ sp.toNat - 48 ∨
          sp.toNat ≤ (LoopLoadSite.right.address s).toNat := by
        rw [sourceNat]
        rcases sourceOwned with empty | separate
        · omega
        · have apart := separate (sp.toNat - 48, 48) (by simp [loopWrites])
          have := space.stack
          simp only [Prod.fst, Prod.snd] at apart
          omega
      have sourceRead : read_mem_bytes 8 (LoopLoadSite.right.address s) s = word := by
        rw [sourceAddress]
        simpa [word, List.getElem?_eq_getElem columnBound] using rightAt ⟨column, columnBound⟩
      have previousRead : read_mem_bytes 8 (LoopStoreSite.output.address s) s = oldWord := by
        rw [destinationAddress]
        have suffix := ((words_append s dst doneWords (oldWord :: old)).mp bufferAt).2
        simpa using suffix ⟨0, by simp⟩
      obtain ⟨fuel, t, runT, stable, cellFrame, nextPC, nextColumn, nextCarry, nextZero, stored⟩ :=
        loop_round_run s base left right.length row column factor word oldWord (BitVec.ofNat 64 carry)
          code error aligned pc (by rw [spAt]; exact space.stack)
          (by rw [dstAt]; exact space.physical) rowAt columnAt countAt widthAt rowBound columnBound
          factorAt carryAt zero
          (by rw [sourceNat]; omega) (by rw [spAt]; exact sourceSeparate)
          (by rw [destinationNat]; have := space.physical; simp only [List.length_cons] at bufferLength; omega)
          (by rw [destinationNat, spAt]; have := space.apart; simp only [List.length_cons] at bufferLength; omega)
          sourceRead previousRead
      rw [carryNat] at nextCarry stored
      have cell : MemoryFrame [(sp.toNat - 48, 48),
          ((dst + BitVec.ofNat 64 (8 * doneWords.length)).toNat, 8)] s t := by
        simpa only [spAt, destinationAddress] using cellFrame
      have frame := loopFrame_of_cell space doneWords.length
        (by simp only [List.length_cons] at bufferLength; omega) cell
      have updated : Words t dst ((doneWords ++ [one.1]) ++ old) := by
        apply words_replace_of_frame doneWords old (by simpa only [List.length_append, List.length_cons,
          bufferLength] using space) bufferAt cell
        simpa only [destinationAddress, one] using stored
      have remainingBound : one.2 < 2^64 := LimbMul.step_carry_lt _ _ _ _ carryBound
      by_cases last : remaining = 0
      · subst remaining
        refine ⟨fuel, t, runT, stable, frame, ?_, ?_, ?_, nextZero, ?_⟩
        · simpa [show column + 1 = right.length by omega] using nextPC
        · simpa [show column + 1 = right.length by omega] using nextColumn
        · simpa [LimbMul.inner, List.head?_drop, one, word] using nextCarry
        · simpa [LimbMul.inner, List.head?_drop, one, word, List.append_assoc] using updated
      · obtain ⟨more, u, runU, finalStable, finalFrame, finalPC, finalColumn, finalCarry, finalZero, finalWords⟩ :=
          ih (by omega) (column + 1) (doneWords ++ [one.1]) old one.2 t
            (by omega) (by simp only [List.length_append, List.length_singleton]; omega)
            (by simp only [List.length_append, List.length_singleton, List.length_cons] at *; omega)
            (by simp only [List.length_cons] at room; omega) remainingBound
            (stable.code code) (stable.error.trans error) (stable.aligned aligned)
            (by simpa [show column + 1 ≠ right.length by omega] using nextPC)
            (stable.sp.trans spAt)
            ((stable.registers _ (by decide)).trans sourceAt)
            ((stable.registers _ (by decide)).trans rowPointer)
            ((stable.registers _ (by decide)).trans rowAt)
            ((stable.registers _ (by decide)).trans factorAt)
            nextCarry nextColumn nextZero
            ((stable.registers _ (by decide)).trans countAt)
            ((stable.registers _ (by decide)).trans dstAt)
            ((stable.registers _ (by decide)).trans widthAt)
            (words_preserve frame sourcePhysical sourceOwned rightAt) updated
        refine ⟨fuel + more, u, by rw [run_plus, runT, runU], stable.trans finalStable,
          frame.trans finalFrame, finalPC, finalColumn, ?_, finalZero, ?_⟩
        · simpa [LimbMul.inner, List.head?_drop, List.tail_drop, one, word] using finalCarry
        · simpa [LimbMul.inner, List.head?_drop, List.tail_drop, one, word,
            List.append_assoc] using finalWords

end SszArm.NatMul
