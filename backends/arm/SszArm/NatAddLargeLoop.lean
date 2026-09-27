import SszArm.NatAddLargeLoopRound

namespace SszArm.NatAdd.LargeLoop

open SszNative
open Delimited (Protected)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Complete arbitrary-length execution from the actual PC1692 entry to
PC2044. Every allocated suffix word is exactly the corresponding frozen
native loop word. The frame excludes the already-written low prefix. -/
theorem loop_run (base stack output : BitVec 64) (left right : List (BitVec 64)) :
    ∀ remaining index carry (s : ArmState),
    CodeAt s base → read_err s = .None → CheckSPAlignment s →
    read_pc s = base + 1692#64 →
    Invariant s stack output left right index remaining carry →
    ∃ fuel t, run fuel s = t ∧
      LoopFrame (suffixWrites stack output index remaining) s t ∧
      read_pc t = base + 2044#64 ∧
      r (.GPR 12#5) t = BitVec.ofNat 64
        (LimbAdd.loop remaining (left.drop index) (right.drop index) carry).2 ∧
      r (.GPR 14#5) t = 0#64 ∧
      r (.GPR 15#5) t = BitVec.ofNat 64 (index + remaining) ∧
      r (.GPR 13#5) t = r (.GPR 13#5) s ∧
      SuffixWords t output index
        (LimbAdd.loop remaining (left.drop index) (right.drop index) carry).1 := by
  intro remaining
  induction remaining with
  | zero =>
    intro index carry s hc he ha hp inv
    have := inv.remainingPositive
    omega
  | succ remaining ih =>
    intro index carry s hc he ha hp inv
    let next := LimbAdd.step (left[index]?.getD 0) (right[index]?.getD 0) carry
    obtain ⟨roundFuel, u, urun, uf, up, u12, u14, u15, u13, stored⟩ :=
      round_run s base stack output left right index (remaining + 1) carry hc he ha hp inv
    by_cases last : remaining = 0
    · subst remaining
      refine ⟨roundFuel, u, urun, uf, ?_, ?_, ?_, u15, u13, ?_⟩
      · simpa using up
      · simpa only [LimbAdd.loop_indexed_succ, LimbAdd.loop] using u12
      · simpa using u14
      · rw [LimbAdd.loop_indexed_succ]
        apply suffix_words_cons u output next.1 index [] stored
        intro i
        exact Fin.elim0 i
    · have nonfinal : 0 < remaining := by omega
      have uinv : Invariant u stack output left right (index + 1) remaining next.2 :=
        invariant_next stack output left right index remaining carry inv nonfinal uf
          u12 (by simpa using u14) u15 u13
      have up' : read_pc u = base + 1692#64 := by
        simpa only [show remaining + 1 ≠ 1 by omega, ↓reduceIte] using up
      obtain ⟨restFuel, t, trun, tf, tp, t12, t14, t15, t13, words⟩ :=
        ih (index + 1) next.2 u (uf.code hc) (uf.error.trans he) (uf.aligned ha) up' uinv
      have preserved : read_mem_bytes 8 (output + BitVec.ofNat 64 (8 * index)) t =
          read_mem_bytes 8 (output + BitVec.ofNat 64 (8 * index)) u := by
        have bound := inv.outputBound
        have address : (output + BitVec.ofNat 64 (8 * index)).toNat =
            output.toNat + 8 * index := by bv_omega
        apply tf.memory.read _ 8 (by rw [address]; omega)
        rw [address]
        apply suffix_head_protected stack output index remaining
        simpa only [Nat.add_assoc] using inv.outputStack
      refine ⟨roundFuel + restFuel, t, ?_,
        uf.trans (suffixFrame_extend stack output index remaining tf), tp, ?_, t14, ?_,
        t13.trans u13, ?_⟩
      · rw [run_plus, urun, trun]
      · rw [LimbAdd.loop_indexed_succ]
        exact t12
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using t15
      · rw [LimbAdd.loop_indexed_succ]
        exact suffix_words_cons t output next.1 index _ (preserved.trans stored) words

/-- Entry after the first word has been stored and registers1552..1568 have
run. Significant width controls the reservation, not the physical list length.
The extra allocated word consumes the carry even for noncanonical originals. -/
theorem entry_run (s : ArmState) (base stack output first : BitVec 64)
    (left right : List (BitVec 64)) (count carry : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1692#64)
    (inv : Invariant s stack output left right 1 count carry)
    (leftCount : (Limbs.trim left).length ≤ count)
    (rightCount : (Limbs.trim right).length ≤ count)
    (low : read_mem_bytes 8 output s = first) :
    ∃ fuel t, run fuel s = t ∧
      LoopFrame (suffixWrites stack output 1 count) s t ∧
      read_pc t = base + 2044#64 ∧
      r (.GPR 12#5) t = 0#64 ∧ r (.GPR 14#5) t = 0#64 ∧
      r (.GPR 15#5) t = BitVec.ofNat 64 (count + 1) ∧
      r (.GPR 13#5) t = r (.GPR 13#5) s ∧
      NatCompare.Words t output
        (first :: (LimbAdd.loop count (left.drop 1) (right.drop 1) carry).1) := by
  obtain ⟨fuel, t, trun, frame, pc, carryOut, remainingOut, indexOut, rightSmall, words⟩ :=
    loop_run base stack output left right count 1 carry s hc he ha hp inv
  have countPositive := inv.remainingPositive
  have carryZero : (LimbAdd.loop count (left.drop 1) (right.drop 1) carry).2 = 0 := by
    simpa using final_carry left right count 1 carry leftCount rightCount
      (by omega) inv.carryBound
  have firstProtected : Protected (suffixWrites stack output 1 count) output.toNat 8 := by
    have lowOwned := inv.outputStack.subspan 0 8 (by omega)
    rcases lowOwned with empty | apart
    · omega
    · right
      intro span member
      simp only [suffixWrites, List.mem_cons, List.mem_singleton] at member
      rcases member with rfl | rfl
      · simpa using apart (stack.toNat - 16, 16) (by simp)
      · simp only [Prod.fst, Prod.snd]
        omega
  have preserved : read_mem_bytes 8 output t = first := by
    rw [frame.memory.read output 8 (by have := inv.outputBound; omega) firstProtected]
    exact low
  have allWords := suffix_words_cons t output first 0 _ (by simpa using preserved)
    (by simpa using words)
  refine ⟨fuel, t, trun, frame, pc, ?_, remainingOut, ?_, rightSmall, ?_⟩
  · simpa only [carryZero] using carryOut
  · simpa only [Nat.add_comm] using indexOut
  · simpa using allWords.words

end SszArm.NatAdd.LargeLoop
