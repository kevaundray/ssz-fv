import SszArm.NatAddLargeCorrectFirst

namespace SszArm.NatAdd.LargeCorrect

open SszNative
open UintCodec (widthLoad)
open NatCompare (Operand Source Words)
open Delimited (Protected MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Both actual allocating carry paths, including the first-word store and
initialization. The result is the complete shared native write list at PC2044. -/
theorem words_run (s u : ArmState) (base : BitVec 64) (left right : NatOperand)
    (reservation : Arena.Reservation) (owned : Owned s left right)
    (allocated : Allocation s left right reservation)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (large : ¬ (left.wordCount ≤ 1 ∧ right.wordCount ≤ 1))
    (hc : CodeAt u base) (he : read_err u = .None) (ha : CheckSPAlignment u)
    (hp : read_pc u = base + 276#64) (frame : Frame s u)
    (memory : MemoryFrame (writesFor s (outcome s left right)) s u)
    (h8 : r (.GPR 8#5) u = BitVec.ofNat 64 (SszNative.NatAdd.count left right))
    (h9 : r (.GPR 9#5) u = BitVec.ofNat 64 reservation.pointer)
    (h10 : r (.GPR 10#5) u = BitVec.ofNat 64 reservation.pointer) :
    ∃ fuel t, run fuel u = t ∧ Frame s t ∧
      MemoryFrame (writesFor s (outcome s left right)) s t ∧
      MemoryFrame (LargeLoop.suffixWrites (r (.GPR 31#5) s)
        (BitVec.ofNat 64 reservation.pointer) 0 (SszNative.NatAdd.count left right + 1)) u t ∧
      read_pc t = base + 2044#64 ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 (SszNative.NatAdd.count left right) ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 reservation.pointer ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 reservation.pointer ∧
      r (.GPR 11#5) t = (SszNative.NatAdd.writtenWords left right)[0]?.getD 0#64 ∧
      Words t (BitVec.ofNat 64 reservation.pointer) (SszNative.NatAdd.writtenWords left right) := by
  obtain ⟨firstFuel, v, vrun, first, vm⟩ := first_run s u base left right reservation owned
    allocated leftNonzero rightNonzero large hc he ha hp frame memory h9
  let pointer := BitVec.ofNat 64 reservation.pointer
  let stack := r (.GPR 31#5) s
  let count := SszNative.NatAdd.count left right
  have pointerNat : pointer.toNat = reservation.pointer :=
    BitVec.toNat_ofNat_of_lt allocated.pointer_bound
  have vf := first_frame first
  have rootFrame := frame.trans vf
  have v8 : r (.GPR 8#5) v = BitVec.ofNat 64 count := (first.registers _ (by decide)).trans h8
  have v9 : r (.GPR 9#5) v = pointer := (first.registers _ (by decide)).trans h9
  have v10 : r (.GPR 10#5) v = pointer := (first.registers _ (by decide)).trans h10
  have v11 : r (.GPR 11#5) v = (SszNative.NatAdd.writtenWords left right)[0]?.getD 0#64 :=
    first.first.trans ((first_low left right).trans (first_written left right))
  have v12 : r (.GPR 12#5) v = BitVec.ofNat 64 (firstStep left right).2 :=
    first.carry.trans (first_carry left right)
  have low : read_mem_bytes 8 pointer v = (firstStep left right).1 := by
    simpa only [h9] using first.stored.trans (first_low left right)
  have vsp : r (.GPR 31#5) v = stack := rootFrame.sp
  have lu := operand_at_preserved vm left owned.leftAt owned.leftOwned
  have ru := operand_at_preserved vm right owned.rightAt owned.rightOwned
  have r1 := (rootFrame.registers 1#5 (by decide)).trans owned.leftPointer
  have r2 := (rootFrame.registers 2#5 (by decide)).trans owned.leftPayload
  have r3 := (rootFrame.registers 3#5 (by decide)).trans owned.rightPointer
  have r4 := (rootFrame.registers 4#5 (by decide)).trans owned.rightPayload
  have writesEq : writesFor v (outcome s left right) = writesFor s (outcome s left right) := by
    simp only [writesFor, localWrites, rootFrame.out, rootFrame.sp,
      rootFrame.registers 5#5 (by decide)]
  have leftInput : Operand v (r (.GPR 1#5) v) (r (.GPR 2#5) v) left.words := by
    rw [r1, r2]
    exact operand_of_owned v _ left (by rw [vsp]; exact owned.stackBound) lu
      (by simpa only [writesEq] using owned.leftOwned)
  have rightInput : Operand v (r (.GPR 3#5) v) (r (.GPR 4#5) v) right.words := by
    rw [r3, r4]
    exact operand_of_owned v _ right (by rw [vsp]; exact owned.stackBound) ru
      (by simpa only [writesEq] using owned.rightOwned)
  have rightOwned : r (.GPR 3#5) v ≠ 0#64 →
      Protected (LargeLoop.suffixWrites stack pointer 1 count)
        (r (.GPR 3#5) v).toNat (8 * right.words.length) := by
    rw [r3]
    cases right with
    | small word => simp [NatOperand.pointer]
    | large address words =>
      intro nonnull
      exact protected_of_contained owned.rightOwned (allocated.suffix_contained 1 count (by omega))
  have positive : 0 < count := by
    dsimp [count, SszNative.NatAdd.count]
    omega
  have layout : SmallLoop.Layout stack pointer (count + 1) := by
    refine ⟨owned.stackBound, ?_, ?_⟩
    · simpa only [pointerNat] using allocated.physical
    · have protected := allocated.output_stack
      rcases protected with empty | apart
      · omega
      · have separate := apart (stack.toNat - 16, 16) (by simp)
        have hs := owned.stackBound
        simp only [Prod.fst, Prod.snd] at separate
        rw [pointerNat]
        omega
  have firstMemory : MemoryFrame (LargeLoop.suffixWrites stack pointer 0 (count + 1)) u v := by
    apply memory_of_contained first.memory
    intro inner member
    simp only [List.mem_singleton] at member
    subst inner
    rw [h9]
    refine ⟨(pointer.toNat, 8 * (count + 1)), by simp [LargeLoop.suffixWrites], by omega, ?_⟩
    simp only [Prod.fst, Prod.snd]; omega
  have finish (loopFuel : Nat) (t : ArmState)
      (trun : run loopFuel v = t)
      (lf : LoopFrame (LargeLoop.suffixWrites stack pointer 1 count) v t)
      (tp : read_pc t = base + 2044#64)
      (stored : Words t pointer (SszNative.NatAdd.writtenWords left right)) :
      ∃ fuel t, run fuel u = t ∧ Frame s t ∧
        MemoryFrame (writesFor s (outcome s left right)) s t ∧
        MemoryFrame (LargeLoop.suffixWrites stack pointer 0 (count + 1)) u t ∧
        read_pc t = base + 2044#64 ∧
        r (.GPR 8#5) t = BitVec.ofNat 64 count ∧ r (.GPR 9#5) t = pointer ∧
        r (.GPR 10#5) t = pointer ∧
        r (.GPR 11#5) t = (SszNative.NatAdd.writtenWords left right)[0]?.getD 0#64 ∧
        Words t pointer (SszNative.NatAdd.writtenWords left right) := by
    refine ⟨firstFuel + loopFuel, t, ?_, rootFrame.trans (loop_frame lf),
      vm.trans (memory_of_contained lf.memory (allocated.suffix_contained 1 count (by omega))),
      firstMemory.trans (LargeLoop.suffixFrame_extend stack pointer 0 count lf).memory,
      tp, (lf.registers _ (by decide)).trans v8, (lf.registers _ (by decide)).trans v9,
      (lf.registers _ (by decide)).trans v10, (lf.registers _ (by decide)).trans v11, stored⟩
    rw [run_plus, vrun, trun]
  cases left with
  | small small =>
    cases right with
    | small rightWord =>
      exfalso
      apply large
      have hl := Limbs.sigWords_le_length [small]
      have hr := Limbs.sigWords_le_length [rightWord]
      constructor
      · change Limbs.sigWords [small] ≤ 1; simpa using hl
      · change Limbs.sigWords [rightWord] ≤ 1; simpa using hr
    | large address words =>
      have nonnull : address ≠ 0#64 := by have h := ru.1; intro hz; simp [hz] at h
      have source := (rightInput.large (by simpa [r3] using nonnull)).2.1
      have limbs := (rightInput.large (by simpa [r3] using nonnull)).2.2
      obtain ⟨fuel, t, trun, tf, tp, _, _, _, _, _, _, _, _, _, stored, _⟩ :=
        SmallLoop.entry_run v base address stack pointer small words count
          (vf.code hc) (vf.error.trans he) (vf.aligned ha)
          (by simpa only [firstKind, ↓reduceIte] using first.pc)
          (by simpa only [NatOperand.pointer] using r1)
          (by simpa only [NatOperand.payload] using r2)
          (by simpa only [NatOperand.pointer] using r3) nonnull
          (by simpa only [NatOperand.payload] using r4) v8 v9
          (by simpa [firstStep, NatOperand.words, List.getElem?_zero] using v12)
          vsp layout positive (by simpa only [r3, NatOperand.pointer] using source)
          (by simpa only [r3, NatOperand.pointer] using limbs)
          (by simpa only [SmallLoop.writes, LargeLoop.suffixWrites, r3, NatOperand.pointer,
            NatOperand.words] using rightOwned (by simpa [r3] using nonnull))
          (by simpa [firstStep, NatOperand.words, List.getElem?_zero] using low)
      apply finish fuel t trun tf tp
      simpa only [SmallLoop.native_words] using stored
  | large address words =>
    have nonnull : r (.GPR 1#5) v ≠ 0#64 := by
      rw [r1]
      have h := lu.1
      intro hz
      simp [NatOperand.pointer, hz] at h
    obtain ⟨length, source, limbs⟩ := leftInput.large nonnull
    have kind : firstKind (.large address words) right ≠ .smallLarge := by cases right <;> decide
    have inv : LargeLoop.Invariant v stack pointer (.large address words).words right.words 1 count
        (firstStep (.large address words) right).2 := by
      refine ⟨by decide, positive, LimbAdd.step_carry_le _ _ 0 (by decide), vsp,
        owned.stackBound, v9, ?_, ?_, nonnull, length, source, limbs, ?_, rightInput,
        rightOwned, ?_, v12, ?_, ?_⟩
      · simpa only [Nat.add_comm 1 count, pointerNat] using allocated.physical
      · simpa only [Nat.add_comm 1 count, pointerNat] using allocated.output_stack
      · rw [r1]
        exact protected_of_contained owned.leftOwned (allocated.suffix_contained 1 count (by omega))
      · rw [first.flag kind, r3]
        cases right with
        | small word => simp [firstKind, NatOperand.pointer]
        | large rightPointer rightWords =>
          have positivePointer := ru.1
          have nonzeroPointer : rightPointer ≠ 0#64 := by intro hz; simp [hz] at positivePointer
          simp [firstKind, NatOperand.pointer, nonzeroPointer]
      · exact (first.remaining kind).trans h8
      · exact first.index kind
    obtain ⟨fuel, t, trun, tf, tp, _, _, _, _, stored⟩ :=
      LargeLoop.native_entry_run v base stack pointer (.large address words) right
        (vf.code hc) (vf.error.trans he) (vf.aligned ha)
        (by simpa only [kind, ↓reduceIte] using first.pc) inv low
    exact finish fuel t trun tf tp stored

end SszArm.NatAdd.LargeCorrect
