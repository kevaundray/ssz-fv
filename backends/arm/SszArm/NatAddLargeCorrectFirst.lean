import SszArm.NatAddLargeCorrectAllocation

namespace SszArm.NatAdd.LargeCorrect

open SszNative
open UintCodec (widthLoad)
open Delimited (MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def firstKind : NatOperand → NatOperand → FirstKind
  | .small _, _ => .smallLarge
  | .large _ _, .small _ => .largeSmall
  | .large _ _, .large _ _ => .largeLarge

def firstStep (left right : NatOperand) : BitVec 64 × Nat :=
  LimbAdd.step (left.words[0]?.getD 0) (right.words[0]?.getD 0) 0

theorem first_low (left right : NatOperand) :
    left.words[0]?.getD 0 + right.words[0]?.getD 0 = (firstStep left right).1 := by
  simp only [firstStep, LimbAdd.step, Nat.add_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]

theorem first_carry (left right : NatOperand) :
    (if 2^64 ≤ (left.words[0]?.getD 0).toNat + (right.words[0]?.getD 0).toNat
      then 1#64 else 0#64) = BitVec.ofNat 64 (firstStep left right).2 := by
  have hl := (left.words[0]?.getD 0).isLt
  have hr := (right.words[0]?.getD 0).isLt
  simp only [firstStep, LimbAdd.step, Nat.add_zero]
  split <;> apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem first_written (left right : NatOperand) :
    (firstStep left right).1 = (SszNative.NatAdd.writtenWords left right)[0]?.getD 0 := by
  rw [← LargeLoop.native_words left right]
  rfl

private theorem large_first (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64))
    (input : (NatOperand.large pointer words).At (widthLoad s))
    (nonzero : (NatOperand.large pointer words).wordCount ≠ 0) :
    BitVec.ofNat 64 words.length ≠ 0#64 ∧
      read_mem_bytes 8 pointer s = words[0]?.getD 0 := by
  have count := Limbs.sigWords_le_length words
  have physical := input.2.2.1
  have positive : 0 < words.length := by
    change Limbs.sigWords words ≠ 0 at nonzero
    omega
  refine ⟨by bv_omega, ?_⟩
  have word := words_of_at s pointer words input ⟨0, positive⟩
  simpa only [Nat.mul_zero, BitVec.ofNat_zero, BitVec.add_zero,
    List.getElem?_eq_getElem positive, Option.getD_some] using word

/-- Reconcile the original tagged operands with the real first-word dispatch.
The forbidden Small/Small branch is excluded by the significant-count premise. -/
theorem first_run (s u : ArmState) (base : BitVec 64) (left right : NatOperand)
    (reservation : Arena.Reservation) (owned : Owned s left right)
    (allocated : Allocation s left right reservation)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (large : ¬ (left.wordCount ≤ 1 ∧ right.wordCount ≤ 1))
    (hc : CodeAt u base) (he : read_err u = .None) (ha : CheckSPAlignment u)
    (hp : read_pc u = base + 276#64) (frame : Frame s u)
    (memory : MemoryFrame (writesFor s (outcome s left right)) s u)
    (h9 : r (.GPR 9#5) u = BitVec.ofNat 64 reservation.pointer) :
    ∃ fuel v, run fuel u = v ∧
      FirstWordPost (firstKind left right) u v base
        (left.words[0]?.getD 0) (right.words[0]?.getD 0) ∧
      MemoryFrame (writesFor s (outcome s left right)) s v := by
  have lu := operand_at_preserved memory left owned.leftAt owned.leftOwned
  have ru := operand_at_preserved memory right owned.rightAt owned.rightOwned
  have r1 := (frame.registers 1#5 (by decide)).trans owned.leftPointer
  have r2 := (frame.registers 2#5 (by decide)).trans owned.leftPayload
  have r3 := (frame.registers 3#5 (by decide)).trans owned.rightPointer
  have r4 := (frame.registers 4#5 (by decide)).trans owned.rightPayload
  have leftKind : r (.GPR 1#5) u = 0#64 ↔ firstKind left right = .smallLarge := by
    rw [r1]
    cases left with
    | small word => simp [NatOperand.pointer, firstKind]
    | large pointer words =>
      have positive := lu.1
      cases right <;> simp [NatOperand.pointer, firstKind]
      all_goals intro zero; simp [zero] at positive
  have rightKind : r (.GPR 3#5) u = 0#64 ↔ firstKind left right = .largeSmall := by
    rw [r3]
    cases left with
    | small word =>
      cases right with
      | small rightWord =>
        have hl := Limbs.sigWords_le_length [word]
        have hr := Limbs.sigWords_le_length [rightWord]
        exfalso
        apply large
        constructor
        · change Limbs.sigWords [word] ≤ 1
          simpa using hl
        · change Limbs.sigWords [rightWord] ≤ 1
          simpa using hr
      | large pointer words =>
        have positive := ru.1
        simp [NatOperand.pointer, firstKind]
        intro zero; simp [zero] at positive
    | large pointer words =>
      cases right with
      | small word => simp [NatOperand.pointer, firstKind]
      | large rightPointer rightWords =>
        have positive := ru.1
        simp [NatOperand.pointer, firstKind]
        intro zero; simp [zero] at positive
  have leftRead : if firstKind left right = .smallLarge then
      r (.GPR 2#5) u = left.words[0]?.getD 0 else
      r (.GPR 2#5) u ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 1#5) u) u = left.words[0]?.getD 0 := by
    rw [r1, r2]
    cases left with
    | small word => simp [firstKind, NatOperand.words, NatOperand.payload]
    | large pointer words =>
      have data := large_first u pointer words lu leftNonzero
      cases right <;> simpa [firstKind, NatOperand.words, NatOperand.payload] using data
  have rightRead : if firstKind left right = .largeSmall then
      r (.GPR 4#5) u = right.words[0]?.getD 0 else
      r (.GPR 4#5) u ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 3#5) u) u = right.words[0]?.getD 0 := by
    rw [r3, r4]
    cases right with
    | small word =>
      have same : firstKind left (.small word) = .largeSmall := rightKind.mp (by simpa [r3])
      simp [same, NatOperand.words, NatOperand.payload]
    | large pointer words =>
      have data := large_first u pointer words ru rightNonzero
      cases left <;> simpa [firstKind, NatOperand.words, NatOperand.payload] using data
  have pointerNat : (BitVec.ofNat 64 reservation.pointer).toNat = reservation.pointer :=
    BitVec.toNat_ofNat_of_lt allocated.pointer_bound
  obtain ⟨runFirst, first⟩ := first_word_run u base (left.words[0]?.getD 0)
    (right.words[0]?.getD 0) (firstKind left right) hc he ha hp
      (by rw [h9, pointerNat]; have := allocated.physical; omega)
      leftKind rightKind leftRead rightRead
  let ops := (firstKind left right).ops
    (sumOverflow (left.words[0]?.getD 0) (right.words[0]?.getD 0))
  let v := block base ops u
  refine ⟨ops.length, v, runFirst, first, memory.trans ?_⟩
  apply memory_of_contained first.memory
  intro inner member
  simp only [List.mem_singleton] at member
  subst inner
  rw [h9, pointerNat]
  refine ⟨(reservation.pointer, 8 * (SszNative.NatAdd.count left right + 1)), ?_, by omega, ?_⟩
  · rw [allocated.writes]; simp
  · simp only [Prod.fst, Prod.snd]; omega

end SszArm.NatAdd.LargeCorrect
