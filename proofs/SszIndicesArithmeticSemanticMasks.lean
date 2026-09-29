import SszIndicesArithmeticSemanticMake

set_option autoImplicit false

namespace SszNative.Indices

theorem belowWord_bit (index : NatOperand) (bits position offset : Nat) (inside : offset < 64) :
    (word index position &&& rangeWord position 0 bits).getLsbD offset =
      (Ssz.gindexBelow index.value bits).testBit (64 * position + offset) := by
  rw [BitVec.getLsbD_and, word_bit index position offset inside,
    rangeWord_bit position 0 bits offset inside]
  simp [Ssz.gindexBelow, Nat.testBit_mod_two_pow, Bool.and_comm]

theorem belowCount_le (index : NatOperand) (bits count : Nat) :
    belowCount index bits count ≤ count := by
  induction count with
  | zero => exact Nat.le_refl 0
  | succ count ih => simp only [belowCount]; split <;> omega

theorem belowCount_zero_above (index : NatOperand) (bits count position : Nat)
    (trimmed : belowCount index bits count ≤ position) (inside : position < count) :
    word index position &&& rangeWord position 0 bits = 0 := by
  induction count generalizing position with
  | zero => omega
  | succ count ih =>
      simp only [belowCount] at trimmed
      split at trimmed
      · rename_i zero
        by_cases last : position = count
        · subst position
          simpa only [beq_iff_eq] using zero
        · exact ih position trimmed (by omega)
      · omega

theorem below_fast (index : NatOperand) (bits base capacity used : Nat)
    (past : bitLength index ≤ bits) :
    below index bits base capacity used = unchanged used (.ok index) := by
  simp [below, past]

theorem below_value (index : NatOperand) (bits base capacity used : Nat) (result : NatOperand)
    (success : (below index bits base capacity used).result = .ok result) :
    result.value = Ssz.gindexBelow index.value bits := by
  unfold below at success
  split at success
  · rename_i past
    simp only [unchanged, Except.ok.injEq] at success
    subst result
    apply (Nat.mod_eq_of_lt _).symm
    apply (NatShift.bitLength_le_iff index bits).mp
    simpa only [NatShift.bitLength, ← bitLength_value] using past
  · cases counted : wordCount bits with
    | error reason => simp [counted, unchanged] at success
    | ok count =>
        simp only [counted] at success
        apply makeNat_value_of_bits _ base capacity used _ _ result
          (belowWord_bit index bits) _ success
        intro position past
        have covers := wordCount_covers bits count counted
        by_cases inside : position / 64 < count
        · have zero := belowCount_zero_above index bits count (position / 64) (by omega) inside
          have digit := belowWord_bit index bits (position / 64) (position % 64)
            (Nat.mod_lt _ (by decide))
          have zeroBit : (0 : BitVec 64).getLsbD (position % 64) = false := by simp
          rw [zero, zeroBit,
            show 64 * (position / 64) + position % 64 = position by omega] at digit
          exact digit.symm
        · have outside : ¬position < bits := by omega
          simp [Ssz.gindexBelow, Nat.testBit_mod_two_pow, outside]

theorem rebase_eq_or (index bits : Nat) :
    Ssz.gindexRebase index bits = (2 ^ bits ||| (index % 2 ^ bits)) := by
  simpa [Ssz.gindexRebase, Ssz.gindexBelow] using
    (Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt index (Nat.two_pow_pos bits)) 1)

theorem rebaseWord_bit (index : NatOperand) (bits position offset : Nat) (inside : offset < 64) :
    ((word index position &&& rangeWord position 0 bits) |||
      rangeWord position bits (bits + 1)).getLsbD offset =
        (Ssz.gindexRebase index.value bits).testBit (64 * position + offset) := by
  rw [BitVec.getLsbD_or, belowWord_bit index bits position offset inside,
    rangeWord_bit position bits (bits + 1) offset inside,
    rebase_eq_or, Nat.testBit_or, Nat.testBit_two_pow]
  have leading : (bits ≤ 64 * position + offset ∧ 64 * position + offset < bits + 1) ↔
      bits = 64 * position + offset := by omega
  simp only [Ssz.gindexBelow, leading, Bool.or_comm]

theorem rebase_value (index : NatOperand) (bits base capacity used : Nat) (result : NatOperand)
    (_physical : index.words.length < 2 ^ 64)
    (success : (rebase index bits base capacity used).result = .ok result) :
    result.value = Ssz.gindexRebase index.value bits := by
  unfold rebase at success
  split at success
  · cases counted : wordCount (bits + 1) with
    | error reason => simp [counted, unchanged] at success
    | ok count =>
        simp only [counted] at success
        apply makeNat_value_of_bits count base capacity used _ _ result
          (rebaseWord_bit index bits) _ success
        intro position past
        have covers := wordCount_covers (bits + 1) count counted
        have different : bits ≠ position := by omega
        have outside : ¬position < bits := by omega
        simp [rebase_eq_or, Nat.testBit_or, Nat.testBit_mod_two_pow, different, outside]
  · cases success

end SszNative.Indices
