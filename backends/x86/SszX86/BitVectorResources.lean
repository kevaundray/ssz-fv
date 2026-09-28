import SszX86.BitVectorCore

namespace SszX86.BitVector
open SszNative

/-- Native normalization can shrink a span but cannot invent a new limb pointer. -/
theorem from_words_large_span (pointer resultPointer : BitVec 64)
    (words resultWords : List (BitVec 64))
    (result : NatOperand.fromWords pointer words = .large resultPointer resultWords) :
    resultPointer = pointer ∧ resultWords.length ≤ words.length := by
  have lengthBound : (Limbs.trim words).length ≤ words.length := by
    rw [Limbs.trim_length]
    exact Limbs.sigWords_le_length words
  cases trimmed : Limbs.trim words with
  | nil => simp only [NatOperand.fromWords, trimmed] at result; cases result
  | cons first rest =>
    cases rest with
    | nil => simp only [NatOperand.fromWords, trimmed] at result; cases result
    | cons second rest =>
      simp only [NatOperand.fromWords, trimmed] at result
      cases result
      exact ⟨rfl, by simpa only [trimmed] using lengthBound⟩

theorem wide_large_allocation (base capacity used : Nat) (wide : BitVec 128)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (success : (NatArithmetic.fromWide base capacity used wide).result = .ok (.large pointer words)) :
    ∃ reservation,
      (NatArithmetic.fromWide base capacity used wide).allocation = some reservation ∧
      pointer = BitVec.ofNat 64 reservation.pointer ∧
      words.length ≤ (NatArithmetic.fromWide base capacity used wide).written.length := by
  by_cases small : wide.toNat < 2^64
  · simp only [NatArithmetic.fromWide, small, ↓reduceIte, NatArithmetic.unchanged] at success
    cases success
  · cases allocated : Arena.reserve base capacity used 2 with
    | none =>
      simp only [NatArithmetic.fromWide, small, ↓reduceIte, allocated, NatArithmetic.unchanged] at success
      cases success
    | some reservation =>
      simp only [NatArithmetic.fromWide, small, ↓reduceIte, allocated, NatArithmetic.committed] at success ⊢
      exact ⟨reservation, rfl,
        from_words_large_span _ _ _ _ (Except.ok.inj success)⟩

/-- Division by eight never borrows a Large quotient. Its retained span is inside
the precise committed buffer, even when redundant high quotient limbs are zero. -/
theorem division_large_allocation (length : NatOperand) (base capacity used : Nat)
    (pointer remainder : BitVec 64) (words : List (BitVec 64))
    (success : (SszNative.NatDivision.run length 8 base capacity used).result =
      .ok (.large pointer words, remainder)) :
    ∃ reservation,
      (SszNative.NatDivision.run length 8 base capacity used).allocation = some reservation ∧
      pointer = BitVec.ofNat 64 reservation.pointer ∧
      words.length ≤ (SszNative.NatDivision.run length 8 base capacity used).written.length := by
  by_cases small : length.wordCount ≤ 2
  · rw [SszNative.NatDivision.phase_wide length 8 base capacity used (by decide) (by decide) small]
      at success ⊢
    cases quotient : (NatArithmetic.fromWide base capacity used
        (SszNative.NatDivision.wideQuotient length 8)).result with
    | error reason => simp only [quotient, Except.map] at success; cases success
    | ok result =>
      simp only [quotient, Except.map, Except.ok.injEq, Prod.mk.injEq] at success
      obtain ⟨rfl, _⟩ := success
      exact wide_large_allocation base capacity used _ pointer words quotient
  · cases allocated : Arena.reserve base capacity used length.wordCount with
    | none =>
      simp only [SszNative.NatDivision.run, show (8 : BitVec 64) ≠ 0 by decide,
        show (8 : BitVec 64) ≠ 1 by decide, small, ↓reduceIte, allocated,
        NatArithmetic.unchanged] at success
      cases success
    | some reservation =>
      simp only [SszNative.NatDivision.run, show (8 : BitVec 64) ≠ 0 by decide,
        show (8 : BitVec 64) ≠ 1 by decide, small, ↓reduceIte, allocated] at success ⊢
      have pair := Except.ok.inj success
      exact ⟨reservation, rfl, from_words_large_span _ _ _ _ (congrArg Prod.fst pair)⟩

/-- The ABI used≤capacity invariant survives every division outcome, including
failure, and every successful reservation moves the cursor forward. -/
theorem division_used_bounds (s : MachineData) (length : NatOperand)
    (address capacity used ra : BitVec 64)
    (owned : NatDivision.Owned s length 8 address capacity used ra)
    (usedBound : used.toNat ≤ capacity.toNat) :
    used.toNat ≤ (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).used ∧
    (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).used ≤ capacity.toNat := by
  cases allocated : (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).allocation with
  | none =>
    rw [(SszNative.NatDivision.no_allocation_resources length 8 _ _ _ allocated).1]
    exact ⟨Nat.le_refl _, usedBound⟩
  | some reservation =>
    have geometry := NatDivision.allocation_bounds s length 8 address capacity used ra owned reservation allocated
    have cursor := (SszNative.NatDivision.allocation_resources length 8 _ _ _ reservation allocated).1
    rw [cursor]
    exact ⟨by omega, geometry.2.2.2.2.1⟩

end SszX86.BitVector
