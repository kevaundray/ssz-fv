import SszX86.BitVectorResources

namespace SszX86.BitVector
open SszNative

theorem add_used_bounds (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : NatAdd.Owned s left right address capacity used ra) :
    used.toNat ≤ (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used ∧
    (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used ≤ capacity.toNat := by
  cases allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation with
  | none =>
    rw [(SszNative.NatAdd.no_allocation_resources left right _ _ _ allocated).1]
    exact ⟨Nat.le_refl _, owned.used_bound⟩
  | some reservation =>
    have geometry := NatAdd.allocation_bounds s left right address capacity used ra owned reservation allocated
    have cursor := (SszNative.NatAdd.allocation_exact left right address.toNat capacity.toNat
      used.toNat reservation allocated).1
    rw [cursor]
    exact ⟨by omega, geometry.2.2.2.2.1⟩

/-- Adding the actual nonzero Small(1) never returns a borrowed Large expected
count. Any such result is inside its own exact committed buffer. -/
theorem round_large_allocation (quotient : NatOperand) (base capacity used : Nat)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (success : (SszNative.NatAdd.run quotient (.small 1) base capacity used).result =
      .ok (.large pointer words)) :
    ∃ reservation,
      (SszNative.NatAdd.run quotient (.small 1) base capacity used).allocation = some reservation ∧
      pointer = BitVec.ofNat 64 reservation.pointer ∧
      words.length ≤ (SszNative.NatAdd.run quotient (.small 1) base capacity used).written.length := by
  by_cases zero : quotient.wordCount = 0
  · rw [SszNative.NatAdd.run_zero_left quotient (.small 1) base capacity used zero] at success
    cases success
  · by_cases small : quotient.wordCount ≤ 1
    · rw [SszNative.NatAdd.run_one_word quotient (.small 1) base capacity used zero (by decide)
        ⟨small, by decide⟩] at success ⊢
      exact wide_large_allocation base capacity used _ pointer words success
    · rw [SszNative.NatAdd.run_large quotient (.small 1) base capacity used zero (by decide)
        (by intro h; exact small h.1)] at success ⊢
      by_cases fits : SszNative.NatAdd.count quotient (.small 1) + 1 < 2^64
      · simp only [fits, ↓reduceIte] at success ⊢
        cases reserved : Arena.reserve base capacity used (SszNative.NatAdd.count quotient (.small 1) + 1) with
        | none =>
          simp only [reserved, NatArithmetic.unchanged] at success
          cases success
        | some reservation =>
          simp only [reserved, NatArithmetic.committed] at success ⊢
          exact ⟨reservation, rfl, from_words_large_span _ _ _ _ (Except.ok.inj success)⟩
      · simp only [fits, ↓reduceIte, NatArithmetic.unchanged] at success
        cases success

end SszX86.BitVector
