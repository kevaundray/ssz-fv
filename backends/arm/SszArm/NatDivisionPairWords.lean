import SszArm.NatDivisionWide
import SszArm.NatDivisionMemory

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- A nonnull count-two Nat pair determines both physical limbs uniquely. -/
theorem pair_two_words (observe : Nat → Nat → Option Nat) (pointer low high : BitVec 64)
    (positive : 0 < pointer.toNat)
    (pair : SszNative.NatMemory.Pair observe pointer 2#64
      (low.toNat + 2^64 * high.toNat)) :
    SszNative.NatMemory.wordsAt observe pointer.toNat [low, high] := by
  rcases pair with ⟨zero, _⟩ | ⟨words, _, _, _, count, stored, value⟩
  · rw [zero] at positive
    simp at positive
  · change 2 = words.length at count
    cases words with
    | nil => simp at count
    | cons first rest =>
      cases rest with
      | nil => simp at count
      | cons second rest =>
        have nil : rest = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at count; omega)
        subst rest
        have joined : Udivti3.join first second = Udivti3.join low high := by
          simp only [SszNative.Limbs.value, Nat.mul_zero, Nat.add_zero] at value
          simp only [Udivti3.join, Udivti3.radix]
          omega
        obtain ⟨rfl, rfl⟩ := join_unique first second low high joined
        exact stored

end SszArm.NatDivision
