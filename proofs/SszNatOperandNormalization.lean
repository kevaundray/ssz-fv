import SszNatAdd

set_option autoImplicit false

namespace SszNative.NatOperand

/-- Normalization keeps a borrowed pointer exactly for a multiword value. -/
theorem fromWords_pointer (address : BitVec 64) (limbs : List (BitVec 64)) :
    (fromWords address limbs).pointer =
      if Limbs.sigWords limbs ≤ 1 then 0 else address := by
  rw [← Limbs.trim_length limbs]
  cases trimmed : Limbs.trim limbs with
  | nil => simp [fromWords, trimmed, pointer]
  | cons first rest =>
    cases rest with
    | nil => simp [fromWords, trimmed, pointer]
    | cons second rest => simp [fromWords, trimmed, pointer]

/-- The one-word payload is the original zero-extended word zero, not a new copy. -/
theorem fromWords_payload (address : BitVec 64) (limbs : List (BitVec 64)) :
    (fromWords address limbs).payload =
      if Limbs.sigWords limbs ≤ 1 then limbs[0]?.getD 0
      else BitVec.ofNat 64 (Limbs.sigWords limbs) := by
  rw [← Limbs.trim_length limbs, ← NatAdd.trim_word limbs 0]
  cases trimmed : Limbs.trim limbs with
  | nil => simp [fromWords, trimmed, payload]
  | cons first rest =>
    cases rest with
    | nil => simp [fromWords, trimmed, payload]
    | cons second rest => simp [fromWords, trimmed, payload]

/-- Trimming preserves exact observations of every retained limb. -/
theorem wordsAt_trim (observe : Nat → Nat → Option Nat) (address : Nat)
    (limbs : List (BitVec 64)) (stored : NatMemory.wordsAt observe address limbs) :
    NatMemory.wordsAt observe address (Limbs.trim limbs) := by
  intro index
  have length : (Limbs.trim limbs).length ≤ limbs.length := by
    rw [Limbs.trim_length]
    exact Limbs.sigWords_le_length limbs
  have bound : index.val < limbs.length := Nat.lt_of_lt_of_le index.isLt length
  have same := NatAdd.trim_word limbs index.val
  rw [List.getElem?_eq_getElem index.isLt, List.getElem?_eq_getElem bound] at same
  simp only [Option.getD_some] at same
  change observe (address + 8 * index.val) 8 = some ((Limbs.trim limbs)[index.val].toNat)
  rw [same]
  exact stored ⟨index.val, bound⟩

/-- A normalized borrowed result needs only the already-owned original slice. -/
theorem fromWords_at (observe : Nat → Nat → Option Nat) (address : BitVec 64)
    (limbs : List (BitVec 64)) (stored : (.large address limbs : NatOperand).At observe) :
    (fromWords address limbs).At observe := by
  obtain ⟨positive, aligned, extent, observed⟩ := stored
  have retained := wordsAt_trim observe address.toNat limbs observed
  have length : (Limbs.trim limbs).length ≤ limbs.length := by
    rw [Limbs.trim_length]
    exact Limbs.sigWords_le_length limbs
  cases trimmed : Limbs.trim limbs with
  | nil => simp only [fromWords, trimmed, At]
  | cons first rest =>
    cases rest with
    | nil => simp only [fromWords, trimmed, At]
    | cons second rest =>
      simp only [fromWords, trimmed, At]
      refine ⟨positive, aligned, ?_, ?_⟩
      · simp only [trimmed] at length
        omega
      · simpa only [trimmed] using retained

/-- Normalization preserves ownership without allocating or assuming canonical input. -/
theorem normalized_at (observe : Nat → Nat → Option Nat) (operand : NatOperand)
    (stored : operand.At observe) : operand.normalized.At observe := by
  cases operand with
  | small limb =>
    by_cases zero : limb = 0#64
    · simp [normalized, fromWords, words, Limbs.trim, zero, At]
    · simp [normalized, fromWords, words, Limbs.trim, zero, At]
  | large address limbs => exact fromWords_at observe address limbs stored

end SszNative.NatOperand
