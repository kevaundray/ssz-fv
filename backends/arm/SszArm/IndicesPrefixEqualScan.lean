import SszIndicesCore

namespace SszArm.Indices.PrefixEqual

open SszNative (NatOperand)
open SszNative.Indices

/-- The machine increments its word position. The accepted operational model's
`allWords` checks the same pure observations in decreasing order. -/
def scan (predicate : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | position, remaining + 1 => predicate position && scan predicate (position + 1) remaining

theorem scan_iff (predicate : Nat → Bool) (position remaining : Nat) :
    scan predicate position remaining = true ↔
      ∀ i, position ≤ i → i < position + remaining → predicate i = true := by
  induction remaining generalizing position with
  | zero => simp [scan]
  | succ remaining ih =>
      rw [scan, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨first, rest⟩ i lower upper
        by_cases same : i = position
        · simpa only [same] using first
        · exact rest i (by omega) (by omega)
      · intro every
        exact ⟨every position (by omega) (by omega),
          fun i lower upper => every i (by omega) (by omega)⟩

theorem scan_allWords (predicate : Nat → Bool) (count : Nat) :
    scan predicate 0 count = allWords predicate count := by
  apply Bool.eq_iff_iff.mpr
  rw [scan_iff, allWords_iff]
  simp

/-- Word-count conversion is the actual truncating usize cast, not a new
logical bound on the supplied natural or either u128 shift. -/
def comparisonCount (left : NatOperand) (shift : Nat) : Nat :=
  let bits := bitLength left - shift
  (bits / 64 + if bits % 64 = 0 then 0 else 1) % 2^64

def comparisonWord (left : NatOperand) (leftShift : Nat) (flip : Bool)
    (right : NatOperand) (rightShift position : Nat) : Bool :=
  (shiftedWord left leftShift position ^^^ (if flip && position == 0 then 1 else 0)) ==
    shiftedWord right rightShift position

theorem prefixEqual_scan (left : NatOperand) (leftShift : Nat) (flip : Bool)
    (right : NatOperand) (rightShift : Nat) :
    prefixEqual left leftShift flip right rightShift =
      if bitLength left - leftShift != bitLength right - rightShift then false else
        scan (comparisonWord left leftShift flip right rightShift) 0
          (comparisonCount left leftShift) := by
  rw [scan_allWords]
  rfl

/-- No numeric xor identity is used at zero width: even with flip set, the
native comparator performs no word observation and returns true. -/
theorem exhausted_prefixes (left : NatOperand) (leftShift : Nat) (flip : Bool)
    (right : NatOperand) (rightShift : Nat)
    (leftEmpty : bitLength left ≤ leftShift) (rightEmpty : bitLength right ≤ rightShift) :
    prefixEqual left leftShift flip right rightShift = true := by
  simp [prefixEqual, Nat.sub_eq_zero_of_le leftEmpty, Nat.sub_eq_zero_of_le rightEmpty, allWords]

/-- The successful prefix accumulated by an ascending execution extends by
exactly the word that was just compared. -/
theorem scanned_succ (predicate : Nat → Bool) (position : Nat)
    (earlier : ∀ i, i < position → predicate i = true) (current : predicate position = true) :
    ∀ i, i < position + 1 → predicate i = true := by
  intro i bound
  by_cases same : i = position
  · simpa only [same] using current
  · exact earlier i (by omega)

theorem mismatch (predicate : Nat → Bool) (count position : Nat)
    (inside : position < count) (different : predicate position = false) :
    scan predicate 0 count = false := by
  cases observed : scan predicate 0 count with
  | false => rfl
  | true =>
      have same := (scan_iff predicate 0 count).mp observed position (by omega) (by omega)
      simp only [different] at same

end SszArm.Indices.PrefixEqual
