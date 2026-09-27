import SszLimbs

set_option autoImplicit false

/- Algorithm models of native/src/nat.rs:significant_words and compare.
The countdown and descending scan operate on zero-extended limb observations.
These are representation proofs, not pointer-access or ISA refinement. -/
namespace SszNative.Limbs

local notation "B" => (2 ^ 64)

/-- Remove redundant high zero limbs without changing the represented number. -/
def trim : List (BitVec 64) → List (BitVec 64)
  | [] => []
  | w :: ws =>
    let rest := trim ws
    if rest = [] then if w = 0 then [] else [w] else w :: rest

def Canonical : List (BitVec 64) → Prop
  | [] => True
  | [w] => w ≠ 0
  | _ :: ws => Canonical ws

theorem trim_value (ws : List (BitVec 64)) : value (trim ws) = value ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    by_cases ht : trim ws = []
    · have hz : value ws = 0 := by rw [← ih, ht]; rfl
      by_cases hw : w = 0 <;> simp_all [trim, value]
    · simp only [trim, ht, ↓reduceIte, value, ih]

theorem trim_canonical (ws : List (BitVec 64)) : Canonical (trim ws) := by
  induction ws with
  | nil => trivial
  | cons w ws ih =>
    cases ht : trim ws with
    | nil => by_cases hw : w = 0 <;> simp_all [trim, Canonical]
    | cons t ts => simpa [trim, ht, Canonical] using ih

/-- A nonempty canonical list has a nonzero highest radix digit. -/
theorem canonical_ge_pow : ∀ ws, Canonical ws → ws ≠ [] →
    2 ^ (64 * (ws.length - 1)) ≤ value ws
  | [], _, hne => False.elim (hne rfl)
  | [w], h, _ => by
    have nonzero : w.toNat ≠ 0 := by
      intro hz
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa using hz
    have positive : 1 ≤ w.toNat := by omega
    simpa [value] using positive
  | x :: y :: ys, h, _ => by
    have ih := canonical_ge_pow (y :: ys) h (by simp)
    have hp : 2 ^ (64 * ((x :: y :: ys).length - 1)) =
        B * 2 ^ (64 * ((y :: ys).length - 1)) := by
      rw [← Nat.pow_add]
      congr 1
      simp only [List.length_cons]
      omega
    calc
      _ = B * 2 ^ (64 * ((y :: ys).length - 1)) := hp
      _ ≤ B * value (y :: ys) := Nat.mul_le_mul_left _ ih
      _ ≤ value (x :: y :: ys) := by
        change B * value (y :: ys) ≤ x.toNat + B * value (y :: ys)
        omega

theorem canonical_pos (ws : List (BitVec 64)) (h : Canonical ws) (hne : ws ≠ []) :
    0 < value ws :=
  Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (canonical_ge_pow ws h hne)

theorem trim_eq_nil_iff_value_zero (ws : List (BitVec 64)) :
    trim ws = [] ↔ value ws = 0 := by
  constructor
  · intro h
    rw [← trim_value ws, h]
    rfl
  · intro hz
    by_cases hn : trim ws = []
    · exact hn
    · have positive := canonical_pos (trim ws) (trim_canonical ws) hn
      rw [trim_value, hz] at positive
      omega

/-- Literal descending-index countdown used by native significant_words. -/
def significantCount (ws : List (BitVec 64)) : Nat → Nat
  | 0 => 0
  | n + 1 => if ws[n]?.getD 0 = 0 then significantCount ws n else n + 1

def sigWords (ws : List (BitVec 64)) : Nat := significantCount ws ws.length

theorem significantCount_le (ws : List (BitVec 64)) (n : Nat) :
    significantCount ws n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => simp only [significantCount]; split <;> omega

private theorem significantCount_cons (w : BitVec 64) (ws : List (BitVec 64)) (n : Nat) :
    significantCount (w :: ws) (n + 1) =
      if significantCount ws n = 0 then (if w = 0 then 0 else 1)
      else significantCount ws n + 1 := by
  induction n with
  | zero => simp [significantCount]
  | succ n ih =>
    rw [significantCount]
    change (if ws[n]?.getD 0 = 0 then significantCount (w :: ws) (n + 1)
      else n + 1 + 1) = _
    rw [ih]
    clear ih
    by_cases hz : ws[n]?.getD 0 = 0 <;> simp_all [significantCount]

private theorem sigWords_cons (w : BitVec 64) (ws : List (BitVec 64)) :
    sigWords (w :: ws) = if sigWords ws = 0 then (if w = 0 then 0 else 1)
      else sigWords ws + 1 := by
  exact significantCount_cons w ws ws.length

theorem sigWords_le_length (ws : List (BitVec 64)) : sigWords ws ≤ ws.length :=
  significantCount_le ws ws.length

/-- Trimming retains exactly the prefix selected by the native countdown. -/
theorem trim_eq_take (ws : List (BitVec 64)) : trim ws = ws.take (sigWords ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [sigWords_cons]
    by_cases h : sigWords ws = 0
    · have ht : trim ws = [] := by simpa [h] using ih
      by_cases hw : w = 0 <;> simp_all [trim]
    · have ht : trim ws ≠ [] := by
        intro hn
        have len : (ws.take (sigWords ws)).length = sigWords ws := by
          rw [List.length_take, Nat.min_eq_left (sigWords_le_length ws)]
        rw [← ih, hn] at len
        simp at len
        omega
      simp only [trim, ht, h, ↓reduceIte, List.take_succ_cons]
      rw [ih]

theorem trim_length (ws : List (BitVec 64)) : (trim ws).length = sigWords ws := by
  rw [trim_eq_take, List.length_take, Nat.min_eq_left (sigWords_le_length ws)]

private theorem compare_radix_lt {r a b x y : Nat} (ha : a < r) (hxy : x < y) :
    Ordering.lt = compare (a + r * x) (b + r * y) := by
  apply (Nat.compare_eq_lt.mpr ?_).symm
  calc
    a + r * x < r + r * x := Nat.add_lt_add_right ha _
    _ = r * (x + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ r * y := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hxy)
    _ ≤ b + r * y := by omega

private theorem compare_radix_gt {r a b x y : Nat} (hb : b < r) (hyx : y < x) :
    Ordering.gt = compare (a + r * x) (b + r * y) := by
  have h := compare_radix_lt (r := r) (a := b) (b := a) (x := y) (y := x) hb hyx
  exact (Nat.compare_eq_gt.mpr (Nat.compare_eq_lt.mp h.symm)).symm

private theorem compare_add_same (a b c : Nat) :
    compare (a + c) (b + c) = compare a b := by
  simp [Nat.compare_eq_ite_lt]

/-- Descending-index comparison, stopping at the highest differing limb. -/
def scanDesc (xs ys : List (BitVec 64)) : Nat → Ordering
  | 0 => .eq
  | n + 1 =>
    match compare (xs[n]?.getD 0).toNat (ys[n]?.getD 0).toNat with
    | .eq => scanDesc xs ys n
    | ord => ord

private theorem value_take_succ : ∀ (ws : List (BitVec 64)) (n : Nat),
    value (ws.take (n + 1)) = value (ws.take n) +
      2 ^ (64 * n) * (ws[n]?.getD 0).toNat
  | [], n => by simp [value]
  | w :: ws, 0 => by simp [value]
  | w :: ws, n + 1 => by
    have ih := value_take_succ ws n
    have hp : 2 ^ (64 * (n + 1)) = B * 2 ^ (64 * n) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hp]
    simp [value, ih, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

private theorem value_take_lt (ws : List (BitVec 64)) (n : Nat) :
    value (ws.take n) < 2 ^ (64 * n) := by
  apply Nat.lt_of_lt_of_le (value_lt (ws.take n))
  apply Nat.pow_le_pow_right (by decide)
  simp only [List.length_take]
  omega

/-- The scan compares the represented prefixes, even with redundant high zeros. -/
theorem scanDesc_value (xs ys : List (BitVec 64)) (n : Nat) :
    scanDesc xs ys n = compare (value (xs.take n)) (value (ys.take n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [scanDesc, value_take_succ, value_take_succ]
    cases hc : compare (xs[n]?.getD 0).toNat (ys[n]?.getD 0).toNat with
    | eq =>
      have equal := Nat.compare_eq_eq.mp hc
      simpa only [equal, compare_add_same] using ih
    | lt =>
      exact compare_radix_lt (b := value (ys.take n))
        (value_take_lt xs n) (Nat.compare_eq_lt.mp hc)
    | gt =>
      exact compare_radix_gt (a := value (xs.take n))
        (value_take_lt ys n) (Nat.compare_eq_gt.mp hc)

theorem scanDesc_take (xs ys : List (BitVec 64)) (n : Nat) :
    scanDesc xs ys n = scanDesc (xs.take n) (ys.take n) n := by
  simp only [scanDesc_value, List.take_take, Nat.min_self]

theorem scanDesc_correct (xs ys : List (BitVec 64)) (n : Nat)
    (hx : xs.length = n) (hy : ys.length = n) :
    scanDesc xs ys n = compare (value xs) (value ys) := by
  rw [scanDesc_value, List.take_of_length_le (by omega : xs.length ≤ n),
    List.take_of_length_le (by omega : ys.length ≤ n)]

theorem canonical_length_lt {xs ys : List (BitVec 64)}
    (hy : Canonical ys) (lengths : xs.length < ys.length) : value xs < value ys := by
  have nonempty : ys ≠ [] := by intro h; subst ys; simp at lengths
  have bound := canonical_ge_pow ys hy nonempty
  have powers : 2 ^ (64 * xs.length) ≤ 2 ^ (64 * (ys.length - 1)) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.lt_of_lt_of_le (value_lt xs) (Nat.le_trans powers bound)

/-- Native length-first comparison, with an original-input scan on equal lengths. -/
def nativeCmp (xs ys : List (BitVec 64)) : Ordering :=
  let left := sigWords xs
  let right := sigWords ys
  match compare left right with
  | .eq => scanDesc xs ys left
  | ord => ord

/-- Arbitrary limb counts and arbitrarily many high zeros preserve natural ordering. -/
theorem nativeCmp_correct (xs ys : List (BitVec 64)) :
    nativeCmp xs ys = compare (value xs) (value ys) := by
  unfold nativeCmp
  dsimp only
  cases hc : compare (sigWords xs) (sigWords ys) with
  | eq =>
    have lengths := Nat.compare_eq_eq.mp hc
    rw [scanDesc_value, ← trim_eq_take xs, lengths, ← trim_eq_take ys,
      trim_value, trim_value]
  | lt =>
    have lengths : (trim xs).length < (trim ys).length := by
      rw [trim_length, trim_length]
      exact Nat.compare_eq_lt.mp hc
    have less := canonical_length_lt (trim_canonical ys) lengths
    rw [trim_value, trim_value] at less
    exact (Nat.compare_eq_lt.mpr less).symm
  | gt =>
    have lengths : (trim ys).length < (trim xs).length := by
      rw [trim_length, trim_length]
      exact Nat.compare_eq_gt.mp hc
    have less := canonical_length_lt (trim_canonical xs) lengths
    rw [trim_value, trim_value] at less
    exact (Nat.compare_eq_gt.mpr less).symm

end SszNative.Limbs
