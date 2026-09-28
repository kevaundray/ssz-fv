import SszLimbAdd

set_option autoImplicit false

/- Mathematical execution of the native row-major multiply/add/carry loops.
This is not an ISA execution proof. Words are emitted by the loops below;
no multiplication result is assumed or used to define the output limbs. -/
namespace SszNative.LimbMul

local notation "B" => (2 ^ 64 : Nat)

/-- The native widened product plus the existing destination word and carry. -/
def step (factor word old : BitVec 64) (carry : Nat) : BitVec 64 × Nat :=
  let product := factor.toNat * word.toNat + old.toNat + carry
  (BitVec.ofNat 64 product, product / B)

theorem step_value (factor word old : BitVec 64) (carry : Nat) :
    (step factor word old carry).1.toNat + B * (step factor word old carry).2 =
      factor.toNat * word.toNat + old.toNat + carry := by
  simpa only [step, BitVec.toNat_ofNat] using
    Nat.mod_add_div (factor.toNat * word.toNat + old.toNat + carry) B

theorem product_lt (factor word old : BitVec 64) (carry : Nat) (hc : carry < B) :
    factor.toNat * word.toNat + old.toNat + carry < 2 ^ 128 := by
  have hf := factor.isLt
  have hw := word.isLt
  have ho := old.isLt
  have hp := Nat.mul_le_mul (show factor.toNat ≤ B - 1 by omega)
    (show word.toNat ≤ B - 1 by omega)
  omega

theorem step_carry_lt (factor word old : BitVec 64) (carry : Nat) (hc : carry < B) :
    (step factor word old carry).2 < B := by
  have bound := product_lt factor word old carry hc
  change (factor.toNat * word.toNat + old.toNat + carry) / B < B
  omega

/-- Actual unsigned 128-bit multiply/add expression, before the casts. -/
def wideProduct (factor word old : BitVec 64) (carry : Nat) : BitVec 128 :=
  BitVec.ofNat 128 factor.toNat * BitVec.ofNat 128 word.toNat +
    BitVec.ofNat 128 old.toNat + BitVec.ofNat 128 carry

theorem wideProduct_toNat (factor word old : BitVec 64) (carry : Nat) (hc : carry < B) :
    (wideProduct factor word old carry).toNat =
      factor.toNat * word.toNat + old.toNat + carry := by
  have bound := product_lt factor word old carry hc
  have hf : factor.toNat < 2 ^ 128 := by have := factor.isLt; omega
  have hw : word.toNat < 2 ^ 128 := by have := word.isLt; omega
  have ho : old.toNat < 2 ^ 128 := by have := old.isLt; omega
  have hc128 : carry < 2 ^ 128 := by omega
  simp only [wideProduct, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt ho,
    Nat.mod_eq_of_lt hc128, Nat.mod_add_mod]
  exact Nat.mod_eq_of_lt bound

theorem step_eq_wide (factor word old : BitVec 64) (carry : Nat) (hc : carry < B) :
    step factor word old carry =
      ((wideProduct factor word old carry).setWidth 64,
        ((wideProduct factor word old carry) >>> 64).toNat) := by
  apply Prod.ext
  · apply BitVec.eq_of_toNat_eq
    simp [step, BitVec.toNat_setWidth, wideProduct_toNat factor word old carry hc]
  · simp [step, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      wideProduct_toNat factor word old carry hc]

/-- One row's low-to-high inner loop. Reads past a list return zero, exactly as
Nat::word does; `old` is the destination suffix at the row's starting index. -/
def inner : Nat → BitVec 64 → List (BitVec 64) → List (BitVec 64) → Nat →
    List (BitVec 64) × Nat
  | 0, _, _, _, carry => ([], carry)
  | width + 1, factor, words, old, carry =>
      let next := step factor (words.head?.getD 0) (old.head?.getD 0) carry
      let rest := inner width factor words.tail old.tail next.2
      (next.1 :: rest.1, rest.2)

theorem inner_indexed_succ (width index : Nat) (factor : BitVec 64)
    (words old : List (BitVec 64)) (carry : Nat) :
    inner (width + 1) factor (words.drop index) (old.drop index) carry =
      let next := step factor (words[index]?.getD 0) (old[index]?.getD 0) carry
      let rest := inner width factor (words.drop (index + 1))
        (old.drop (index + 1)) next.2
      (next.1 :: rest.1, rest.2) := by
  simp only [inner, List.head?_drop, List.tail_drop]

theorem inner_length (width : Nat) (factor : BitVec 64)
    (words old : List (BitVec 64)) (carry : Nat) :
    (inner width factor words old carry).1.length = width := by
  induction width generalizing words old carry with
  | zero => rfl
  | succ width ih => simp only [inner, List.length_cons, ih]

theorem inner_carry_lt (width : Nat) (factor : BitVec 64)
    (words old : List (BitVec 64)) (carry : Nat) (hc : carry < B) :
    (inner width factor words old carry).2 < B := by
  induction width generalizing words old carry with
  | zero => exact hc
  | succ width ih => exact ih words.tail old.tail _ (step_carry_lt _ _ _ carry hc)

private theorem value_head_tail (words : List (BitVec 64)) :
    Limbs.value words = (words.head?.getD 0).toNat + B * Limbs.value words.tail := by
  cases words <;> simp [Limbs.value]

/-- Inner-loop conservation, including unread input, destination, and carry.
It holds at every iteration, without a bound on the logical operand lengths. -/
theorem inner_value (width : Nat) (factor : BitVec 64)
    (words old : List (BitVec 64)) (carry : Nat) :
    Limbs.value (inner width factor words old carry).1 +
        B ^ width * (factor.toNat * Limbs.value (words.drop width) +
          Limbs.value (old.drop width) + (inner width factor words old carry).2) =
      factor.toNat * Limbs.value words + Limbs.value old + carry := by
  induction width generalizing words old carry with
  | zero => simp [inner, Limbs.value]
  | succ width ih =>
      let next := step factor (words.head?.getD 0) (old.head?.getD 0) carry
      let rest := inner width factor words.tail old.tail next.2
      have hrec := ih words.tail old.tail next.2
      have hstep := step_value factor (words.head?.getD 0) (old.head?.getD 0) carry
      change next.1.toNat + B * Limbs.value rest.1 +
          B ^ (width + 1) * (factor.toNat * Limbs.value (words.drop (width + 1)) +
            Limbs.value (old.drop (width + 1)) + rest.2) = _
      calc
        _ = next.1.toNat + B * (Limbs.value rest.1 +
            B ^ width * (factor.toNat * Limbs.value (words.tail.drop width) +
              Limbs.value (old.tail.drop width) + rest.2)) := by
          simp only [List.drop_tail, Nat.pow_succ B width, Nat.mul_add]
          ac_rfl
        _ = next.1.toNat + B *
            (factor.toNat * Limbs.value words.tail + Limbs.value old.tail + next.2) := by
          rw [hrec]
        _ = factor.toNat * Limbs.value words + Limbs.value old + carry := by
          rw [value_head_tail words, value_head_tail old]
          simp only [Nat.mul_add, Nat.mul_left_comm factor.toNat B]
          dsimp [next] at *
          omega

theorem inner_value_complete (width : Nat) (factor : BitVec 64)
    (words old : List (BitVec 64)) (carry : Nat)
    (hw : words.length ≤ width) (ho : old.length ≤ width) :
    Limbs.value (inner width factor words old carry).1 +
        B ^ width * (inner width factor words old carry).2 =
      factor.toNat * Limbs.value words + Limbs.value old + carry := by
  simpa only [List.drop_eq_nil_of_le hw, List.drop_eq_nil_of_le ho,
    Limbs.value, Nat.mul_zero, Nat.zero_add] using inner_value width factor words old carry

/-- Extra zero-extended word in mul_word consumes the final carry. -/
theorem inner_extra_carry_zero (width : Nat) (factor : BitVec 64)
    (words : List (BitVec 64)) (carry : Nat)
    (hw : words.length < width) (hc : carry < B) :
    (inner width factor words [] carry).2 = 0 := by
  induction width generalizing words carry with
  | zero => omega
  | succ width ih =>
      by_cases hz : width = 0
      · subst width
        have empty : words = [] := List.eq_nil_of_length_eq_zero (by omega)
        simp [inner, step, empty, Nat.div_eq_of_lt hc]
      · have smaller : words.tail.length < width := by
          simp only [List.length_tail]
          omega
        exact ih words.tail _ smaller (step_carry_lt _ _ _ carry hc)

/-- Appended destination words are unread when the inner width fits the prefix. -/
theorem inner_append (width : Nat) (factor : BitVec 64)
    (words old extra : List (BitVec 64)) (carry : Nat) (ho : width ≤ old.length) :
    inner width factor words (old ++ extra) carry = inner width factor words old carry := by
  induction width generalizing words old carry with
  | zero => rfl
  | succ width ih =>
      cases old with
      | nil => simp only [List.length_nil] at ho; omega
      | cons first rest =>
          simp only [List.cons_append, inner, List.head?_cons, Option.getD_some, List.tail_cons]
          rw [ih words.tail rest _ (by simp only [List.length_cons] at ho; omega)]

private theorem append_arithmetic (a b x p y : Nat) :
    a + b * (x + p * y) = a + b * x + (p * b) * y := by
  simp only [Nat.mul_add]
  ac_rfl

private theorem value_append (left right : List (BitVec 64)) :
    Limbs.value (left ++ right) = Limbs.value left + B ^ left.length * Limbs.value right := by
  induction left with
  | nil => simp [Limbs.value]
  | cons word words ih =>
      simp only [List.cons_append, Limbs.value, List.length_cons, ih, Nat.pow_succ]
      exact append_arithmetic word.toNat B (Limbs.value words) (B ^ words.length)
        (Limbs.value right)

/-- The active row window, including the explicit carry destination. -/
def row (factor : BitVec 64) (right old : List (BitVec 64)) : List (BitVec 64) :=
  let next := inner right.length factor right old 0
  next.1 ++ [BitVec.ofNat 64 next.2]

theorem row_length (factor : BitVec 64) (right old : List (BitVec 64)) :
    (row factor right old).length = right.length + 1 := by
  simp only [row, List.length_append, inner_length, List.length_cons, List.length_nil]

theorem row_value (factor : BitVec 64) (right old : List (BitVec 64))
    (ho : old.length = right.length) :
    Limbs.value (row factor right old) = factor.toNat * Limbs.value right + Limbs.value old := by
  have carry := inner_carry_lt right.length factor right old 0 (by decide)
  have total := inner_value_complete right.length factor right old 0 (by omega) (by omega)
  simpa only [row, value_append, inner_length, Limbs.value, Nat.mul_zero,
    Nat.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt carry] using total

/-- The outer loop visits left words low-to-high. Its first output word is no
longer touched by later rows; the rest becomes the next active window. -/
def rows : List (BitVec 64) → List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], _, old => old
  | factor :: left, right, old =>
      let updated := row factor right old
      updated.head?.getD 0 :: rows left right updated.tail

theorem rows_length (left right old : List (BitVec 64)) (ho : old.length = right.length) :
    (rows left right old).length = left.length + right.length := by
  induction left generalizing old with
  | nil => simpa only [rows, List.length_nil, Nat.zero_add] using ho
  | cons factor left ih =>
      have next : (row factor right old).tail.length = right.length := by
        simp only [List.length_tail, row_length, Nat.add_sub_cancel]
      simp only [rows, List.length_cons, ih _ next]
      omega

/-- Outer-loop invariant: the active destination is augmented by the product of
the remaining left suffix and the complete right operand. -/
theorem rows_value (left right old : List (BitVec 64)) (ho : old.length = right.length) :
    Limbs.value (rows left right old) = Limbs.value left * Limbs.value right + Limbs.value old := by
  induction left generalizing old with
  | nil => simp [rows, Limbs.value]
  | cons factor left ih =>
      have next : (row factor right old).tail.length = right.length := by
        simp only [List.length_tail, row_length, Nat.add_sub_cancel]
      have hr := row_value factor right old ho
      have hh := value_head_tail (row factor right old)
      simp only [rows, Limbs.value, ih _ next, Nat.mul_add, Nat.add_mul]
      calc
        _ = B * (Limbs.value left * Limbs.value right) + Limbs.value (row factor right old) := by
          rw [hh]
          ac_rfl
        _ = _ := by rw [hr]; ac_rfl

/-- Full-buffer write of one native row: inner writes, carry overwrite, then the
untouched suffix. Earlier rows never wrote the carry destination. -/
def nativeRow (factor : BitVec 64) (right buffer : List (BitVec 64)) : List (BitVec 64) :=
  row factor right buffer ++ buffer.drop (right.length + 1)

/-- Full-buffer row-major execution, with the already-final low prefix peeled off. -/
def nativeRows : List (BitVec 64) → List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], _, buffer => buffer
  | factor :: left, right, buffer =>
      let updated := nativeRow factor right buffer
      updated.head?.getD 0 :: nativeRows left right updated.tail

private theorem head_append (words rest : List (BitVec 64)) (positive : 0 < words.length) :
    (words ++ rest).head?.getD 0 = words.head?.getD 0 := by
  cases words with
  | nil => simp only [List.length_nil] at positive; omega
  | cons word words => rfl

private theorem tail_append (words rest : List (BitVec 64)) (positive : 0 < words.length) :
    (words ++ rest).tail = words.tail ++ rest := by
  cases words with
  | nil => simp only [List.length_nil] at positive; omega
  | cons word words => rfl

/-- The row invariant makes explicit every untouched high zero of the originally
zero-filled allocation. It justifies overwriting, rather than adding, the carry. -/
theorem nativeRows_eq_rows (left right old : List (BitVec 64))
    (ho : old.length = right.length) :
    nativeRows left right (old ++ List.replicate left.length 0) = rows left right old := by
  induction left generalizing old with
  | nil => simp [nativeRows, rows]
  | cons factor left ih =>
      have ir := inner_append right.length factor right old
        (List.replicate (factor :: left).length 0) 0 (by omega)
      have dropped : (old ++ List.replicate (factor :: left).length (0 : BitVec 64)).drop
          (right.length + 1) = List.replicate left.length 0 := by
        rw [List.drop_append]
        simp [ho, List.drop_eq_nil_of_le (show old.length ≤ right.length + 1 by omega)]
      have roweq : nativeRow factor right (old ++ List.replicate (factor :: left).length 0) =
          row factor right old ++ List.replicate left.length 0 := by
        simp only [nativeRow, row, ir, dropped]
      have positive : 0 < (row factor right old).length := by rw [row_length]; omega
      have next : (row factor right old).tail.length = right.length := by
        simp only [List.length_tail, row_length, Nat.add_sub_cancel]
      simp only [nativeRows, roweq, head_append _ _ positive, tail_append _ _ positive,
        ih _ next, rows]

def mul (left right : List (BitVec 64)) : List (BitVec 64) :=
  rows left right (List.replicate right.length 0)

private theorem replicate_add (m n : Nat) :
    List.replicate (m + n) (0 : BitVec 64) =
      List.replicate m 0 ++ List.replicate n 0 := by
  induction m with
  | zero => simp
  | succ m ih => simp only [Nat.succ_add, List.replicate_succ, List.cons_append, ih]

theorem mul_native (left right : List (BitVec 64)) :
    mul left right = nativeRows left right (List.replicate (left.length + right.length) 0) := by
  have same := nativeRows_eq_rows left right (List.replicate right.length 0) (by simp)
  rw [← replicate_add] at same
  simpa only [mul, Nat.add_comm right.length left.length] using same.symm

theorem mul_length (left right : List (BitVec 64)) :
    (mul left right).length = left.length + right.length :=
  rows_length left right _ (by simp)

theorem mul_value (left right : List (BitVec 64)) :
    Limbs.value (mul left right) = Limbs.value left * Limbs.value right := by
  have hz : Limbs.value (List.replicate right.length (0 : BitVec 64)) = 0 := by
    simpa only [List.nil_append, Limbs.value] using Limbs.value_append_zero [] right.length
  rw [mul, rows_value _ _ _ (by simp), hz, Nat.add_zero]

end SszNative.LimbMul
