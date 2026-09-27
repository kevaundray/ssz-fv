import SszLimbs

set_option autoImplicit false

/- Executable arithmetic of native/src/nat.rs:Nat::add. The output retains
all allocated words, including the extra carry word. Normalization, allocation,
and physical operand bounds are deliberately left to the caller. -/
namespace SszNative.LimbAdd

local notation "B" => (2 ^ 64 : Nat)

/-- One zero-extended word addition: the low word and the outgoing carry. -/
def step (left right : BitVec 64) (carry : Nat) : BitVec 64 × Nat :=
  let sum := left.toNat + right.toNat + carry
  (BitVec.ofNat 64 sum, sum / B)

/-- The low word is the wrapped sum, without a precondition on the carry. -/
theorem step_low (left right : BitVec 64) (carry : Nat) :
    (step left right carry).1.toNat = (left.toNat + right.toNat + carry) % B := by
  simp [step, BitVec.toNat_ofNat]

/-- The low/high decomposition is exact, even for an arbitrary natural carry. -/
theorem step_value (left right : BitVec 64) (carry : Nat) :
    (step left right carry).1.toNat + B * (step left right carry).2 =
      left.toNat + right.toNat + carry := by
  simpa only [step, BitVec.toNat_ofNat] using
    Nat.mod_add_div (left.toNat + right.toNat + carry) B

/-- A valid incoming carry makes the mathematical sum fit in 65 bits. -/
theorem step_sum_lt (left right : BitVec 64) (carry : Nat) (hc : carry ≤ 1) :
    left.toNat + right.toNat + carry < 2 ^ 65 := by
  have hl := left.isLt
  have hr := right.isLt
  omega

/-- Carry is always zero or one throughout a native addition. -/
theorem step_carry_le (left right : BitVec 64) (carry : Nat) (hc : carry ≤ 1) :
    (step left right carry).2 ≤ 1 := by
  have hs := step_sum_lt left right carry hc
  change (left.toNat + right.toNat + carry) / B ≤ 1
  omega

/-- The native `u128` expression before the cast and the right shift. -/
def wideSum (left right : BitVec 64) (carry : Nat) : BitVec 128 :=
  BitVec.ofNat 128 left.toNat + BitVec.ofNat 128 right.toNat + BitVec.ofNat 128 carry

/-- The native widened addition does not wrap for a valid carry. -/
theorem wideSum_toNat (left right : BitVec 64) (carry : Nat) (hc : carry ≤ 1) :
    (wideSum left right carry).toNat = left.toNat + right.toNat + carry := by
  have hs := step_sum_lt left right carry hc
  simp only [wideSum, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_add_mod, Nat.add_mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- The executable step agrees with the native low-64 cast and high-64 shift. -/
theorem step_eq_wide (left right : BitVec 64) (carry : Nat) (hc : carry ≤ 1) :
    step left right carry =
      ((wideSum left right carry).setWidth 64,
        ((wideSum left right carry) >>> 64).toNat) := by
  apply Prod.ext
  · apply BitVec.eq_of_toNat_eq
    simp [step, BitVec.toNat_setWidth, wideSum_toNat left right carry hc]
  · simp [step, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      wideSum_toNat left right carry hc]

/-- Run exactly `width` low-to-high word steps, reading zero past either input.
The pair records every written word and the carry after the final write. -/
def loop : Nat → List (BitVec 64) → List (BitVec 64) → Nat → List (BitVec 64) × Nat
  | 0, _, _, carry => ([], carry)
  | width + 1, left, right, carry =>
      let next := step (left.head?.getD 0) (right.head?.getD 0) carry
      let rest := loop width left.tail right.tail next.2
      (next.1 :: rest.1, rest.2)

/-- The recurrence with native indexed observations and the next unread index. -/
theorem loop_indexed_succ (width index : Nat) (left right : List (BitVec 64))
    (carry : Nat) :
    loop (width + 1) (left.drop index) (right.drop index) carry =
      let next := step (left[index]?.getD 0) (right[index]?.getD 0) carry
      let rest := loop width (left.drop (index + 1)) (right.drop (index + 1)) next.2
      (next.1 :: rest.1, rest.2) := by
  simp only [loop, List.head?_drop, List.tail_drop]

/-- Exactly one limb is emitted for every requested native scratch write. -/
theorem loop_length (width : Nat) (left right : List (BitVec 64)) (carry : Nat) :
    (loop width left right carry).1.length = width := by
  induction width generalizing left right carry with
  | zero => rfl
  | succ width ih => simp only [loop, List.length_cons, ih]

/-- Every iteration preserves the one-bit carry bound. -/
theorem loop_carry_le (width : Nat) (left right : List (BitVec 64))
    (carry : Nat) (hc : carry ≤ 1) :
    (loop width left right carry).2 ≤ 1 := by
  induction width generalizing left right carry with
  | zero => exact hc
  | succ width ih =>
      exact ih left.tail right.tail _ (step_carry_le _ _ carry hc)

private theorem value_head_tail (words : List (BitVec 64)) :
    Limbs.value words = (words.head?.getD 0).toNat + B * Limbs.value words.tail := by
  cases words <;> simp [Limbs.value]

/-- Conservation across any prefix of the loop. The still-unread high words and
outgoing carry account for everything not yet written; no size bound is assumed. -/
theorem loop_value (width : Nat) (left right : List (BitVec 64)) (carry : Nat) :
    Limbs.value (loop width left right carry).1 +
        B ^ width * (Limbs.value (left.drop width) + Limbs.value (right.drop width) +
          (loop width left right carry).2) =
      Limbs.value left + Limbs.value right + carry := by
  induction width generalizing left right carry with
  | zero => simp [loop, Limbs.value]
  | succ width ih =>
      let next := step (left.head?.getD 0) (right.head?.getD 0) carry
      let rest := loop width left.tail right.tail next.2
      have hrec := ih left.tail right.tail next.2
      have hstep := step_value (left.head?.getD 0) (right.head?.getD 0) carry
      change next.1.toNat + B * Limbs.value rest.1 +
          B ^ (width + 1) * (Limbs.value (left.drop (width + 1)) +
            Limbs.value (right.drop (width + 1)) + rest.2) = _
      calc
        _ = next.1.toNat + B * (Limbs.value rest.1 +
            B ^ width * (Limbs.value (left.tail.drop width) +
              Limbs.value (right.tail.drop width) + rest.2)) := by
          simp only [List.drop_tail, Nat.pow_succ B width, Nat.mul_add]
          ac_rfl
        _ = next.1.toNat + B * (Limbs.value left.tail + Limbs.value right.tail + next.2) := by
          rw [hrec]
        _ = Limbs.value left + Limbs.value right + carry := by
          rw [value_head_tail left, value_head_tail right]
          dsimp [next] at *
          simp only [Nat.mul_add]
          omega

/-- Once both inputs have been consumed, only the outgoing carry is omitted. -/
theorem loop_value_complete (width : Nat) (left right : List (BitVec 64)) (carry : Nat)
    (hl : left.length ≤ width) (hr : right.length ≤ width) :
    Limbs.value (loop width left right carry).1 + B ^ width * (loop width left right carry).2 =
      Limbs.value left + Limbs.value right + carry := by
  simpa only [List.drop_eq_nil_of_le hl, List.drop_eq_nil_of_le hr,
    Limbs.value, Nat.zero_add] using loop_value width left right carry

/-- The extra zero-extended word consumes the last possible carry. -/
theorem loop_carry_eq_zero (width : Nat) (left right : List (BitVec 64)) (carry : Nat)
    (hl : left.length < width) (hr : right.length < width) (hc : carry ≤ 1) :
    (loop width left right carry).2 = 0 := by
  induction width generalizing left right carry with
  | zero => omega
  | succ width ih =>
      by_cases hw : width = 0
      · subst width
        have hleft : left = [] := List.eq_nil_of_length_eq_zero (by omega)
        have hright : right = [] := List.eq_nil_of_length_eq_zero (by omega)
        have hsmall : carry < B := by omega
        simp [loop, step, hleft, hright, Nat.div_eq_of_lt hsmall]
      · have hleft : left.tail.length < width := by
          simp only [List.length_tail]
          omega
        have hright : right.tail.length < width := by
          simp only [List.length_tail]
          omega
        exact ih left.tail right.tail _ hleft hright (step_carry_le _ _ carry hc)

/-- Full allocating-path output, before normalization. Leading zero inputs are
permitted; callers trim first when they need exactly native significant width. -/
def add (left right : List (BitVec 64)) : List (BitVec 64) :=
  (loop (max left.length right.length + 1) left right 0).1

/-- The output includes the extra word even when its value is zero. -/
theorem add_length (left right : List (BitVec 64)) :
    (add left right).length = max left.length right.length + 1 :=
  loop_length _ left right 0

/-- The complete executable carry algorithm adds the unbounded limb values. -/
theorem add_value (left right : List (BitVec 64)) :
    Limbs.value (add left right) = Limbs.value left + Limbs.value right := by
  have hl : left.length < max left.length right.length + 1 := by omega
  have hr : right.length < max left.length right.length + 1 := by omega
  have hz := loop_carry_eq_zero _ left right 0 hl hr (by omega)
  have hv := loop_value_complete _ left right 0 (Nat.le_of_lt hl) (Nat.le_of_lt hr)
  simpa only [add, hz, Nat.mul_zero, Nat.add_zero] using hv

end SszNative.LimbAdd
