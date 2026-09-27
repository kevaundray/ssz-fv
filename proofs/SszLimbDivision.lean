import SszLimbs

set_option autoImplicit false

namespace SszNative.LimbDivision

/-- The widened numerator formed from an incoming remainder and the next limb. -/
def current (remainder : Nat) (word : BitVec 64) : Nat :=
  remainder * 2 ^ 64 + word.toNat

/-- One division step. The quotient cast is exact when `remainder < divisor`. -/
def step (divisor : BitVec 64) (remainder : Nat) (word : BitVec 64) : BitVec 64 × Nat :=
  let numerator := current remainder word
  (BitVec.ofNat 64 (numerator / divisor.toNat), numerator % divisor.toNat)

/-- Long division of little-endian limbs, processing the high tail before its low head.
The output retains every input position; normalization is a separate operation. -/
def loop (divisor : BitVec 64) : List (BitVec 64) → Nat → List (BitVec 64) × Nat
  | [], remainder => ([], remainder)
  | word :: words, remainder =>
      let high := loop divisor words remainder
      let low := step divisor high.2 word
      (low.1 :: high.1, low.2)

/-- The full-width result of native `divide_words`, before output normalization. -/
def divideWords (divisor : BitVec 64) (words : List (BitVec 64)) : List (BitVec 64) × Nat :=
  loop divisor words 0

private theorem divisor_pos (divisor : BitVec 64) (hd : divisor ≠ 0) :
    0 < divisor.toNat := by
  have hn : divisor.toNat ≠ 0 := by
    intro hz
    apply hd
    apply BitVec.eq_of_toNat_eq
    simpa using hz
  omega

/-- The native 128-bit temporary cannot overflow under the loop invariant. -/
theorem current_lt (divisor word : BitVec 64) (remainder : Nat)
    (hr : remainder < divisor.toNat) : current remainder word < 2 ^ 128 := by
  have hd := divisor.isLt
  have hw := word.isLt
  unfold current
  omega

/-- The next quotient fits the native output word without truncation. -/
theorem quotient_lt (divisor word : BitVec 64) (remainder : Nat)
    (hr : remainder < divisor.toNat) : current remainder word / divisor.toNat < 2 ^ 64 := by
  apply Nat.div_lt_of_lt_mul
  have hw := word.isLt
  unfold current
  omega

theorem step_quotient (divisor word : BitVec 64) (remainder : Nat)
    (hr : remainder < divisor.toNat) :
    (step divisor remainder word).1.toNat = current remainder word / divisor.toNat := by
  simp only [step, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (quotient_lt divisor word remainder hr)]

/-- The remainder is not truncated, including in the executable step. -/
theorem step_remainder (divisor word : BitVec 64) (remainder : Nat) :
    (step divisor remainder word).2 = current remainder word % divisor.toNat := rfl

theorem step_remainder_lt (divisor word : BitVec 64) (remainder : Nat)
    (hd : divisor ≠ 0) : (step divisor remainder word).2 < divisor.toNat := by
  exact Nat.mod_lt _ (divisor_pos divisor hd)

/-- Conservation for one native limb update. -/
theorem step_conservation (divisor word : BitVec 64) (remainder : Nat)
    (hr : remainder < divisor.toNat) :
    current remainder word =
      divisor.toNat * (step divisor remainder word).1.toNat +
        (step divisor remainder word).2 := by
  rw [step_quotient divisor word remainder hr, step_remainder]
  exact (Nat.div_add_mod _ _).symm

/-- A low chunk is visited after the high chunk, retaining little-endian positions. -/
theorem loop_append (divisor : BitVec 64) (low high : List (BitVec 64)) (remainder : Nat) :
    loop divisor (low ++ high) remainder =
      let upper := loop divisor high remainder
      let lower := loop divisor low upper.2
      (lower.1 ++ upper.1, lower.2) := by
  induction low with
  | nil => simp [loop]
  | cons word words ih => simp [loop, ih]

/-- Each visited limb produces exactly one quotient limb, including high zeros. -/
theorem loop_length (divisor : BitVec 64) (words : List (BitVec 64)) (remainder : Nat) :
    (loop divisor words remainder).1.length = words.length := by
  induction words with
  | nil => rfl
  | cons word words ih => simpa only [loop, List.length_cons] using congrArg Nat.succ ih

theorem loop_remainder_lt (divisor : BitVec 64) (words : List (BitVec 64)) (remainder : Nat)
    (hd : divisor ≠ 0) (hr : remainder < divisor.toNat) :
    (loop divisor words remainder).2 < divisor.toNat := by
  cases words with
  | nil => exact hr
  | cons word words => exact step_remainder_lt divisor word (loop divisor words remainder).2 hd

/-- General incoming-remainder invariant for a high-to-low pass over a low chunk.
There is no bound on the represented input beyond the length of its limb list. -/
theorem loop_conservation (divisor : BitVec 64) (words : List (BitVec 64)) (remainder : Nat)
    (hd : divisor ≠ 0) (hr : remainder < divisor.toNat) :
    remainder * 2 ^ (64 * words.length) + Limbs.value words =
      divisor.toNat * Limbs.value (loop divisor words remainder).1 +
        (loop divisor words remainder).2 := by
  induction words with
  | nil => simp [loop, Limbs.value]
  | cons word words ih =>
      have hstep := step_conservation divisor word (loop divisor words remainder).2
        (loop_remainder_lt divisor words remainder hd hr)
      have hpow : 2 ^ (64 * (words.length + 1)) = 2 ^ 64 * 2 ^ (64 * words.length) := by
        rw [show 64 * (words.length + 1) = 64 + 64 * words.length by omega, Nat.pow_add]
      change remainder * 2 ^ (64 * (words.length + 1)) +
          (word.toNat + 2 ^ 64 * Limbs.value words) =
        divisor.toNat * ((step divisor (loop divisor words remainder).2 word).1.toNat +
          2 ^ 64 * Limbs.value (loop divisor words remainder).1) +
          (step divisor (loop divisor words remainder).2 word).2
      calc
        _ = 2 ^ 64 * (remainder * 2 ^ (64 * words.length) + Limbs.value words) +
              word.toNat := by rw [hpow, Nat.mul_add]; ac_rfl
        _ = 2 ^ 64 * (divisor.toNat * Limbs.value (loop divisor words remainder).1 +
              (loop divisor words remainder).2) + word.toNat := by rw [ih]
        _ = 2 ^ 64 * (divisor.toNat * Limbs.value (loop divisor words remainder).1) +
              current (loop divisor words remainder).2 word := by
                unfold current
                rw [Nat.mul_add]
                ac_rfl
        _ = _ := by rw [hstep, Nat.mul_add]; ac_rfl

/-- The unbounded natural-number quotient and remainder of a pass with an incoming remainder. -/
theorem loop_result (divisor : BitVec 64) (words : List (BitVec 64)) (remainder : Nat)
    (hd : divisor ≠ 0) (hr : remainder < divisor.toNat) :
    Limbs.value (loop divisor words remainder).1 =
        (remainder * 2 ^ (64 * words.length) + Limbs.value words) / divisor.toNat ∧
      (loop divisor words remainder).2 =
        (remainder * 2 ^ (64 * words.length) + Limbs.value words) % divisor.toNat := by
  rw [loop_conservation divisor words remainder hd hr]
  have hrem := loop_remainder_lt divisor words remainder hd hr
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ (divisor_pos divisor hd),
      Nat.div_eq_of_lt hrem, Nat.zero_add]
  · rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt hrem]
    exact (Nat.mod_eq_of_lt hrem).symm

theorem divideWords_length (divisor : BitVec 64) (words : List (BitVec 64)) :
    (divideWords divisor words).1.length = words.length := loop_length divisor words 0

theorem divideWords_remainder_lt (divisor : BitVec 64) (words : List (BitVec 64))
    (hd : divisor ≠ 0) : (divideWords divisor words).2 < divisor.toNat :=
  loop_remainder_lt divisor words 0 hd (divisor_pos divisor hd)

theorem divideWords_conservation (divisor : BitVec 64) (words : List (BitVec 64))
    (hd : divisor ≠ 0) :
    Limbs.value words = divisor.toNat * Limbs.value (divideWords divisor words).1 +
      (divideWords divisor words).2 := by
  simpa only [divideWords, Nat.zero_mul, Nat.zero_add] using
    loop_conservation divisor words 0 hd (divisor_pos divisor hd)

theorem divideWords_result (divisor : BitVec 64) (words : List (BitVec 64))
    (hd : divisor ≠ 0) :
    Limbs.value (divideWords divisor words).1 = Limbs.value words / divisor.toNat ∧
      (divideWords divisor words).2 = Limbs.value words % divisor.toNat := by
  simpa only [divideWords, Nat.zero_mul, Nat.zero_add] using
    loop_result divisor words 0 hd (divisor_pos divisor hd)

/-- The exact native widened shift/OR expression, with the remainder still in a u128. -/
def nativeCurrent (remainder : BitVec 128) (word : BitVec 64) : BitVec 128 :=
  (remainder <<< 64) ||| word.setWidth 128

/-- The quotient truncation and widened remainder update in one native loop iteration. -/
def nativeStep (divisor : BitVec 64) (remainder : BitVec 128) (word : BitVec 64) :
    BitVec 64 × BitVec 128 :=
  let numerator := nativeCurrent remainder word
  ((numerator / divisor.setWidth 128).setWidth 64, numerator % divisor.setWidth 128)

theorem nativeCurrent_toNat (divisor word : BitVec 64) (remainder : BitVec 128)
    (hr : remainder.toNat < divisor.toNat) :
    (nativeCurrent remainder word).toNat = current remainder.toNat word := by
  have hcurrent := current_lt divisor word remainder.toNat hr
  have hshift : remainder.toNat <<< 64 < 2 ^ 128 := by
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.le_add_right _ word.toNat) hcurrent
  simp only [nativeCurrent, BitVec.toNat_or, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth_of_le (show 64 ≤ 128 by decide), Nat.mod_eq_of_lt hshift]
  simpa only [Nat.shiftLeft_eq, current] using
    (Nat.shiftLeft_add_eq_or_of_lt word.isLt remainder.toNat).symm

/-- The real native word operation agrees with the executable arithmetic step. -/
theorem nativeStep_eq (divisor word : BitVec 64) (remainder : BitVec 128)
    (hr : remainder.toNat < divisor.toNat) :
    (nativeStep divisor remainder word).1 = (step divisor remainder.toNat word).1 ∧
      (nativeStep divisor remainder word).2.toNat = (step divisor remainder.toNat word).2 := by
  have hd : (divisor.setWidth 128).toNat = divisor.toNat :=
    BitVec.toNat_setWidth_of_le (show 64 ≤ 128 by decide)
  constructor
  · apply BitVec.eq_of_toNat_eq
    calc
      (nativeStep divisor remainder word).1.toNat =
          ((nativeCurrent remainder word).toNat / (divisor.setWidth 128).toNat) % 2 ^ 64 := by
            simp only [nativeStep, BitVec.toNat_setWidth, BitVec.toNat_udiv]
      _ = (current remainder.toNat word / divisor.toNat) % 2 ^ 64 := by
        rw [nativeCurrent_toNat divisor word remainder hr, hd]
      _ = (step divisor remainder.toNat word).1.toNat := by
        simp only [step, BitVec.toNat_ofNat]
  · calc
      (nativeStep divisor remainder word).2.toNat =
          (nativeCurrent remainder word).toNat % (divisor.setWidth 128).toNat := by
            simp only [nativeStep, BitVec.toNat_umod]
      _ = (step divisor remainder.toNat word).2 := by
        rw [nativeCurrent_toNat divisor word remainder hr, hd, step_remainder]

/-- The quotient written by the native operation is the full mathematical quotient. -/
theorem nativeStep_quotient (divisor word : BitVec 64) (remainder : BitVec 128)
    (hr : remainder.toNat < divisor.toNat) :
    (nativeStep divisor remainder word).1.toNat = current remainder.toNat word / divisor.toNat := by
  rw [(nativeStep_eq divisor word remainder hr).1, step_quotient divisor word remainder.toNat hr]

/-- The native widened remainder retains the invariant for the next iteration. -/
theorem nativeStep_remainder_lt (divisor word : BitVec 64) (remainder : BitVec 128)
    (hd : divisor ≠ 0) (hr : remainder.toNat < divisor.toNat) :
    (nativeStep divisor remainder word).2.toNat < divisor.toNat := by
  rw [(nativeStep_eq divisor word remainder hr).2]
  exact step_remainder_lt divisor word remainder.toNat hd

/-- Exact reconstruction from the native quotient word and widened remainder. -/
theorem nativeStep_conservation (divisor word : BitVec 64) (remainder : BitVec 128)
    (hr : remainder.toNat < divisor.toNat) :
    current remainder.toNat word =
      divisor.toNat * (nativeStep divisor remainder word).1.toNat +
        (nativeStep divisor remainder word).2.toNat := by
  rw [(nativeStep_eq divisor word remainder hr).1, (nativeStep_eq divisor word remainder hr).2]
  exact step_conservation divisor word remainder.toNat hr

/-- The final native u128-to-u64 remainder cast loses no information. -/
theorem remainder_cast_exact (divisor : BitVec 64) (remainder : BitVec 128)
    (hr : remainder.toNat < divisor.toNat) :
    (remainder.setWidth 64).toNat = remainder.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hr divisor.isLt)]

end SszNative.LimbDivision
