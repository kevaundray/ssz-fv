import Std

set_option autoImplicit false

namespace SszNative.Division

/-- One restoring-division step. -/
def step (d bit q r : Nat) : Nat × Nat :=
  let t := 2 * r + bit
  if d ≤ t then (2 * q + 1, t - d) else (2 * q, t)

/-- Process the low `k` bits of `n`, most significant first. -/
def loop (d n : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, q, r => (q, r)
  | k + 1, q, r =>
      let p := step d ((n / 2 ^ k) % 2) q r
      loop d n k p.1 p.2

/-- The step satisfies the restoring-division conservation law. -/
theorem step_conservation (d bit q r : Nat) :
    (step d bit q r).1 * d + (step d bit q r).2 = 2 * (q * d + r) + bit := by
  by_cases h : d ≤ 2 * r + bit
  · simp only [step, h, ↓reduceIte, Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_assoc]
    omega
  · simp only [step, h, ↓reduceIte, Nat.mul_add, Nat.mul_assoc]
    omega

/-- The step keeps the remainder below the divisor. -/
theorem step_remainder_lt (d bit q r : Nat) (hr : r < d) (_hd : 0 < d)
    (hbit : bit < 2) : (step d bit q r).2 < d := by
  unfold step
  by_cases h : d ≤ 2 * r + bit
  · simp [h]
    omega
  · simp [h]
    exact Nat.lt_of_not_ge h

/-- The loop keeps the remainder below `d`. -/
theorem loop_remainder_lt (d n k q r : Nat) (hr : r < d) (hd : 0 < d) :
    (loop d n k q r).2 < d := by
  induction k generalizing q r with
  | zero =>
      simp [loop, hr]
  | succ k ih =>
      have hbit : ((n / 2 ^ k) % 2) < 2 := Nat.mod_lt _ (by decide)
      let p := step d ((n / 2 ^ k) % 2) q r
      have hp : p.2 < d := by
        simpa [p] using step_remainder_lt d ((n / 2 ^ k) % 2) q r hr hd hbit
      simpa [loop, p] using ih p.1 p.2 hp
/-- The loop preserves the numeric conservation equation. -/
theorem loop_conservation (d n k q r : Nat) :
    (loop d n k q r).1 * d + (loop d n k q r).2 = (q * d + r) * 2 ^ k + n % 2 ^ k := by
  induction k generalizing q r with
  | zero => simp [loop, Nat.mod_one]
  | succ k ih =>
      simp only [loop]
      rw [ih, step_conservation, Nat.mod_pow_succ, Nat.pow_succ, Nat.add_mul]
      ac_rfl

private theorem div_mod_of_mul_add (d q r value : Nat) (hd : 0 < d) (hr : r < d)
    (h : q * d + r = value) : value / d = q ∧ value % d = r := by
  subst value
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right r q hd, Nat.div_eq_of_lt hr, Nat.zero_add]
  · exact Nat.mul_add_mod_of_lt hr

/-- General loop result, including a nonzero quotient prefix. -/
theorem loop_result (d n k q r : Nat) (hr : r < d) (hd : 0 < d) :
    loop d n k q r =
      (((q * d + r) * 2 ^ k + n % 2 ^ k) / d,
       ((q * d + r) * 2 ^ k + n % 2 ^ k) % d) := by
  have hpair := div_mod_of_mul_add d (loop d n k q r).1 (loop d n k q r).2
    ((q * d + r) * 2 ^ k + n % 2 ^ k) hd
    (loop_remainder_lt d n k q r hr hd) (loop_conservation d n k q r)
  exact Prod.ext hpair.1.symm hpair.2.symm

/-- Bits above the remaining input width do not affect execution. -/
theorem loop_mod_input (d n k q r : Nat) (hr : r < d) (hd : 0 < d) :
    loop d (n % 2 ^ k) k q r = loop d n k q r := by
  rw [loop_result d (n % 2 ^ k) k q r hr hd,
    loop_result d n k q r hr hd, Nat.mod_mod]

/-- The loop computes the quotient of `high * 2^k + n` when `n < 2^k`. -/
theorem loop_quotient (d n k high : Nat) (hn : n < 2 ^ k) (hhigh : high < d)
    (hd : 0 < d) :
    (loop d n k 0 high).1 = (high * 2 ^ k + n) / d := by
  let out := loop d n k 0 high
  have hsum : out.1 * d + out.2 = high * 2 ^ k + n := by
    simpa only [Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hn] using
      loop_conservation d n k 0 high
  have hbound : out.2 < d := loop_remainder_lt d n k 0 high hhigh hd
  exact (div_mod_of_mul_add d out.1 out.2 (high * 2 ^ k + n) hd hbound hsum).1.symm

/-- The loop computes the remainder of `high * 2^k + n` when `n < 2^k`. -/
theorem loop_remainder (d n k high : Nat) (hn : n < 2 ^ k) (hhigh : high < d)
    (hd : 0 < d) :
    (loop d n k 0 high).2 = (high * 2 ^ k + n) % d := by
  let out := loop d n k 0 high
  have hsum : out.1 * d + out.2 = high * 2 ^ k + n := by
    simpa only [Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hn] using
      loop_conservation d n k 0 high
  have hbound : out.2 < d := loop_remainder_lt d n k 0 high hhigh hd
  exact (div_mod_of_mul_add d out.1 out.2 (high * 2 ^ k + n) hd hbound hsum).2.symm

/-- The computed quotient is strictly below `2^k` when the input fits in `k` bits. -/
theorem loop_quotient_lt (d n k high : Nat) (hn : n < 2 ^ k) (hhigh : high < d)
    (hd : 0 < d) :
    (loop d n k 0 high).1 < 2 ^ k := by
  rw [loop_quotient d n k high hn hhigh hd]
  apply Nat.div_lt_of_lt_mul
  calc
    high * 2 ^ k + n < high * 2 ^ k + 2 ^ k := Nat.add_lt_add_left hn _
    _ = (high + 1) * 2 ^ k := by simp [Nat.add_mul]
    _ ≤ d * 2 ^ k := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hhigh)

/-- Combine the high-word quotient with a low-word pass from its remainder. -/
theorem two_word_quotient (d hi lo base : Nat) (hd : 0 < d) :
    (hi / d) * base + ((hi % d) * base + lo) / d = (hi * base + lo) / d := by
  have h : hi * base + lo = ((hi % d) * base + lo) + ((hi / d) * base) * d := by
    calc
      hi * base + lo = (hi % d + d * (hi / d)) * base + lo :=
        congrArg (fun value => value * base + lo) (Nat.mod_add_div hi d).symm
      _ = ((hi % d) * base + lo) + ((hi / d) * base) * d := by
        rw [Nat.add_mul]
        ac_rfl
  rw [h, Nat.add_mul_div_right _ _ hd, Nat.add_comm]

end SszNative.Division
