import SszArm.IndicesNatShrArithmetic
import SszIndicesArithmetic

set_option autoImplicit false

namespace SszArm.Indices.CeilShift

open SszNative (NatOperand)

/-- LSL consumes six bits; the actual caller's bound rules out its wraparound. -/
theorem low_mask (bits : Nat) (bounded : bits ≤ 8) :
    ~~~((-1 : BitVec 64) <<< (bits % 64)) = SszNative.Indices.lowMask bits := by
  rw [Nat.mod_eq_of_lt (show bits < 64 by omega)]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index inside
  rw [BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    SszNative.Indices.lowMask_bit bits index (by omega)]
  rw [BitVec.neg_one_eq_allOnes, BitVec.getLsbD_allOnes]
  by_cases below : index < bits
  · simp [inside, below]
  · simp [inside, below, show index - bits < 64 by omega]

theorem low_mask_test (value : BitVec 64) (bits : Nat) (bounded : bits ≤ 8) :
    value &&& ~~~((-1 : BitVec 64) <<< (bits % 64)) =
      value &&& SszNative.Indices.lowMask bits := by
  rw [low_mask bits bounded]

/-- The remainder branch is never entered with a zero shift. -/
theorem remainder_positive (operand : NatOperand) (bits : Nat)
    (remainder : SszNative.Indices.word operand 0 &&& SszNative.Indices.lowMask bits ≠ 0) :
    0 < bits := by
  by_contra nonpositive
  have zero : bits = 0 := by omega
  subst bits
  simp [SszNative.Indices.lowMask] at remainder

/-- The literal NEG W3/LSR/LSL/ORR closure agrees with the source for every
logical Nat representation, including empty or trailing-zero Large. -/
theorem shifted_word (operand : NatOperand) (bits position : Nat)
    (physical : operand.words.length < 2^64) (bounded : bits ≤ 8)
    (remainder : SszNative.Indices.word operand 0 &&& SszNative.Indices.lowMask bits ≠ 0) :
    NatShr.loweredWord operand bits position = SszNative.Indices.shiftedWord operand bits position :=
  NatShr.loweredWord_indices operand bits position physical
    (remainder_positive operand bits remainder) (by omega)

/-- Exact source tailcall branch: no normalization or ceil-div replacement. -/
theorem no_remainder (operand : NatOperand) (bits base capacity used : Nat)
    (remainder : SszNative.Indices.word operand 0 &&& SszNative.Indices.lowMask bits = 0) :
    SszNative.Indices.ceilShift operand bits base capacity used =
      SszNative.Indices.arithmetic used (SszNative.NatShift.shr operand bits base capacity used) := by
  simp only [SszNative.Indices.ceilShift, remainder, beq_self_eq_true, ↓reduceIte]

/-- The ascending machine scan and the source's descending allWords have the
same all-ones decision; neither requires a canonical representation. -/
theorem all_ones_iff (operand : NatOperand) (bits count : Nat) :
    SszNative.Indices.allWords
      (fun i => SszNative.Indices.shiftedWord operand bits i == -1) count = true ↔
      ∀ i < count, SszNative.Indices.shiftedWord operand bits i = -1 := by
  rw [SszNative.Indices.allWords_iff]
  simp only [beq_iff_eq]

/-- Carry propagates only through a maximal limb; this is the per-limb invariant
used at ADDS X16,X16,X14 and its B.HS materialization. -/
theorem carry_step (operand : NatOperand) (bits position : Nat) (carry : Bool) :
    (SszNative.Indices.ceilStep operand bits position carry).2 =
      (carry && (SszNative.Indices.shiftedWord operand bits position == -1)) := by
  have bound := (SszNative.Indices.shiftedWord operand bits position).isLt
  cases carry with
  | false =>
      simp [SszNative.Indices.ceilStep, show ¬2^64 ≤
        (SszNative.Indices.shiftedWord operand bits position).toNat by omega]
  | true =>
      simp only [SszNative.Indices.ceilStep, ↓reduceIte, Bool.true_and]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq]
      constructor
      · intro overflow
        apply BitVec.eq_of_toNat_eq
        change (SszNative.Indices.shiftedWord operand bits position).toNat = 2^64 - 1
        change 2^64 ≤ (SszNative.Indices.shiftedWord operand bits position).toNat + 1 at overflow
        omega
      · intro maximum
        rw [maximum]
        decide

/-- Stateful fill records precisely the increasing initialized prefix and the
carry passed to its next initializer. -/
theorem fill_prefix (operand : NatOperand) (bits start count : Nat) (carry : Bool) :
    SszNative.Indices.fillWords (SszNative.Indices.ceilStep operand bits) start (count + 1) carry =
      let first := SszNative.Indices.ceilStep operand bits start carry
      let rest := SszNative.Indices.fillWords (SszNative.Indices.ceilStep operand bits)
        (start + 1) count first.2
      (first.1 :: rest.1, rest.2) := rfl

/-- Failed reservation has no initialized output limbs and retains the cursor;
this equation uses the shared operational model, not a rollback abstraction. -/
theorem reserve_failure (operand : NatOperand) (bits count base capacity used : Nat)
    (failed : SszNative.Arena.reserve base capacity used (count + 2) = none) :
    SszNative.Indices.makeNatState (count + 2) base capacity used true
      (SszNative.Indices.ceilStep operand bits) =
      SszNative.Indices.arithmetic used
        (SszNative.NatArithmetic.unchanged used (.error .scratchExhausted)) := by
  simp only [SszNative.Indices.makeNatState, failed]

end SszArm.Indices.CeilShift
