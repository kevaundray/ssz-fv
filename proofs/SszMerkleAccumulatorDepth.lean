import SszNatOperand
import Ssz.Merkle.Tree
import Ssz.Proofs.Merkle.Merkleize

set_option autoImplicit false

namespace SszNative.MerkleAccumulator

/-- Native Merkle errors retain the supplied natural representations. -/
inductive Error where
  | merkleizeLimit (count capacity : NatOperand)
  | outputTooSmall
  deriving DecidableEq, Repr

inductive Host where
  | outputTooSmall
  deriving DecidableEq, Repr

def eraseResult {α : Type} : Except Error α → Except Host (Except Ssz.Err α)
  | .ok value => .ok (.ok value)
  | .error (.merkleizeLimit count capacity) =>
      .ok (.error (.merkleizeLimit count.value capacity.value))
  | .error .outputTooSmall => .error .outputTooSmall

/-- Mathematical result of the native bit-length helper, including zero. -/
def bitLength (number : Nat) : Nat :=
  if number = 0 then 0 else number.log2 + 1

/-- `usize::BITS - (count - 1).leading_zeros()` in the nontrivial branch.
The physical bound belongs to callers, not to the logical depth arithmetic. -/
def depthForCount (count : Nat) : Nat :=
  if count ≤ 1 then 0 else bitLength (count - 1)

/-- The native `bit_len - is_power_of_two` formula. The equality test is
false at zero and true exactly at powers of two. No logical capacity is capped. -/
def capacityDepth (capacity : NatOperand) : Nat :=
  bitLength capacity.value - (if capacity.value = 2 ^ capacity.value.log2 then 1 else 0)

/-- Capacity is checked before computing its depth; failure retains its exact
original representation, including redundant high zeros and empty Large values. -/
def boundedDepth (count : Nat) (limit : Option NatOperand) : Except Error Nat :=
  match limit with
  | none => .ok (depthForCount count)
  | some capacity =>
      if capacity.value < count then
        .error (.merkleizeLimit (.small (BitVec.ofNat 64 count)) capacity)
      else .ok (capacityDepth capacity)

/-- The decision and error construction in native `finish_depth`, before rooting. -/
def finishDepthDecision (count depth : Nat) : Except Error Nat :=
  if depth < depthForCount count then
    .error (.merkleizeLimit (.small (BitVec.ofNat 64 count))
      (.small (BitVec.ofNat 64 (2 ^ depth))))
  else .ok depth

theorem bitLength_le_iff (number depth : Nat) :
    bitLength number ≤ depth ↔ number < 2 ^ depth := by
  by_cases empty : number = 0
  · subst number
    have positive : 0 < 2 ^ depth := Nat.pow_pos (by decide)
    simp [bitLength, positive]
  · simp only [bitLength, empty, ↓reduceIte]
    have logarithm := Nat.log2_lt (n := number) (k := depth) empty
    omega

theorem depthForCount_le_iff (count depth : Nat) :
    depthForCount count ≤ depth ↔ count ≤ 2 ^ depth := by
  by_cases small : count ≤ 1
  · have positive : 0 < 2 ^ depth := Nat.pow_pos (by decide)
    simp only [depthForCount, small, ↓reduceIte]
    omega
  · simp only [depthForCount, small, ↓reduceIte, bitLength_le_iff]
    omega

theorem depthForCount_eq_depthFor (count : Nat) :
    depthForCount count = Ssz.depthFor count := by
  apply Nat.le_antisymm
  · exact (depthForCount_le_iff count (Ssz.depthFor count)).2
      (Ssz.le_two_pow_depthFor count)
  · exact Ssz.depthFor_le_of_le_two_pow
      ((depthForCount_le_iff count (depthForCount count)).1 (Nat.le_refl _))

theorem capacity_power_test_iff (number : Nat) :
    number = 2 ^ number.log2 ↔ ∃ exponent : Nat, number = 2 ^ exponent := by
  constructor
  · intro power
    exact ⟨number.log2, power⟩
  · rintro ⟨exponent, rfl⟩
    rw [Nat.log2_two_pow]

theorem capacityDepth_eq_depthFor (capacity : NatOperand) :
    capacityDepth capacity = Ssz.depthFor capacity.value := by
  by_cases empty : capacity.value = 0
  · simp [capacityDepth, bitLength, empty, Ssz.depthFor]
  · by_cases power : capacity.value = 2 ^ capacity.value.log2
    · calc
        capacityDepth capacity = capacity.value.log2 := by
          simp only [capacityDepth, bitLength, empty, ↓reduceIte]
          split <;> omega
        _ = Ssz.depthFor capacity.value :=
          (Ssz.depthFor_pow capacity.value.log2).symm.trans
            (congrArg Ssz.depthFor power.symm)
    · have upper : Ssz.depthFor capacity.value ≤ capacity.value.log2 + 1 :=
        Ssz.depthFor_le_of_le_two_pow (Nat.le_of_lt (Nat.lt_log2_self))
      have lowerPower : 2 ^ capacity.value.log2 < capacity.value := by
        have lower := Nat.log2_self_le empty
        omega
      have lower : capacity.value.log2 < Ssz.depthFor capacity.value := by
        have widened : 2 ^ capacity.value.log2 < 2 ^ Ssz.depthFor capacity.value :=
          Nat.lt_of_lt_of_le lowerPower (Ssz.le_two_pow_depthFor capacity.value)
        exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp widened
      simp only [capacityDepth, bitLength, empty, power, ↓reduceIte, Nat.sub_zero]
      omega

theorem finishDepth_undersize_iff (count depth : Nat) :
    depth < depthForCount count ↔ 2 ^ depth < count := by
  have adequacy := depthForCount_le_iff count depth
  omega

/-- Physical counts fit the native array. This does not bound logical capacities. -/
theorem depthForCount_le_64 (count : Nat) (physical : count < 2 ^ 64) :
    depthForCount count ≤ 64 :=
  (depthForCount_le_iff count 64).2 (Nat.le_of_lt physical)

/-- A rejected exact depth fits the native shift used to construct its capacity. -/
theorem finishDepth_undersize_lt_64 (count depth : Nat) (physical : count < 2 ^ 64)
    (undersize : depth < depthForCount count) : depth < 64 := by
  have bound := depthForCount_le_64 count physical
  omega

theorem small_value (number : Nat) (physical : number < 2 ^ 64) :
    (NatOperand.small (BitVec.ofNat 64 number)).value = number := by
  simp [NatOperand.value, NatOperand.words, Limbs.value, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt physical]

/-- Erasing the raw native error gives exactly the upstream depth/capacity
choice. Only the supplied physical count is bounded. -/
theorem boundedDepth_erasure (count : Nat) (limit : Option NatOperand)
    (physical : count < 2 ^ 64) :
    eraseResult (boundedDepth count limit) =
      .ok (match limit.map NatOperand.value with
        | none => .ok (Ssz.depthFor count)
        | some capacity =>
            if capacity < count then .error (.merkleizeLimit count capacity)
            else .ok (Ssz.depthFor capacity)) := by
  cases limit with
  | none => simp [boundedDepth, eraseResult, depthForCount_eq_depthFor]
  | some capacity =>
    by_cases undersize : capacity.value < count
    · simp [boundedDepth, undersize, eraseResult, small_value count physical]
    · simp [boundedDepth, undersize, eraseResult, capacityDepth_eq_depthFor]

/-- The exact failure representation does not normalize the caller's capacity. -/
theorem boundedDepth_error (count : Nat) (capacity : NatOperand)
    (undersize : capacity.value < count) :
    boundedDepth count (some capacity) =
      .error (.merkleizeLimit (.small (BitVec.ofNat 64 count)) capacity) := by
  simp [boundedDepth, undersize]

theorem boundedDepth_adequate (count depth : Nat) (limit : Option NatOperand)
    (success : boundedDepth count limit = .ok depth) : count ≤ 2 ^ depth := by
  cases limit with
  | none =>
    simp only [boundedDepth, Except.ok.injEq] at success
    subst depth
    exact (depthForCount_le_iff count (depthForCount count)).1 (Nat.le_refl _)
  | some capacity =>
    by_cases undersize : capacity.value < count
    · simp [boundedDepth, undersize] at success
    · simp only [boundedDepth, undersize, ↓reduceIte, Except.ok.injEq] at success
      subst depth
      rw [capacityDepth_eq_depthFor]
      exact Nat.le_trans (by omega) (Ssz.le_two_pow_depthFor capacity.value)

theorem finishDepthDecision_erasure (count depth : Nat) (physical : count < 2 ^ 64) :
    eraseResult (finishDepthDecision count depth) =
      .ok (if 2 ^ depth < count then .error (.merkleizeLimit count (2 ^ depth))
        else .ok depth) := by
  by_cases undersize : depth < depthForCount count
  · have capacitySmall : 2 ^ depth < 2 ^ 64 :=
      Nat.lt_trans ((finishDepth_undersize_iff count depth).1 undersize) physical
    simp [finishDepthDecision, undersize, eraseResult, small_value count physical,
      small_value (2 ^ depth) capacitySmall,
      (finishDepth_undersize_iff count depth).1 undersize]
  · have adequate : ¬ 2 ^ depth < count := by
      intro tooMany
      exact undersize ((finishDepth_undersize_iff count depth).2 tooMany)
    simp [finishDepthDecision, undersize, eraseResult, adequate]

end SszNative.MerkleAccumulator
