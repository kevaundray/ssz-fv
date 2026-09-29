import SszX86.IndicesStorage
import SszIndicesFrontierResourcesCore
import SszIndicesFrontierSemanticValidation

set_option autoImplicit false

namespace SszX86.IndicesHelperIndices
open SszNative SszNative.Indices

/-- The checked counter at offsets 2041--2077 counts retained nodes, not path
lengths. In particular, rejected candidates cannot cause an overflow. -/
theorem countLevels_exact (keep : Nat → Bool) (remaining level count : Nat)
    (bounded : count < 2 ^ 64) :
    countLevels keep remaining level count =
      if count + retainedLevels keep remaining level < 2 ^ 64 then
        .ok (count + retainedLevels keep remaining level) else .error scratch := by
  induction remaining generalizing level count with
  | zero => simp [countLevels, retainedLevels, bounded]
  | succ remaining ih =>
    by_cases selected : keep level = true
    · by_cases fits : count + 1 < 2 ^ 64
      · simp only [countLevels, selected, fits, ↓reduceIte, Bind.bind, Except.bind,
          retainedLevels]
        rw [ih (level + 1) (count + 1) fits]
        simp only [Nat.add_assoc]
      · have overflow : ¬ count + (1 + retainedLevels keep remaining (level + 1)) <
            2 ^ 64 := by omega
        simp [countLevels, retainedLevels, selected, fits, overflow, Bind.bind, Except.bind]
    · have excluded : keep level = false := Bool.eq_false_iff.mpr selected
      simpa only [countLevels, retainedLevels, excluded, Bool.false_eq_true,
        ↓reduceIte, Bind.bind, Except.bind, Nat.zero_add] using ih (level + 1) count bounded

/-- This is the complete count-pass outcome, including its sole failure. It
uses no claim-validity or successful-fill premise. -/
theorem countHelpers_exact (indices pending : List NatOperand) (claim count : Nat)
    (bounded : count < 2 ^ 64) :
    countHelpers indices pending claim count =
      if count + retainedClaims indices true pending claim < 2 ^ 64 then
        .ok (count + retainedClaims indices true pending claim) else .error scratch := by
  induction pending generalizing claim count with
  | nil => simp [countHelpers, retainedClaims, bounded]
  | cons index rest ih =>
    let amount := retainedLevels (isHelper indices index claim) (depth index) 0
    have first := countLevels_exact (isHelper indices index claim) (depth index) 0 count bounded
    by_cases fits : count + amount < 2 ^ 64
    · have counted : countLevels (isHelper indices index claim) (depth index) 0 count =
          .ok (count + amount) := by simpa only [amount, fits, ↓reduceIte] using first
      simp only [countHelpers, counted, Bind.bind, Except.bind]
      rw [ih (claim + 1) (count + amount) fits]
      simp only [retainedClaims, ↓reduceIte, Nat.add_assoc, amount]
    · have counted : countLevels (isHelper indices index claim) (depth index) 0 count =
          .error scratch := by simpa only [amount, fits, ↓reduceIte] using first
      have overflow : ¬ count + retainedClaims indices true (index :: rest) claim <
          2 ^ 64 := by
        simp only [retainedClaims, ↓reduceIte]
        change ¬ count + (amount + retainedClaims indices true rest (claim + 1)) < 2 ^ 64
        omega
      simp only [countHelpers, counted, Bind.bind, Except.bind, overflow, ↓reduceIte]

/-- The source initializer retains a claim/level cursor between slots. This
quantity counts the not-yet-visited retained nodes at that exact cursor. -/
def scanRemaining (indices : List NatOperand) : List NatOperand → Nat → Nat → Nat
  | [], _, _ => 0
  | index :: rest, claim, level =>
      retainedLevels (isHelper indices index claim) (depth index - level) level +
        retainedClaims indices true rest (claim + 1)

@[simp] theorem scanRemaining_start (indices pending : List NatOperand) (claim : Nat) :
    scanRemaining indices pending claim 0 = retainedClaims indices true pending claim := by
  cases pending <;> simp [scanRemaining, retainedClaims]

/-- The level increment is performed before the child call. Advancing past a
claim resets the level even when the selected child later fails. -/
theorem scanRemaining_step (indices : List NatOperand) (index : NatOperand)
    (rest : List NatOperand) (claim level : Nat) (inside : level < depth index) :
    scanRemaining indices (index :: rest) claim level =
      (if isHelper indices index claim level then 1 else 0) +
        if level + 1 = depth index then scanRemaining indices rest (claim + 1) 0
        else scanRemaining indices (index :: rest) claim (level + 1) := by
  have remaining : depth index - level = (depth index - (level + 1)) + 1 := by omega
  rw [scanRemaining, remaining, retainedLevels]
  by_cases last : level + 1 = depth index
  · have exhausted : depth index - (level + 1) = 0 := by omega
    simp only [last, ↓reduceIte, exhausted, retainedLevels, Nat.add_zero, scanRemaining_start]
  · simp only [last, ↓reduceIte, scanRemaining, Nat.add_assoc]

/-- Conservation for either branch of the initializer's candidate scan. The
counter changes only when the candidate is retained. -/
theorem scanRemaining_conserved (indices : List NatOperand) (index : NatOperand)
    (rest : List NatOperand) (claim level slot count : Nat)
    (inside : level < depth index)
    (conserved : slot + scanRemaining indices (index :: rest) claim level = count) :
    (slot + if isHelper indices index claim level then 1 else 0) +
        (if level + 1 = depth index then scanRemaining indices rest (claim + 1) 0
        else scanRemaining indices (index :: rest) claim (level + 1)) = count := by
  rw [scanRemaining_step indices index rest claim level inside] at conserved
  simpa only [Nat.add_assoc] using conserved

/-- At offsets 2527/2532 the reserved-slot loop has at least one retained node
left. Hence its claim index cannot reach the panic edge, independently of how
many intervening candidates have been rejected. -/
theorem claim_inside_of_remaining (indices : List NatOperand) (claim level slot count : Nat)
    (conserved : slot + scanRemaining indices (indices.drop claim) claim level = count)
    (pending : slot < count) : claim < indices.length := by
  by_contra outside
  have empty : indices.drop claim = [] := List.drop_eq_nil_of_le (by omega)
  simp only [empty, scanRemaining, Nat.add_zero] at conserved
  omega

/-- The original count pass establishes the conservation equation at the first
initializer; no successful initializer is assumed. -/
theorem counted_scan_start (indices : List NatOperand) (count : Nat)
    (counted : countHelpers indices indices 0 0 = .ok count) :
    0 + scanRemaining indices (indices.drop 0) 0 0 = count := by
  have exactCount := countHelpers_count indices indices 0 0 count counted
  simpa only [List.drop_zero, scanRemaining_start] using exactCount.symm

/-- Readonly ownership at a fill cursor comes from the original borrowed array,
not from a semantic child-success witness. -/
theorem cursor_nat_owned {m : DataMem} {readonly : Codec.Footprint}
    {pointer : BitVec 64} {indices : List NatOperand}
    (stored : Indices.Storage.NatArrayAt m readonly pointer indices)
    (claim level slot count : Nat)
    (conserved : slot + scanRemaining indices (indices.drop claim) claim level = count)
    (pending : slot < count) :
    ∃ inside : claim < indices.length,
      Codec.NatAt m readonly (pointer + BitVec.ofNat 64 (16 * claim)) indices[claim] := by
  have inside := claim_inside_of_remaining indices claim level slot count conserved pending
  exact ⟨inside, stored.elements claim inside⟩

/-- The duplicate scan's `length + 1` sentinel cannot wrap. The premise is the
physical 16-byte array extent, not a restriction on any represented natural. -/
theorem duplicate_sentinel_bounded {m : DataMem} {readonly : Codec.Footprint}
    {pointer : BitVec 64} {indices : List NatOperand}
    (stored : Indices.Storage.NatArrayAt m readonly pointer indices) :
    indices.length + 1 < 2 ^ 64 := by
  have bytes := stored.byteBound
  omega

/-- The slice-index-fail branch at offset 77 compares the current request index
against `length + 1`; every original loop position is strictly below it. -/
theorem duplicate_sentinel_not_reached {m : DataMem} {readonly : Codec.Footprint}
    {pointer : BitVec 64} {indices : List NatOperand}
    (stored : Indices.Storage.NatArrayAt m readonly pointer indices)
    (claim : Nat) (inside : claim < indices.length) :
    BitVec.ofNat 64 claim ≠ BitVec.ofNat 64 (indices.length + 1) := by
  intro equal
  have sentinel := duplicate_sentinel_bounded stored
  have bounded : claim < 2 ^ 64 := by omega
  have same := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded,
    Nat.mod_eq_of_lt sentinel] at same
  omega

/-- A successful validation gives positive depths in request order. Zero and
root claims must already have returned their precise validation error. -/
theorem validated_depth_positive (indices : List NatOperand)
    (accepted : rejectRelated indices = .ok ()) (index : NatOperand)
    (member : index ∈ indices) : 0 < depth index := by
  have valid := rejectRelated_valid indices accepted index member
  rw [depth_value]
  have positive : 1 ≤ index.value.log2 :=
    (Nat.le_log2 (by omega)).mpr (by simpa using valid)
  omega

/-- The increment and subtraction in the two-register level cursor fit u128
because the original physical limb slice does; values are not capped at u64. -/
theorem helper_level_u128 (index : NatOperand) (level : Nat)
    (physical : index.words.length < 2 ^ 64) (inside : level < depth index) :
    level + 1 < 2 ^ 128 ∧ depth index - level < 2 ^ 128 := by
  have bits := bitLength_u128 index physical
  unfold depth at *
  omega

/-- A termination measure for the source's inner `loop`, including rejected
candidates. It is derived from the finite input, not supplied as execution fuel. -/
def scanWork : List NatOperand → Nat → Nat
  | [], _ => 0
  | index :: rest, level => depth index - level + (rest.map depth).sum

@[simp] theorem scanWork_start (pending : List NatOperand) :
    scanWork pending 0 = (pending.map depth).sum := by
  cases pending <;> simp [scanWork]

theorem retainedLevels_le (keep : Nat → Bool) (remaining level : Nat) :
    retainedLevels keep remaining level ≤ remaining := by
  induction remaining generalizing level with
  | zero => rfl
  | succ remaining ih =>
    have tail := ih (level + 1)
    cases selected : keep level <;> simp only [retainedLevels, selected,
      Bool.false_eq_true, ↓reduceIte] <;> omega

theorem retainedClaims_le (indices pending : List NatOperand) (claim : Nat) :
    retainedClaims indices true pending claim ≤ (pending.map depth).sum := by
  induction pending generalizing claim with
  | nil => rfl
  | cons index rest ih =>
    have first := retainedLevels_le (isHelper indices index claim) (depth index) 0
    have tail := ih (claim + 1)
    simp only [retainedClaims, ↓reduceIte, List.map_cons, List.sum_cons]
    omega

theorem scanRemaining_le_work (indices pending : List NatOperand) (claim level : Nat) :
    scanRemaining indices pending claim level ≤ scanWork pending level := by
  cases pending with
  | nil => rfl
  | cons index rest =>
    have first := retainedLevels_le (isHelper indices index claim) (depth index - level) level
    have tail := retainedClaims_le indices rest (claim + 1)
    simp only [scanRemaining, scanWork]
    omega

theorem scanWork_decreases (index : NatOperand) (rest : List NatOperand) (level : Nat)
    (inside : level < depth index) :
    (if level + 1 = depth index then scanWork rest 0
      else scanWork (index :: rest) (level + 1)) < scanWork (index :: rest) level := by
  by_cases last : level + 1 = depth index
  · simp only [last, ↓reduceIte, scanWork_start, scanWork]
    omega
  · simp only [last, ↓reduceIte, scanWork]
    omega

theorem scanWork_positive (indices pending : List NatOperand) (claim level slot count : Nat)
    (conserved : slot + scanRemaining indices pending claim level = count)
    (remaining : slot < count) : 0 < scanWork pending level := by
  have bound := scanRemaining_le_work indices pending claim level
  omega

end SszX86.IndicesHelperIndices
