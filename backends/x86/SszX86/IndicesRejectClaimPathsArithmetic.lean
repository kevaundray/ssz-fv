import SszX86.IndicesPrefixEqualArithmetic
import SszIndicesFrontierSemanticValidation

set_option autoImplicit false

namespace SszX86.IndicesRejectClaimPaths
open SszNative SszNative.Indices

/-- The comparison call is reached only after both unsigned depth gates. -/
def ancestorTest (claim : NatOperand) (claimDepth : Nat) (ancestor : NatOperand) : Bool :=
  depth ancestor != 0 && depth ancestor < claimDepth &&
    prefixEqual claim (claimDepth - depth ancestor) false ancestor 0

def claimResult (indices : List NatOperand) (claim : NatOperand) : Except Error Unit := do
  let claimDepth ← length claim
  if indices.any (ancestorTest claim claimDepth) then
    throw (.nestedIndex claim)
  pure ()

/-- A claim's zero/root check precedes its own complete ancestor scan; a later
claim cannot override this claim's first failure. -/
theorem rejectClaimPaths_cons (indices : List NatOperand) (claim : NatOperand)
    (rest : List NatOperand) :
    rejectClaimPaths indices (claim :: rest) =
      match claimResult indices claim with
      | .error reason => .error reason
      | .ok () => rejectClaimPaths indices rest := by
  cases measured : length claim with
  | error reason =>
      simp [rejectClaimPaths, claimResult, measured, Bind.bind, Except.bind]
  | ok count =>
      cases detected : indices.any (ancestorTest claim count) <;>
        simp only [ancestorTest] at detected <;>
        simp [rejectClaimPaths, claimResult, ancestorTest, measured,
          detected, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem claimResult_length_error (indices : List NatOperand) (claim : NatOperand)
    (reason : Error) (failed : length claim = .error reason) :
    claimResult indices claim = .error reason := by
  simp [claimResult, failed, Bind.bind, Except.bind]

theorem claimResult_nested (indices : List NatOperand) (claim : NatOperand)
    (count : Nat) (measured : length claim = .ok count)
    (ancestor : NatOperand) (member : ancestor ∈ indices)
    (detected : ancestorTest claim count ancestor = true) :
    claimResult indices claim = .error (.nestedIndex claim) := by
  have found : indices.any (ancestorTest claim count) = true :=
    List.any_eq_true.mpr ⟨ancestor, member, detected⟩
  simp [claimResult, measured, found, Bind.bind, Except.bind]

/-- The source's unit result forgets which ancestor matched, but never which
claim was being visited. This is the exact recurrence used by the linked loop. -/
theorem ancestor_scan_cons (claim : NatOperand) (count : Nat)
    (ancestor : NatOperand) (rest : List NatOperand) :
    (ancestor :: rest).any (ancestorTest claim count) =
      (ancestorTest claim count ancestor || rest.any (ancestorTest claim count)) :=
  List.any_cons

theorem ancestor_call_shift (claim ancestor : NatOperand) (count : Nat)
    (measured : length claim = .ok count)
    (positive : depth ancestor ≠ 0) (shallower : depth ancestor < count) :
    count - depth ancestor = bitLength claim - bitLength ancestor := by
  have claimDepth := (length_success claim count measured).1
  unfold depth at claimDepth positive shallower ⊢
  omega

theorem ancestor_call_flip (claim : NatOperand) (shift : Nat) :
    PrefixFlipDomain claim shift false := by
  intro impossible
  cases impossible

/-- All actual comparator calls retain their original bounded u128 difference.
This does not constrain the operand's numeric value or require canonical limbs. -/
theorem ancestor_call_shift_bound (claim ancestor : NatOperand) (count : Nat)
    (measured : length claim = .ok count)
    (physical : claim.words.length < 2 ^ 64) :
    count - depth ancestor < 2 ^ 128 := by
  have claimDepth := (length_success claim count measured).1
  have storage := bitLength_le_storage claim
  unfold depth at claimDepth
  omega

theorem rejectClaimPaths_append (indices earlier later : List NatOperand) :
    rejectClaimPaths indices (earlier ++ later) =
      match rejectClaimPaths indices earlier with
      | .error reason => .error reason
      | .ok () => rejectClaimPaths indices later := by
  induction earlier with
  | nil => rfl
  | cons claim rest ih =>
      simp only [List.cons_append, rejectClaimPaths_cons]
      cases current : claimResult indices claim with
      | error reason => rfl
      | ok unit => cases unit; exact ih

end SszX86.IndicesRejectClaimPaths
