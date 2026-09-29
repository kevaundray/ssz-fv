import SszIndicesCore

set_option autoImplicit false

namespace SszNative.Proof

/-- Checked conversion on both supported, 64-bit native targets. Logical path
lengths are not reduced modulo this bound. -/
def physicalIndex (value : Nat) : Option Nat :=
  if value < 2 ^ 64 then some value else none

/-- The native shifted borrowed-word view, including both checked source-word
conversions and the zero extension of noncanonical representations. -/
def shiftedWord (index : NatOperand) (offset position : Nat) : BitVec 64 :=
  let source := offset / 64 + position
  let low : BitVec 64 := match physicalIndex source with
    | none => 0
    | some source => Indices.word index source
  let shift := offset % 64
  if shift = 0 then low else
    let high : BitVec 64 := match physicalIndex (source + 1) with
      | none => 0
      | some source => Indices.word index source
    (low >>> shift) ||| (high <<< (64 - shift))

def windowMask (held : Nat) : BitVec 64 :=
  if held = 64 then BitVec.ofNat 64 (2 ^ 64 - 1)
  else BitVec.ofNat 64 (2 ^ held - 1)

/-- Scan the high words in source order. The recursion counts actual loop
iterations, not a logical-index fuel budget. -/
def windowHighZero (index : NatOperand) (offset effective : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | position, remaining + 1 =>
      if shiftedWord index offset position &&&
          windowMask (min (effective - position * 64) 64) != 0 then false
      else windowHighZero index offset effective (position + 1) remaining

/-- A physically unrepresentable window is absent, not a rejected generalized
index. In particular an arbitrarily wide all-zero window succeeds. -/
def window (index : NatOperand) (offset width : Nat) : Option Nat :=
  let effective := min (Indices.bitLength index - offset) width
  if effective = 0 then some 0 else
    match physicalIndex ((effective + 63) / 64) with
    | none => none
    | some words =>
        if windowHighZero index offset effective 1 (words - 1) then
          let mask := if 64 ≤ effective then windowMask 64 else windowMask effective
          physicalIndex (shiftedWord index offset 0 &&& mask).toNat
        else none

/-- Native checked multiplication followed by checked addition. -/
def physicalOffset (base position span : Nat) : Option Nat := do
  let delta ← physicalIndex (position * span)
  physicalIndex (base + delta)

/-- The large-span branch never constructs a huge shift merely to discover that
it cannot name any physically backed leaf. -/
def boundedStart (index : NatOperand) (depth base spanDepth : Nat) : Option Nat :=
  let position := window index 0 depth
  if 64 ≤ spanDepth then
    match position with
    | some 0 => some base
    | _ => none
  else position.bind (fun position => physicalOffset base position (2 ^ spanDepth))

def boundedStop (count start spanDepth : Nat) : Nat :=
  if 64 ≤ spanDepth then count
  else min (min (start + 2 ^ spanDepth) (2 ^ 64 - 1)) count

@[simp] theorem physicalIndex_of_lt (value : Nat) (fits : value < 2 ^ 64) :
    physicalIndex value = some value := by simp [physicalIndex, fits]

@[simp] theorem physicalIndex_of_ge (value : Nat) (large : 2 ^ 64 ≤ value) :
    physicalIndex value = none := by simp [physicalIndex, Nat.not_lt.mpr large]

theorem physicalIndex_some (value result : Nat)
    (converted : physicalIndex value = some result) :
    value = result ∧ value < 2 ^ 64 := by
  unfold physicalIndex at converted
  split at converted
  · exact ⟨Option.some.inj converted, by assumption⟩
  · cases converted

theorem window_zero_width (index : NatOperand) (offset : Nat) :
    window index offset 0 = some 0 := by simp [window]

theorem window_above_bits (index : NatOperand) (offset width : Nat)
    (above : Indices.bitLength index ≤ offset) : window index offset width = some 0 := by
  simp [window, Nat.sub_eq_zero_of_le above]

theorem window_some_physical (index : NatOperand) (offset width position : Nat)
    (found : window index offset width = some position) : position < 2 ^ 64 := by
  dsimp only [window] at found
  split at found
  · cases found; exact Nat.two_pow_pos 64
  · split at found
    · cases found
    · split at found
      · obtain ⟨same, fits⟩ := physicalIndex_some _ _ found
        simpa only [same] using fits
      · cases found

theorem boundedStart_huge_first (index : NatOperand) (depth base spanDepth : Nat)
    (huge : 64 ≤ spanDepth) (first : window index 0 depth = some 0) :
    boundedStart index depth base spanDepth = some base := by
  simp [boundedStart, huge, first]

theorem boundedStart_huge_missing (index : NatOperand) (depth base spanDepth : Nat)
    (huge : 64 ≤ spanDepth) (missing : window index 0 depth = none) :
    boundedStart index depth base spanDepth = none := by
  simp [boundedStart, huge, missing]

theorem windowHighZero_append (index : NatOperand) (offset effective position left right : Nat) :
    windowHighZero index offset effective position (left + right) =
      (windowHighZero index offset effective position left &&
        windowHighZero index offset effective (position + left) right) := by
  induction left generalizing position with
  | zero => simp [windowHighZero]
  | succ left ih =>
      rw [Nat.succ_add]
      simp only [windowHighZero]
      split
      · rfl
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (position + 1)

end SszNative.Proof
