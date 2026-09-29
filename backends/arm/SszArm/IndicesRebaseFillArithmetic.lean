import SszIndicesArithmeticSemanticWords
import SszIndicesArithmeticInitialization
import SszArm.IndicesStorage

set_option autoImplicit false

namespace SszArm.Indices.Rebase.Fill

open SszNative (NatOperand)
open SszNative.Indices

/-- The explicit whole-limb branch compensates for AArch64 LSL's six-bit
shift count. In particular 64 must not be confused with zero. -/
def loweredMask (bits : Nat) : BitVec 64 :=
  if bits = 64 then -1 else ~~~((-1 : BitVec 64) <<< (bits % 64))

theorem loweredMask_eq (bits : Nat) (bounded : bits ≤ 64) :
    loweredMask bits = lowMask bits := by
  by_cases whole : bits = 64
  · simp [loweredMask, lowMask, whole]
  · have small : bits < 64 := by omega
    rw [loweredMask, if_neg whole, Nat.mod_eq_of_lt small]
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro offset inside
    rw [BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      lowMask_bit bits offset bounded]
    rw [BitVec.neg_one_eq_allOnes, BitVec.getLsbD_allOnes]
    by_cases below : offset < bits
    · simp [inside, below]
    · simp [inside, below, show offset - bits < 64 by omega]

/-- CSEL zero at the whole-limb boundary is the complement of the lower mask. -/
def loweredUpper (bits : Nat) : BitVec 64 :=
  if bits = 64 then 0 else (-1 : BitVec 64) <<< (bits % 64)

theorem loweredUpper_eq (bits : Nat) (bounded : bits ≤ 64) :
    loweredUpper bits = ~~~(lowMask bits) := by
  rw [← loweredMask_eq bits bounded]
  by_cases whole : bits = 64 <;> simp [loweredUpper, loweredMask, whole]

/-- This saturation applies to logical Nat metadata, not to the input's
numeric value or its physical limb count. -/
def clamp (bits position : Nat) : Nat := min (bits - position * 64) 64

theorem clamp_le (bits position : Nat) : clamp bits position ≤ 64 := Nat.min_le_right _ _

def loweredRange (position start stop : Nat) : BitVec 64 :=
  loweredMask (clamp stop position) &&& loweredUpper (clamp start position)

theorem loweredRange_eq (position start stop : Nat) :
    loweredRange position start stop = rangeWord position start stop := by
  rw [loweredRange, loweredMask_eq _ (clamp_le _ _),
    loweredUpper_eq _ (clamp_le _ _)]
  rfl

/-- Register-level initializer shared by the first word, loaded Large words,
and the zero-extension arm after the physical input slice ends. -/
def loweredWord (raw : BitVec 64) (bits position : Nat) : BitVec 64 :=
  (raw &&& loweredMask (clamp bits position)) |||
    (loweredMask (clamp (bits + 1) position) &&& loweredUpper (clamp bits position))

def sourceWord (index : NatOperand) (bits position : Nat) : BitVec 64 :=
  (word index position &&& rangeWord position 0 bits) ||| rangeWord position bits (bits + 1)

theorem loweredWord_eq (index : NatOperand) (bits position : Nat) :
    loweredWord (word index position) bits position = sourceWord index bits position := by
  simp only [loweredWord, loweredMask_eq _ (clamp_le _ _),
    loweredUpper_eq _ (clamp_le _ _), sourceWord, rangeWord]
  simp [clamp, lowMask]

/-- No canonicality assumption: empty and zero-padded Large operands take the
same physical-end branch as every other Large representation. -/
theorem large_past (pointer : BitVec 64) (words : List (BitVec 64))
    (bits position : Nat) (past : words.length ≤ position) :
    loweredWord 0 bits position = sourceWord (.large pointer words) bits position := by
  have absent : word (.large pointer words) position = 0 := by
    simp [word, List.getElem?_eq_none (by omega)]
  simpa only [absent] using loweredWord_eq (.large pointer words) bits position

theorem small_past (raw : BitVec 64) (bits position : Nat) (positive : 0 < position) :
    loweredWord 0 bits position = sourceWord (.small raw) bits position := by
  simpa [word, show position ≠ 0 by omega] using loweredWord_eq (.small raw) bits position

theorem clamp_before (bits position : Nat) (before : position * 64 + 64 ≤ bits) :
    clamp bits position = 64 := by unfold clamp; omega

theorem clamp_after (bits position : Nat) (after : bits ≤ position * 64) :
    clamp bits position = 0 := by unfold clamp; omega

/-- Complete words below the new root bit are copied without normalization. -/
theorem loweredWord_before (raw : BitVec 64) (bits position : Nat)
    (before : position * 64 + 64 ≤ bits) : loweredWord raw bits position = raw := by
  simp [loweredWord, clamp_before bits position before,
    clamp_before (bits + 1) position (by omega), loweredMask, loweredUpper]

/-- Words strictly above the new root bit are zero, irrespective of source data. -/
theorem loweredWord_after (raw : BitVec 64) (bits position : Nat)
    (after : bits + 1 ≤ position * 64) : loweredWord raw bits position = 0 := by
  simp [loweredWord, clamp_after bits position (by omega),
    clamp_after (bits + 1) position after, loweredMask, loweredUpper]

/-- At an exact multiple of 64 the root occupies bit zero of a new word; the
preceding word is not accidentally erased by LSL modulo 64. -/
theorem loweredWord_whole (raw : BitVec 64) (position : Nat) :
    loweredWord raw (position * 64) position = 1#64 := by
  have lo : clamp (position * 64) position = 0 := by unfold clamp; omega
  have hi : clamp (position * 64 + 1) position = 1 := by unfold clamp; omega
  simp only [loweredWord, lo, hi]
  have low : loweredMask 0 = 0#64 := by decide
  have high : loweredMask 1 &&& loweredUpper 0 = 1#64 := by decide
  simp only [low, BitVec.and_zero, high, BitVec.zero_or]

/-- The logical list is exactly the ascending initializer; it retains every
allocated slot, even a zero high limb. -/
def initialized (index : NatOperand) (bits start count : Nat) : List (BitVec 64) :=
  (fillWords (fun position (_ : Unit) => (sourceWord index bits position, ())) start count ()).1

theorem initialized_length (index : NatOperand) (bits start count : Nat) :
    (initialized index bits start count).length = count :=
  fillWords_length _ start count ()

theorem initialized_prefix (index : NatOperand) (bits start first rest : Nat) :
    (initialized index bits start (first + rest)).take first = initialized index bits start first :=
  fillWords_prefix _ start first rest ()

theorem initialized_cons (index : NatOperand) (bits start count : Nat) :
    initialized index bits start (count + 1) =
      sourceWord index bits start :: initialized index bits (start + 1) count := rfl

/-- Exact make_nat outcome, rather than an equation only on numerical values.
The pointer, committed cursor, allocation event and complete initialized list
are retained, and the Large constructor is never normalized away. -/
theorem allocated_result (index : NatOperand) (bits count base capacity used : Nat)
    (reservation : SszNative.Arena.Reservation)
    (increment : bits + 1 < 2 ^ 128)
    (counted : wordCount (bits + 1) = .ok (count + 2))
    (reserved : SszNative.Arena.reserve base capacity used (count + 2) = some reservation) :
    rebase index bits base capacity used =
      arithmetic used ⟨.ok (.large (BitVec.ofNat 64 reservation.pointer)
        (initialized index bits 0 (count + 2))), reservation.used,
        some reservation, initialized index bits 0 (count + 2)⟩ := by
  simp only [rebase, increment, ↓reduceIte, counted, makeNat]
  exact makeNatState_large count base capacity used ()
    (fun position (_ : Unit) => (sourceWord index bits position, ())) reservation reserved

/-- Physical containment of every initialized word follows from the existing
allocator contract, independently of the operand's logical value. -/
theorem initialized_slot (count base capacity used : Nat)
    (reservation : SszNative.Arena.Reservation)
    (reserved : SszNative.Arena.reserve base capacity used (count + 2) = some reservation)
    (slot : Nat) (inside : slot < count + 2) :
    base + used ≤ reservation.pointer + 8 * slot ∧
      reservation.pointer + 8 * slot + 8 ≤ base + reservation.used ∧
      reservation.used ≤ capacity :=
  makeNatState_slot_within count base capacity used reservation reserved slot inside

end SszArm.Indices.Rebase.Fill
