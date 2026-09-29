import SszNatOperand
import Ssz.Merkle.Tree

set_option autoImplicit false

namespace SszNative.MerkleWords

/-- The native hash-sized, zero-initialized destination. -/
def zeroWord : Ssz.Bytes := Array.replicate 32 0

/-- Copy the first `count` little-endian bytes of one raw native limb.
The recursion writes lower byte addresses before higher byte addresses. -/
def writeLimbBytes (buffer : Ssz.Bytes) (start : Nat) (limb : BitVec 64) :
    Nat → Ssz.Bytes
  | 0 => buffer
  | count + 1 =>
      (writeLimbBytes buffer start limb count).set! (start + count)
        (Limbs.byteAt [limb] count)

/-- The completed iterations of `length_word`'s eight-byte chunk loop.
The raw representation is read directly, with absent limbs read as zero. -/
def lengthLoop (operand : NatOperand) : Nat → Ssz.Bytes
  | 0 => zeroWord
  | count + 1 =>
      writeLimbBytes (lengthLoop operand count) (8 * count)
        (operand.words[count]?.getD 0) 8

/-- The four actual limb writes into the 32-byte destination. -/
def lengthWord (operand : NatOperand) : Ssz.Bytes := lengthLoop operand 4

/-- Observing an in-bounds byte after a native array write. -/
theorem setByte_get (buffer : Ssz.Bytes) (position index : Nat) (byte : UInt8)
    (inside : index < buffer.size) :
    (buffer.set! position byte)[index]! =
      if position = index then byte else buffer[index]! := by
  simp [getElem!_pos, inside, Array.getElem_setIfInBounds]

@[simp] theorem writeLimbBytes_size (buffer : Ssz.Bytes) (start : Nat)
    (limb : BitVec 64) (count : Nat) :
    (writeLimbBytes buffer start limb count).size = buffer.size := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [writeLimbBytes, Array.set!_eq_setIfInBounds,
      Array.size_setIfInBounds, ih]

/-- Byte-copy invariant, obtained from the individual destination writes. -/
theorem writeLimbBytes_get (buffer : Ssz.Bytes) (start : Nat)
    (limb : BitVec 64) (count index : Nat) (inside : index < buffer.size) :
    (writeLimbBytes buffer start limb count)[index]! =
      if start ≤ index ∧ index < start + count then
        Limbs.byteAt [limb] (index - start)
      else buffer[index]! := by
  induction count with
  | zero =>
      simp only [writeLimbBytes,
        show ¬(start ≤ index ∧ index < start + 0) by omega, ↓reduceIte]
  | succ count ih =>
      rw [writeLimbBytes, setByte_get _ _ _ _ (by simpa using inside)]
      by_cases last : start + count = index
      · subst index
        split
        · simp only [show start ≤ start + count ∧ start + count < start + (count + 1)
            by omega, true_and, ↓reduceIte, Nat.add_sub_cancel_left]
        · rename_i impossible
          exact False.elim (impossible rfl)
      · simp only [last, ↓reduceIte]
        rw [ih]
        by_cases covered : start ≤ index ∧ index < start + count
        · simp only [covered, show start ≤ index ∧ index < start + (count + 1)
            by omega, true_and, ↓reduceIte]
        · simp only [covered, show ¬(start ≤ index ∧ index < start + (count + 1))
            by omega, ↓reduceIte]

@[simp] theorem lengthLoop_size (operand : NatOperand) (count : Nat) :
    (lengthLoop operand count).size = 32 := by
  induction count with
  | zero => simp [lengthLoop, zeroWord]
  | succ count ih => simp only [lengthLoop, writeLimbBytes_size, ih]

/-- The existing limb encoding locates each byte in its original raw limb. -/
theorem limb_byteAt (limbs : List (BitVec 64)) (limbIndex offset : Nat)
    (small : offset < 8) :
    Limbs.byteAt [limbs[limbIndex]?.getD 0] offset =
      Limbs.byteAt limbs (8 * limbIndex + offset) := by
  have quotient : (8 * limbIndex + offset) / 8 = limbIndex := by omega
  have remainder : (8 * limbIndex + offset) % 8 = offset := by omega
  simp [Limbs.byteAt, Nat.div_eq_of_lt small, Nat.mod_eq_of_lt small,
    quotient, remainder]

/-- After `count` chunk writes, exactly the lower `8 * count` bytes have
been copied. Every untouched byte still comes from the zero initialization. -/
theorem lengthLoop_get (operand : NatOperand) (count index : Nat)
    (inside : index < 32) :
    (lengthLoop operand count)[index]! =
      if index < 8 * count then Limbs.byteAt operand.words index else 0 := by
  induction count with
  | zero => simp [lengthLoop, zeroWord, getElem!_pos, inside]
  | succ count ih =>
      rw [lengthLoop, writeLimbBytes_get _ _ _ _ _ (by simpa using inside)]
      by_cases earlier : index < 8 * count
      · simp only [show ¬(8 * count ≤ index ∧ index < 8 * count + 8) by omega,
          ih, earlier, show index < 8 * (count + 1) by omega, ↓reduceIte]
      · by_cases copied : index < 8 * (count + 1)
        · simp only [show 8 * count ≤ index ∧ index < 8 * count + 8 by omega,
            copied, true_and, ↓reduceIte]
          have byteIs := limb_byteAt operand.words count (index - 8 * count) (by omega)
          simpa only [show 8 * count + (index - 8 * count) = index by omega] using byteIs
        · simp only [show ¬(8 * count ≤ index ∧ index < 8 * count + 8) by omega,
            ih, earlier, copied, ↓reduceIte]

@[simp] theorem lengthWord_size (operand : NatOperand) :
    (lengthWord operand).size = 32 := lengthLoop_size operand 4

/-- The native writes recover the existing limb-byte model, not a new encoding. -/
theorem lengthWord_eq_limbBytes (operand : NatOperand) :
    lengthWord operand = Limbs.bytes operand.words 32 := by
  apply Array.ext
  · simp [Limbs.bytes]
  · intro index inside otherInside
    have small : index < 32 := by simpa using inside
    have copied := lengthLoop_get operand 4 index small
    simpa [lengthWord, Limbs.bytes, getElem!_pos, lengthLoop_size, small] using copied

/-- Refinement for every raw operand: empty Large values, redundant high zero
limbs and values beyond the 256-bit mixing field require no extra premise. -/
theorem lengthWord_eq_upstream (operand : NatOperand) :
    lengthWord operand = Ssz.lengthWord operand.value := by
  rw [lengthWord_eq_limbBytes, Limbs.bytes_eq_uintBytes]
  rfl

/-- Exact per-byte truncation, with no bound on the represented natural. -/
theorem lengthWord_byte (operand : NatOperand) (index : Nat) (inside : index < 32) :
    (lengthWord operand)[index]! =
      UInt8.ofNat ((operand.value / 2 ^ (8 * index)) % 256) := by
  have copied := lengthLoop_get operand 4 index inside
  simpa only [lengthWord, show index < 8 * 4 by omega, ↓reduceIte,
    Limbs.byteAt_eq_value, NatOperand.value] using copied

private theorem uintBytes_mod (byteCount number : Nat) :
    Ssz.uintBytes byteCount (number % 2 ^ (8 * byteCount)) =
      Ssz.uintBytes byteCount number := by
  apply Array.ext
  · simp only [Ssz.uintBytes_size]
  · intro index inside otherInside
    have small : index < byteCount := by simpa only [Ssz.uintBytes_size] using inside
    rw [Limbs.uintBytes_byte _ _ _ small, Limbs.uintBytes_byte _ _ _ small]
    have splitPower : 2 ^ (8 * byteCount) =
        2 ^ (8 * index) * 2 ^ (8 * byteCount - 8 * index) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [splitPower, Nat.mod_mul_right_div_self]
    have divides : 256 ∣ 2 ^ (8 * byteCount - 8 * index) := by
      change 2 ^ 8 ∣ 2 ^ (8 * byteCount - 8 * index)
      exact Nat.pow_dvd_pow 2 (by omega)
    rw [Nat.mod_mod_of_dvd _ divides]

/-- The native word depends on exactly the low 256 bits, even for larger values. -/
theorem lengthWord_truncation (operand : NatOperand) :
    lengthWord operand = Ssz.lengthWord (operand.value % 2 ^ 256) := by
  rw [lengthWord_eq_upstream]
  exact (uintBytes_mod 32 operand.value).symm

/-- Decoding observes precisely the truncated count. -/
theorem read_lengthWord (operand : NatOperand) :
    Ssz.readUint (lengthWord operand) 0 32 = operand.value % 2 ^ 256 := by
  rw [lengthWord_truncation]
  exact Ssz.readUint_uintBytes 32 _ (Nat.mod_lt _ (Nat.two_pow_pos 256))

/-- A count that fits the mixing field is recovered without truncation. -/
theorem read_lengthWord_exact (operand : NatOperand) (fits : operand.value < 2 ^ 256) :
    Ssz.readUint (lengthWord operand) 0 32 = operand.value := by
  rw [read_lengthWord, Nat.mod_eq_of_lt fits]

end SszNative.MerkleWords
