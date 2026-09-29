import SszMerkleWords
import SszPacking

set_option autoImplicit false

namespace SszNative.MerkleWords

/-- The native `(bit as u8) << offset` mask has exactly its selected bit.
This small finite calculation is checked by the kernel, without a native oracle. -/
theorem shiftedBool_bit (bit : Bool) (shift offset : Fin 8) :
    (((if bit then (1 : UInt8) else 0) <<< UInt8.ofNat shift.val).toNat.testBit offset.val) =
      (bit && decide (offset.val = shift.val)) := by
  revert bit shift offset
  decide

/-- Bridge the existing packed-bit observation to natural-number bit extensionality. -/
theorem byteProbe_eq_testBit (byte : UInt8) (offset : Nat) (small : offset < 8) :
    ((byte >>> UInt8.ofNat offset) &&& 1 == 1) = byte.toNat.testBit offset := by
  have bound : offset < UInt8.size := by change offset < 256; omega
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, ← UInt8.toNat_inj, UInt8.toNat_and, UInt8.toNat_shiftRight,
    UInt8.toNat_ofNat_of_lt' bound, Nat.mod_eq_of_lt small, UInt8.toNat_one,
    Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_true_eq]

/-- Eight bit observations determine a byte; higher bits are excluded by its type. -/
theorem byte_eq_of_testBit {left right : UInt8}
    (same : ∀ offset, offset < 8 →
      left.toNat.testBit offset = right.toNat.testBit offset) : left = right := by
  apply UInt8.eq_iff_toBitVec_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro offset small
  exact same offset small

/-- One actual read/OR/write update of the native active-field loop. -/
def activeUpdate (buffer : Ssz.Bytes) (index : Nat) (bit : Bool) : Ssz.Bytes :=
  buffer.set! (index / 8)
    (buffer[index / 8]! ||| ((if bit then (1 : UInt8) else 0) <<< UInt8.ofNat (index % 8)))

/-- Completed iterations, starting from the zero buffer and retaining their
actual OR updates. The public entry point supplies the native iteration count. -/
def activeLoop (active : List Bool) : Nat → Ssz.Bytes
  | 0 => zeroWord
  | count + 1 => activeUpdate (activeLoop active count) count (active[count]?.getD false)

/-- Native `active.iter().take(256)`, including short and overlong inputs. -/
def activeFieldsWord (active : List Bool) : Ssz.Bytes :=
  activeLoop active (min active.length 256)

@[simp] theorem activeUpdate_size (buffer : Ssz.Bytes) (index : Nat) (bit : Bool) :
    (activeUpdate buffer index bit).size = buffer.size := by
  simp [activeUpdate]

@[simp] theorem activeLoop_size (active : List Bool) (count : Nat) :
    (activeLoop active count).size = 32 := by
  induction count with
  | zero => simp [activeLoop, zeroWord]
  | succ count ih => simp only [activeLoop, activeUpdate_size, ih]

@[simp] theorem activeFieldsWord_size (active : List Bool) :
    (activeFieldsWord active).size = 32 := activeLoop_size active _

/-- A destination update changes only its selected bit, by OR rather than
assignment. This statement also describes arbitrary dirty initial buffers. -/
theorem activeUpdate_bit (buffer : Ssz.Bytes) (index : Nat) (bit : Bool)
    (byteIndex offset : Nat) (inside : byteIndex < buffer.size) (small : offset < 8) :
    ((activeUpdate buffer index bit)[byteIndex]!).toNat.testBit offset =
      ((buffer[byteIndex]!).toNat.testBit offset ||
        (bit && decide (index = 8 * byteIndex + offset))) := by
  rw [activeUpdate, setByte_get _ _ _ _ inside]
  by_cases sameByte : index / 8 = byteIndex
  · simp only [sameByte, ↓reduceIte]
    rw [UInt8.toNat_or, Nat.testBit_or,
      shiftedBool_bit bit ⟨index % 8, by omega⟩ ⟨offset, small⟩]
    have samePosition : (offset = index % 8) ↔ index = 8 * byteIndex + offset := by omega
    simp only [samePosition]
  · have differentPosition : index ≠ 8 * byteIndex + offset := by omega
    simp [sameByte, differentPosition]

/-- The loop invariant is derived from `activeUpdate_bit`: positions already
visited contain their input bit, while every not-yet-visited position is clear. -/
theorem activeLoop_bit (active : List Bool) (count byteIndex offset : Nat)
    (inside : byteIndex < 32) (small : offset < 8) :
    ((activeLoop active count)[byteIndex]!).toNat.testBit offset =
      if 8 * byteIndex + offset < count then
        active[8 * byteIndex + offset]?.getD false
      else false := by
  induction count with
  | zero => simp [activeLoop, zeroWord, getElem!_pos, inside]
  | succ count ih =>
      rw [activeLoop, activeUpdate_bit _ _ _ _ _ (by simpa using inside) small, ih]
      by_cases earlier : 8 * byteIndex + offset < count
      · have different : count ≠ 8 * byteIndex + offset := by omega
        simp [earlier, different, show 8 * byteIndex + offset < count + 1 by omega]
      · by_cases current : count = 8 * byteIndex + offset
        · subst count
          simp
        · simp [earlier, current, show ¬(8 * byteIndex + offset < count + 1) by omega]

/-- Each of the 256 output bits is its supplied logical bit or zero padding.
There is deliberately no upper bound on the input list length. -/
theorem activeFieldsWord_bit (active : List Bool) (byteIndex offset : Nat)
    (inside : byteIndex < 32) (small : offset < 8) :
    ((activeFieldsWord active)[byteIndex]!).toNat.testBit offset =
      active[8 * byteIndex + offset]?.getD false := by
  rw [activeFieldsWord, activeLoop_bit _ _ _ _ inside small]
  by_cases supplied : 8 * byteIndex + offset < active.length
  · simp only [show 8 * byteIndex + offset < min active.length 256 by omega, ↓reduceIte]
  · simp only [show ¬(8 * byteIndex + offset < min active.length 256) by omega, ↓reduceIte]
    rw [List.getElem?_eq_none (by omega)]
    rfl

/-- The native OR-update loop refines upstream packing for arbitrary input
lengths, including inputs longer than the 256-bit destination. -/
theorem activeFieldsWord_eq_upstream (active : List Bool) :
    activeFieldsWord active = Ssz.activeFieldsWord active := by
  apply Array.ext
  · simp [Ssz.activeFieldsWord, Ssz.packBits, Ssz.bytesPerChunk]
  · intro byteIndex inside otherInside
    have smallIndex : byteIndex < 32 := by simpa using inside
    simp only [Ssz.activeFieldsWord, Ssz.packBits, Array.getElem_ofFn]
    apply byte_eq_of_testBit
    intro offset small
    have native := activeFieldsWord_bit active byteIndex offset smallIndex small
    have packed := Packing.packByte_bit active.toArray byteIndex offset small
    rw [byteProbe_eq_testBit _ _ small] at packed
    have packed' : (Ssz.packByte active.toArray byteIndex).toNat.testBit offset =
        active[8 * byteIndex + offset]?.getD false := by
      simpa only [List.getElem?_toArray, Nat.mul_comm] using packed
    simpa [getElem!_pos, smallIndex] using native.trans packed'.symm

/-- Ignoring the input suffix is an exact behavioral property, not a bound
assumed of the caller. -/
theorem activeFieldsWord_truncation (active : List Bool) :
    activeFieldsWord active = activeFieldsWord (active.take 256) := by
  apply Array.ext
  · simp
  · intro byteIndex inside otherInside
    have smallIndex : byteIndex < 32 := by simpa using inside
    apply byte_eq_of_testBit
    intro offset small
    have leftBits := activeFieldsWord_bit active byteIndex offset smallIndex small
    have rightBits := activeFieldsWord_bit (active.take 256) byteIndex offset smallIndex small
    rw [List.getElem?_take_of_lt (by omega)] at rightBits
    simpa [getElem!_pos, smallIndex] using leftBits.trans rightBits.symm

end SszNative.MerkleWords
