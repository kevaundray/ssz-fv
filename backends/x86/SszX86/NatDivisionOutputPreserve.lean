import SszX86.NatDivisionOutputMemory
import SszX86.DelimitedMemory

namespace SszX86.NatDivision
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- An output-only byte frame transports any disjoint physical read. -/
theorem result_frame_load (before after : DataMem) (out : BitVec 64)
    (frame : ∀ address, (∀ i < 68, address ≠ out + BitVec.ofNat 64 i) →
      after.get? address = before.get? address)
    (outputBound : out.toNat + 68 ≤ 2^64)
    (p n off count : Nat) (bound : p+n ≤ 2^64)
    (apart : Body.Apart p n out.toNat 68) (inside : off+count ≤ n) :
    widthLoad after (p+off) count = widthLoad before (p+off) count := by
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  apply frame
  intro j hj same
  have leftBound : p+off+i < 2^64 := by omega
  have rightBound : out.toNat+j < 2^64 := by omega
  have addresses := congrArg BitVec.toNat same
  rw [← BitVec.ofNat_add] at addresses
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound,
    BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2^64 by omega),
    Nat.mod_eq_of_lt rightBound] at addresses
  unfold Body.Apart at apart
  omega

/-- Every written quotient limb survives publication, including high zeros that
fromWords omits from the returned quotient representation. -/
theorem result_success_preserves_words (m : DataMem)
    (out pointer payload remainder : BitVec 64) (address : Nat)
    (words : List (BitVec 64))
    (outputBound : out.toNat + 68 ≤ 2^64)
    (bound : address + 8*words.length ≤ 2^64)
    (apart : Body.Apart address (8*words.length) out.toNat 68)
    (stored : NatMemory.wordsAt (widthLoad m) address words) :
    NatMemory.wordsAt (widthLoad (resultSuccessMem m out pointer payload remainder)) address words := by
  intro i
  rw [result_frame_load m (resultSuccessMem m out pointer payload remainder) out
    (result_success_mem_frame m out pointer payload remainder) outputBound
    address (8*words.length) (8*i.val) 8 bound apart (by omega)]
  exact stored i

/-- Borrowed original representations are preserved verbatim, without trimming
redundant high limbs or replacing the caller's pointer. -/
theorem result_frame_operand (before after : DataMem) (out : BitVec 64)
    (frame : ∀ address, (∀ i < 68, address ≠ out + BitVec.ofNat 64 i) →
      after.get? address = before.get? address)
    (outputBound : out.toNat+68 ≤ 2^64) (operand : NatOperand)
    (apart : ∀ pointer words, operand = .large pointer words →
      Body.Apart pointer.toNat (8*words.length) out.toNat 68)
    (stored : operand.At (widthLoad before)) : operand.At (widthLoad after) := by
  cases operand with
  | small limb => trivial
  | large pointer words =>
    obtain ⟨positive, aligned, bound, limbs⟩ := stored
    refine ⟨positive, aligned, bound, ?_⟩
    intro i
    rw [result_frame_load before after out frame outputBound
      pointer.toNat (8*words.length) (8*i.val) 8 bound (apart pointer words rfl) (by omega)]
    exact limbs i

end SszX86.NatDivision
