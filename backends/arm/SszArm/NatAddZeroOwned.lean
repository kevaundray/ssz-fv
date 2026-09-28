import SszArm.NatAddZeroMemory

namespace SszArm.NatAdd

open UintCodec (widthLoad)
open Delimited (Protected)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Retaining a prefix of an already-protected borrowed slice needs no new
separation premise. Representation identities come from the shared module. -/
theorem fromWords_owned (writes : List Delimited.Span) (pointer : BitVec 64)
    (words : List (BitVec 64)) (owned : OperandOwned writes (.large pointer words)) :
    OperandOwned writes (SszNative.NatOperand.fromWords pointer words) := by
  have length : (SszNative.Limbs.trim words).length ≤ words.length := by
    rw [SszNative.Limbs.trim_length]
    exact SszNative.Limbs.sigWords_le_length words
  have original : Protected writes pointer.toNat (8 * words.length) := owned
  have retained := original.subspan 0 (8 * (SszNative.Limbs.trim words).length) (by omega)
  cases trimmed : SszNative.Limbs.trim words with
  | nil => simp only [SszNative.NatOperand.fromWords, trimmed, OperandOwned]
  | cons first rest =>
    cases rest with
    | nil => simp only [SszNative.NatOperand.fromWords, trimmed, OperandOwned]
    | cons second rest =>
      simpa only [SszNative.NatOperand.fromWords, trimmed, OperandOwned, Nat.add_zero] using retained

theorem normalized_owned (writes : List Delimited.Span) (operand : SszNative.NatOperand)
    (owned : OperandOwned writes operand) : OperandOwned writes operand.normalized := by
  cases operand with
  | small word =>
    by_cases zero : word = 0#64 <;>
      simp [SszNative.NatOperand.normalized, SszNative.NatOperand.words,
        SszNative.NatOperand.fromWords,
        SszNative.Limbs.trim, zero, OperandOwned]
  | large pointer words => exact fromWords_owned writes pointer words owned

/-- Exact first physical word, used only after the significant count is positive. -/
theorem original_low_word (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64))
    (input : (SszNative.NatOperand.large pointer words).At (widthLoad s))
    (positive : 0 < SszNative.Limbs.sigWords words) :
    read_mem_bytes 8 pointer s = words[0]?.getD 0 := by
  have length := SszNative.Limbs.sigWords_le_length words
  have nonempty : 0 < words.length := by omega
  have stored := input.2.2.2 ⟨0, nonempty⟩
  apply BitVec.eq_of_toNat_eq
  have same := Option.some.inj stored
  simpa [widthLoad, BitVec.setWidth_eq, List.getElem?_eq_getElem nonempty] using same

end SszArm.NatAdd
