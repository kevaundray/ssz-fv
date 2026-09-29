import SszArm.NatMulWordReserveLarge
import SszArm.NatMulWordReserveCommit
import SszArm.NatToU128Finish
import SszNatMul

namespace SszArm.NatMulWord.Reserve

open SszNative (NatOperand)
open SszNative.NatArithmetic

/-- The checked runWord branch selected by the real high-product registers. -/
theorem wide_runWord (operand : NatOperand) (factor low high : BitVec 64)
    (address capacity used : Nat) (nonzero : factor ≠ 0) (notone : factor ≠ 1)
    (small : operand.wordCount ≤ 1)
    (product : SszNative.NatMul.wordProduct operand factor = high ++ low)
    (wide : high ≠ 0#64) :
    SszNative.NatMul.runWord operand factor address capacity used =
      match SszNative.Arena.reserve address capacity used 2 with
      | none => unchanged used (.error .scratchExhausted)
      | some reservation => committed reservation [low, high] := by
  rw [SszNative.NatMul.runWord_small operand factor address capacity used nonzero notone small,
    SszNative.NatArithmetic.fromWide, product]
  have large : ¬ (high ++ low).toNat < 2^64 := by
    rw [NatToU128.append_toNat]
    have hp : 0 < high.toNat := by
      have hz : high.toNat ≠ 0 := by intro h; apply wide; apply BitVec.eq_of_toNat_eq; simpa using h
      omega
    omega
  have lo : (high ++ low).setWidth 64 = low :=
    BitVec.eq_of_toNat_eq (NatToU128.append_low high low)
  have hi : ((high ++ low) >>> (64 : Nat)).setWidth 64 = high :=
    BitVec.eq_of_toNat_eq (NatToU128.append_high high low)
  simp only [large, ↓reduceIte, lo, hi]
  rfl

theorem wide_failure_runWord (operand : NatOperand) (factor low high : BitVec 64)
    (address capacity used : Nat) (nonzero : factor ≠ 0) (notone : factor ≠ 1)
    (small : operand.wordCount ≤ 1)
    (product : SszNative.NatMul.wordProduct operand factor = high ++ low)
    (wide : high ≠ 0#64) (failed : SszNative.Arena.reserve address capacity used 2 = none) :
    SszNative.NatMul.runWord operand factor address capacity used =
      unchanged used (.error .scratchExhausted) := by
  rw [wide_runWord operand factor low high address capacity used nonzero notone small product wide, failed]

theorem wide_success_runWord (operand : NatOperand) (factor low high : BitVec 64)
    (address capacity used : Nat) (nonzero : factor ≠ 0) (notone : factor ≠ 1)
    (small : operand.wordCount ≤ 1)
    (product : SszNative.NatMul.wordProduct operand factor = high ++ low)
    (wide : high ≠ 0#64) (checks : SszNative.Arena.Checks address capacity used 2) :
    SszNative.NatMul.runWord operand factor address capacity used =
      committed ⟨address + SszNative.Arena.start address used, SszNative.Arena.finish address used 2⟩
        [low, high] := by
  rw [wide_runWord operand factor low high address capacity used nonzero notone small product wide]
  have reserved := (SszNative.Arena.reserve_eq_some_iff_checks address capacity used 2 (by decide)
    ⟨address + SszNative.Arena.start address used, SszNative.Arena.finish address used 2⟩).2 ⟨checks, rfl⟩
  rw [reserved]

/-- Both native error PCs implement exactly the checked scratch-exhaustion
outcome; usize overflow and all reserve failures are kept distinct in LargePost. -/
theorem large_failure_runWord (operand : NatOperand) (factor : BitVec 64)
    (s t : ArmState) (base address capacity used : BitVec 64)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (large : 1 < operand.wordCount)
    (count : (r (.GPR 9#5) s).toNat = operand.wordCount)
    (failed : ((r (.GPR 9#5) s).toNat + 1 = 2^64 ∧ read_pc t = base + 1632#64) ∨
      ((r (.GPR 9#5) s).toNat + 1 < 2^64 ∧
        SszNative.Arena.reserve address.toNat capacity.toNat used.toNat
          ((r (.GPR 9#5) s).toNat + 1) = none ∧ read_pc t = base + 1264#64)) :
    SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
      unchanged used.toNat (.error .scratchExhausted) := by
  rw [SszNative.NatMul.runWord_large operand factor _ _ _ nonzero notone large]
  rw [count] at failed
  rcases failed with ⟨overflow, _⟩ | ⟨fits, exhausted, _⟩
  · simp only [show ¬ operand.wordCount + 1 < 2^64 by omega, ↓reduceIte]
  · simp only [fits, ↓reduceIte, exhausted]

theorem large_success_runWord (operand : NatOperand) (factor : BitVec 64)
    (s : ArmState) (address capacity used : BitVec 64)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (large : 1 < operand.wordCount)
    (count : (r (.GPR 9#5) s).toNat = operand.wordCount)
    (fits : (r (.GPR 9#5) s).toNat + 1 < 2^64)
    (checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat
      ((r (.GPR 9#5) s).toNat + 1)) :
    SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
      committed ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
          SszNative.Arena.finish address.toNat used.toNat (operand.wordCount + 1)⟩
        (SszNative.NatMul.wordWritten operand factor) := by
  rw [count] at fits checks
  rw [SszNative.NatMul.runWord_large operand factor _ _ _ nonzero notone large, if_pos fits]
  have reserved := (SszNative.Arena.reserve_eq_some_iff_checks address.toNat capacity.toNat used.toNat
    (operand.wordCount + 1) (by omega)
    ⟨address.toNat + SszNative.Arena.start address.toNat used.toNat,
      SszNative.Arena.finish address.toNat used.toNat (operand.wordCount + 1)⟩).2 ⟨checks, rfl⟩
  rw [reserved]

/-- Only the physically represented input extent bounds the significant count.
The immutable logical runWord model itself remains unrestricted. -/
theorem physical_count_add_one (s : ArmState) (operand : NatOperand)
    (input : operand.At (UintCodec.widthLoad s)) : operand.wordCount + 1 < 2^64 := by
  have significant := SszNative.Limbs.sigWords_le_length operand.words
  change operand.wordCount ≤ operand.words.length at significant
  cases operand with
  | small word =>
    simp only [NatOperand.words, List.length_cons, List.length_nil] at significant
    omega
  | large pointer words =>
    have physical := input.2.2.1
    simp only [NatOperand.words] at significant
    omega

theorem physical_usize_error_unreachable (s : ArmState) (operand : NatOperand)
    (input : operand.At (UintCodec.widthLoad s))
    (count : (r (.GPR 9#5) s).toNat = operand.wordCount) :
    (r (.GPR 9#5) s).toNat + 1 ≠ 2^64 := by
  have bound := physical_count_add_one s operand input
  rw [count]
  omega

end SszArm.NatMulWord.Reserve
