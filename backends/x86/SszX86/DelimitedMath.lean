import SszX86.DelimitedCore

namespace SszX86.Delimited
open SszNative.BitView

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Exact native count arithmetic, including lengths with bit 63 set. -/
theorem count_words (length highest : Nat) (positive : 0 < length)
    (physical : length < 2^64) (byte : highest < 8) :
    (8 * (length - 1) + highest) / 2^64 = (length - 1) / 2^61 ∧
    (8 * (length - 1) + highest) % 2^64 =
      ((BitVec.ofNat 64 highest) + (BitVec.ofNat 64 (length - 1)) * 8).toNat ∧
    8 * (length - 1) + highest < 2^67 := by
  constructor
  · omega
  constructor
  · simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.ofNat_eq_ofNat,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  · omega

/-- A two-word `from_u128` reservation is needed exactly at the linked threshold. -/
theorem count_large (length highest : Nat) (byte : highest < 8) :
    2^64 ≤ 8 * (length - 1) + highest ↔ 2^61 + 1 ≤ length := by omega

/-- The native checked byte-length reconstruction can never take reason 32770.
The proof uses only physical usize representability, never a signed-length bound. -/
theorem retained_checked (length highest : Nat) (positive : 0 < length)
    (physical : length < 2^64) (byte : highest < 8) :
    let retained := if highest = 0 then length - 1 else length
    let extra := if highest = 0 then 0 else 1
    length - 1 + extra = retained ∧
    length - 1 + extra < 2^64 ∧
    (8 * (length - 1) + highest + 7) / 8 = retained := by
  dsimp only
  by_cases hz : highest = 0 <;> simp only [hz, ↓reduceIte] <;> omega

/-- The XOR lowering tests exactly whether the delimiter is byte-aligned. -/
theorem highest_xor (highest : Nat) (byte : highest < 8) :
    (((BitVec.ofNat 32 highest) ^^^ 7#32).setWidth 8 = 7#8) ↔ highest = 0 := by
  have cases : highest = 0 ∨ highest = 1 ∨ highest = 2 ∨ highest = 3 ∨
      highest = 4 ∨ highest = 5 ∨ highest = 6 ∨ highest = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Every shift traversed by the lowered BSR loop, as a finite byte certificate. -/
def HighestCertificate (byte : UInt8) : Prop :=
  byte ≠ 0 →
  ((byte.toBitVec.setWidth 32 >>> (Ssz.highestBit byte + 1)) = 0#32) ∧
  ∀ i : Fin 8, i.val ≤ Ssz.highestBit byte →
    byte.toBitVec.setWidth 32 >>> i.val ≠ 0#32

set_option maxRecDepth 4096 in
theorem highest_certificate (byte : UInt8) : HighestCertificate byte := by
  unfold HighestCertificate
  cases byte with
  | ofBitVec byte =>
    cases byte with
    | ofFin byte => revert byte; decide

end SszX86.Delimited
