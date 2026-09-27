import SszArm.DelimitedImpl
import SszBitView
import SszArena

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open SszNative.BitView

/-- The loop introduced by CLZ lowering shifts this exact 32-bit value. -/
def clzInput (byte : UInt8) : BitVec 32 := BitVec.ofNat 32 byte.toNat <<< 24

/-- Nonzero byte inputs take 25 + highestBit iterations; every intermediate
CBNZ is justified, not replaced by an assumed CLZ instruction. -/
theorem clz_byte_facts (byte : UInt8) (nonzero : byte ≠ 0) :
    25 + Ssz.highestBit byte ≤ 32 ∧
    clzInput byte >>> (25 + Ssz.highestBit byte) = 0#32 ∧
    (∀ i : Fin 32, i.val < 25 + Ssz.highestBit byte →
      clzInput byte >>> i.val ≠ 0#32) := by
  cases byte with
  | ofBitVec byte =>
    cases byte with
    | ofFin byte => revert byte; decide

/-- XOR 7 turns the lowering's leading-zero count into the delimiter bit index. -/
theorem clz_highest (byte : UInt8) :
    (BitVec.ofNat 32 (32 - (25 + Ssz.highestBit byte)) ^^^ 7#32).toNat =
      Ssz.highestBit byte := by
  cases byte with
  | ofBitVec byte =>
    cases byte with
    | ofFin byte => revert byte; decide

/-- This is precisely the native checked byte-count reconstruction. Physical
nonwrapping length, not an isize restriction, rules out BadRepresentation. -/
theorem representation_check (length highest : Nat)
    (nonempty : 0 < length) (physical : length < 2^64) (bit : highest < 8) :
    let extra := if highest = 0 then 0 else 1
    let retained := if highest = 0 then length - 1 else length
    length - 1 + extra < 2^64 ∧ length - 1 + extra = retained ∧
      retained = (8 * (length - 1) + highest + 7) / 8 := by
  dsimp
  by_cases zero : highest = 0 <;> simp only [zero, ↓reduceIte] <;> omega

/-- Count high bits come exclusively from the logical full-byte prefix. -/
theorem count_high (length highest : Nat) (bit : highest < 8) :
    (8 * (length - 1) + highest) / 2^64 = (length - 1) / 2^61 := by
  omega

theorem count_low_high (length highest : Nat)
    (physical : length < 2^64) (bit : highest < 8) :
    let count := 8 * (length - 1) + highest
    count < 2^67 ∧ count % 2^64 + 2^64 * (count / 2^64) = count ∧
      count / 2^64 < 8 := by
  dsimp
  omega

/-- The machine compares length against 2^61 + 1 before consulting Option Nat.
Consequently None does not avoid a required two-word allocation. -/
theorem count_needs_scratch (length highest : Nat) (bit : highest < 8) :
    2^64 ≤ 8 * (length - 1) + highest ↔ 2^61 + 1 ≤ length := by
  omega

/-- Exact two-word reservation, retaining every native overflow guard. -/
theorem reserve_count (base capacity used : Nat) :
    SszNative.Arena.reserve base capacity used 2 =
      if SszNative.Arena.Checks base capacity used 2 then
        some ⟨SszNative.Arena.aligned (base + used),
          SszNative.Arena.start base used + 16⟩
      else none := by
  by_cases checks : SszNative.Arena.Checks base capacity used 2 <;>
    simp [SszNative.Arena.reserve, SszNative.Arena.finish,
      SszNative.Arena.start_pointer, checks]

/-- A failed allocation has no commit. The caller retains its exact old cursor;
success consumes only alignment padding and the two u64 limbs. -/
theorem reserve_count_cursor (base capacity used : Nat) (allocation : SszNative.Arena.Reservation)
    (success : SszNative.Arena.reserve base capacity used 2 = some allocation) :
    allocation.pointer = SszNative.Arena.aligned (base + used) ∧
      allocation.used = used + SszNative.Arena.padding (base + used) + 16 := by
  obtain ⟨_, rfl⟩ :=
    (SszNative.Arena.reserve_eq_some_iff_checks base capacity used 2 (by decide) allocation).1 success
  constructor
  · exact SszNative.Arena.start_pointer base used
  · rfl

end SszArm.Delimited
