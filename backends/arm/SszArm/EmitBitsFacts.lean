import SszArm.EmitMemory
import SszArm.BitVectorValueArithmetic

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Value Packed)
open SszNative (NatOperand)
open BitVector.ValueTail (countLow countHigh quotientWord)

def IsList : Desc → Prop
  | .bitList _ | .progressiveBitList _ => True
  | _ => False

def IsBits : Desc → Prop
  | .bitVector _ | .bitList _ | .progressiveBitList _ => True
  | _ => False

theorem list_size {desc : Desc} {bits : Packed} {size : Nat}
    (kind : IsList desc)
    (expected : SszNative.Serialize.expectedSize desc (.bits bits) = .ok size) :
    size = bits.count.toNat / 8 + 1 := by
  cases desc with
  | bitList limit =>
    simp only [SszNative.Serialize.expectedSize] at expected
    split at expected <;> simp_all
  | progressiveBitList limit =>
    cases limit with
    | none => simpa only [SszNative.Serialize.expectedSize, Except.ok.injEq] using expected.symm
    | some cap =>
      simp only [SszNative.Serialize.expectedSize] at expected
      split at expected <;> simp_all
  | _ => cases kind

theorem vector_size {length : NatOperand} {bits : Packed} {size : Nat}
    (expected : SszNative.Serialize.expectedSize (.bitVector length) (.bits bits) = .ok size) :
    size = bits.bytes.size := by
  simp only [SszNative.Serialize.expectedSize] at expected
  split at expected <;> simp_all

theorem full_le_size {desc : Desc} {bits : Packed} {size : Nat}
    (kind : IsBits desc)
    (expected : SszNative.Serialize.expectedSize desc (.bits bits) = .ok size) :
    bits.count.toNat / 8 ≤ size := by
  cases desc with
  | bitVector length => have h := vector_size expected; have hsize := bits.sized; omega
  | bitList limit => have h := list_size (desc := .bitList limit) trivial expected; omega
  | progressiveBitList limit =>
    have h := list_size (desc := .progressiveBitList limit) trivial expected; omega
  | _ => cases kind

/-- Physical backing length, not the descriptor's logical cap, bounds the high
word used by the real LSR/ORR lowering. Counts need not fit in a single word. -/
theorem count_quotient (bits : Packed) (physical : bits.bytes.size < 2^64) :
    (quotientWord (countLow bits.count) (countHigh bits.count)).toNat = bits.count.toNat / 8 ∧
    (countLow bits.count &&& 7#64).toNat = bits.count.toNat % 8 := by
  have words := BitVector.ValueTail.count_words bits.count
  have lowBound := (countLow bits.count).isLt
  have sized := bits.sized
  have highBound : (countHigh bits.count).toNat < 8 := by omega
  have quotient := BitVector.ValueTail.quotientWord_nat
    (countLow bits.count) (countHigh bits.count) highBound
  have remainder := BitVector.ValueTail.mask7_nat (countLow bits.count)
  constructor <;> omega

theorem backing_guards (bits : Packed) :
    bits.count.toNat / 8 ≤ bits.bytes.size ∧
    (bits.count.toNat % 8 = 0 → bits.bytes.size = bits.count.toNat / 8) ∧
    (bits.count.toNat % 8 ≠ 0 → bits.bytes.size = bits.count.toNat / 8 + 1) := by
  have sized := bits.sized
  omega

theorem list_guards {s : ArmState} {args : Args} {desc : Desc} {bits : Packed} {size : Nat}
    (kind : IsList desc) (owned : Owned s args desc (.bits bits) size) :
    bits.count.toNat / 8 < args.capacity.toNat ∧
    bits.count.toNat / 8 + 1 < 2^64 := by
  have sizeEq := list_size kind owned.expected
  have fitting := owned.fitting
  have representable := owned.representable
  omega

theorem vector_tail_guard {s : ArmState} {args : Args} {length : NatOperand}
    {bits : Packed} {size : Nat}
    (owned : Owned s args (.bitVector length) (.bits bits) size)
    (hasTail : bits.count.toNat % 8 ≠ 0) :
    bits.count.toNat / 8 < args.capacity.toNat := by
  have sizeEq := vector_size owned.expected
  have backing := (backing_guards bits).2.2 hasTail
  have fitting := owned.fitting
  omega

/-- The memcpy prefix borrows only original backing and writes only the emitted
prefix. Empty slices need no address separation. -/
theorem copy_bounds {s : ArmState} {args : Args} {desc : Desc} {bits : Packed} {size : Nat}
    (kind : IsBits desc) (owned : Owned s args desc (.bits bits) size) :
    args.output.toNat + bits.count.toNat / 8 ≤ 2^64 ∧
    (read_mem_bytes 8 (args.value + 16#64) s).toNat + bits.count.toNat / 8 ≤ 2^64 ∧
    Memcpy.Disjoint args.output (read_mem_bytes 8 (args.value + 16#64) s)
      (bits.count.toNat / 8) := by
  have fullSize := full_le_size kind owned.expected
  have fitting := owned.fitting
  have outputBound := owned.outputBound
  have backingBound := owned.value_at.2.2.1
  have backingSize := (backing_guards bits).1
  refine ⟨by omega, by omega, ?_⟩
  unfold Memcpy.Disjoint
  by_cases empty : bits.count.toNat / 8 = 0
  · omega
  · have sizeNonzero : size ≠ 0 := by omega
    have backingProtected := owned.backingOwned
      ((read_mem_bytes 8 (args.value + 16#64) s).toNat, bits.bytes.size)
      (by simp [backingSpan])
    rcases backingProtected with zero | separate
    · omega
    · have apart := separate (args.output.toNat, size)
        (by simp [writesFor, sizeNonzero])
      simp only at apart
      omega

end SszArm.Emit.Bits
