import SszArm.DispatchEntry
import SszArm.ByteViewBody
import SszArm.UintBody
import SszNatABI

namespace SszArm.Dispatch.Scalar

open UintCodec (widthLoad)

def pointer (s : ArmState) := read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s
def payload (s : ArmState) := read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s

/-- Original physical scalar arguments, including an arbitrary native Nat pair.
The read-only input, descriptor, and limbs may alias one another or used arena.
There is no capacity bound and no future body ownership premise. -/
structure Owned (s : ArmState) (kind : Kind) (capacity : Nat) (data : Ssz.Bytes) : Prop where
  entry : EntryOwned s kind
  stackLow : 384 ≤ (r (.GPR 31#5) s).toNat
  outputBound : (r (.GPR 0#5) s).toNat + 80 ≤ 2^64
  outputStack : (r (.GPR 0#5) s).toNat + 80 ≤ (r (.GPR 31#5) s).toNat - 384 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat
  length : (r (.GPR 3#5) s).toNat = data.size
  inputBound : (r (.GPR 2#5) s).toNat + data.size ≤ 2^64
  input : SszNative.ByteView.BytesAt (widthLoad s) (r (.GPR 2#5) s).toNat data
  inputOutput : data.size = 0 ∨ (r (.GPR 2#5) s).toNat + data.size ≤ (r (.GPR 0#5) s).toNat ∨
    (r (.GPR 0#5) s).toNat + 76 ≤ (r (.GPR 2#5) s).toNat
  inputStack : data.size = 0 ∨ (r (.GPR 2#5) s).toNat + data.size ≤ (r (.GPR 31#5) s).toNat - 384 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 2#5) s).toNat
  descriptorBound : (r (.GPR 1#5) s).toNat + 24 ≤ 2^64
  descriptorOutput : (r (.GPR 1#5) s).toNat + 24 ≤ (r (.GPR 0#5) s).toNat ∨
    (r (.GPR 0#5) s).toNat + 76 ≤ (r (.GPR 1#5) s).toNat
  descriptorStack : (r (.GPR 1#5) s).toNat + 24 ≤ (r (.GPR 31#5) s).toNat - 384 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 1#5) s).toNat
  pair : SszNative.NatMemory.Pair (widthLoad s) (pointer s) (payload s) capacity
  limbsOutput : pointer s ≠ 0#64 → payload s ≠ 0#64 →
    (pointer s).toNat + 8 * (payload s).toNat ≤ (r (.GPR 0#5) s).toNat ∨
      (r (.GPR 0#5) s).toNat + 76 ≤ (pointer s).toNat
  limbsStack : pointer s ≠ 0#64 → payload s ≠ 0#64 →
    (pointer s).toNat + 8 * (payload s).toNat ≤ (r (.GPR 31#5) s).toNat - 384 ∨
      (r (.GPR 31#5) s).toNat ≤ (pointer s).toNat

theorem Owned.header {s : ArmState} {kind : Kind} {capacity : Nat} {data : Ssz.Bytes}
    (owned : Owned s kind capacity data) (offset : Nat) (within : offset + 8 ≤ 24) :
    read_mem_bytes 8 (r (.GPR 1#5) (entered s kind) + BitVec.ofNat 64 offset) (entered s kind) =
      read_mem_bytes 8 (r (.GPR 1#5) s + BitVec.ofNat 64 offset) s := by
  rw [entered_reg s kind 1#5 (by decide) (by decide) (by decide)]
  apply entered_read s kind owned.entry.stackLow
  · have bound := owned.descriptorBound
    bv_omega
  · have bound := owned.descriptorBound
    have separate := owned.descriptorStack
    bv_omega

theorem Owned.entered_input {s : ArmState} {kind : Kind} {capacity : Nat} {data : Ssz.Bytes}
    (owned : Owned s kind capacity data) :
    SszNative.ByteView.BytesAt (widthLoad (entered s kind)) (r (.GPR 2#5) s).toNat data := by
  intro i within
  have read := entered_read s kind owned.entry.stackLow
    (BitVec.ofNat 64 ((r (.GPR 2#5) s).toNat + i)) 1
    (by have bound := owned.inputBound; bv_omega)
    (by have bound := owned.inputBound; have separate := owned.inputStack; bv_omega)
  simpa only [widthLoad, read] using owned.input i within

theorem Owned.entered_pair {s : ArmState} {kind : Kind} {capacity : Nat} {data : Ssz.Bytes}
    (owned : Owned s kind capacity data) :
    SszNative.NatMemory.Pair (widthLoad (entered s kind)) (pointer s) (payload s) capacity := by
  rcases owned.pair with small | ⟨words, positive, aligned, bound, count, memory, value⟩
  · exact Or.inl small
  · refine Or.inr ⟨words, positive, aligned, bound, count, ?_, value⟩
    intro i
    have within := i.isLt
    have nonzero : pointer s ≠ 0#64 := by intro zero; simp only [zero, BitVec.toNat_ofNat] at positive; omega
    have nonempty : payload s ≠ 0#64 := by intro zero; simp only [zero, BitVec.toNat_ofNat] at count; omega
    have separate := owned.limbsStack nonzero nonempty
    have read := entered_read s kind owned.entry.stackLow
      (BitVec.ofNat 64 ((pointer s).toNat + 8 * i.val)) 8
      (by bv_omega) (by bv_omega)
    simpa only [widthLoad, read] using memory i

theorem Owned.byte_separated {s : ArmState} {kind : Kind} {capacity : Nat} {data : Ssz.Bytes}
    (owned : Owned s kind capacity data) : ByteView.Tail.Separated (entered s kind) := by
  have low := owned.stackLow
  have output := owned.outputBound
  have separate := owned.outputStack
  constructor <;>
    simp only [entered_sp, entered_reg _ _ 0#5 (by decide) (by decide) (by decide), bodySP] <;>
    bv_omega

theorem Owned.uint_separated {s : ArmState} {kind : Kind} {capacity : Nat} {data : Ssz.Bytes}
    (owned : Owned s kind capacity data) : UintCodec.Tail.Separated (entered s kind) := by
  have low := owned.stackLow
  have output := owned.outputBound
  have separate := owned.outputStack
  constructor <;>
    simp only [entered_sp, entered_reg _ _ 0#5 (by decide) (by decide) (by decide), bodySP] <;>
    bv_omega

theorem Owned.byte_input {s : ArmState} {kind : Kind} {capacity : Nat} {data : Ssz.Bytes}
    (owned : Owned s kind capacity data) : ByteView.Tail.Input (entered s kind) data := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using owned.length
  · simpa using owned.inputBound
  · simpa using owned.entered_input
  · have low := owned.stackLow
    have out := owned.inputOutput
    have stack := owned.inputStack
    simp only [entered_sp, entered_reg _ _ 0#5 (by decide) (by decide) (by decide),
      entered_reg _ _ 2#5 (by decide) (by decide) (by decide), bodySP]
    bv_omega

theorem Owned.byte_pair {s : ArmState} {kind : Kind} {capacity : Nat} {data : Ssz.Bytes}
    (owned : Owned s kind capacity data) :
    ByteView.Tail.NatPair (entered s kind) (pointer s) (payload s) capacity := by
  rcases owned.entered_pair with small | ⟨words, positive, aligned, bound, count, memory, value⟩
  · exact Or.inl small
  · refine Or.inr ⟨words, positive, aligned, bound, count, memory, value, ?_⟩
    by_cases empty : words = []
    · exact Or.inl empty
    · right
      have nonzero : pointer s ≠ 0#64 := by intro zero; simp only [zero, BitVec.toNat_ofNat] at positive; omega
      have nonempty : payload s ≠ 0#64 := by
        intro zero
        have length : words.length = 0 := by simpa only [zero, BitVec.toNat_ofNat] using count.symm
        exact empty (List.eq_nil_of_length_eq_zero length)
      have out := owned.limbsOutput nonzero nonempty
      have stack := owned.limbsStack nonzero nonempty
      have low := owned.stackLow
      simp only [entered_sp, entered_reg _ _ 0#5 (by decide) (by decide) (by decide), bodySP]
      bv_omega

theorem Owned.uint_pair {s : ArmState} {kind : Kind} {capacity : Nat} {data : Ssz.Bytes}
    (owned : Owned s kind capacity data) :
    UintCodec.Tail.NatPair (entered s kind) (pointer s) (payload s) capacity := by
  rcases owned.entered_pair with small | ⟨words, positive, aligned, bound, count, memory, value⟩
  · exact Or.inl small
  · refine Or.inr ⟨words, positive, aligned, bound, count, memory, value, ?_⟩
    by_cases empty : words = []
    · exact Or.inl empty
    · right
      have nonzero : pointer s ≠ 0#64 := by intro zero; simp only [zero, BitVec.toNat_ofNat] at positive; omega
      have nonempty : payload s ≠ 0#64 := by
        intro zero
        have length : words.length = 0 := by simpa only [zero, BitVec.toNat_ofNat] using count.symm
        exact empty (List.eq_nil_of_length_eq_zero length)
      have out := owned.limbsOutput nonzero nonempty
      have stack := owned.limbsStack nonzero nonempty
      have low := owned.stackLow
      simp only [entered_sp, entered_reg _ _ 0#5 (by decide) (by decide) (by decide), bodySP]
      bv_omega

theorem Owned.byte_owned {s : ArmState} {kind : Kind} {capacity : Nat} {data : Ssz.Bytes}
    (owned : Owned s kind capacity data) : ByteView.Owned (entered s kind) capacity data := by
  refine ⟨owned.byte_separated, owned.byte_input, ?_, ?_, ?_, ?_⟩
  · simpa using owned.descriptorBound
  · simpa using owned.descriptorOutput
  · have low := owned.stackLow
    have stack := owned.descriptorStack
    simp only [entered_sp, entered_reg _ _ 1#5 (by decide) (by decide) (by decide), bodySP]
    bv_omega
  · rw [owned.header 8 (by decide), owned.header 16 (by decide)]
    exact owned.byte_pair

end SszArm.Dispatch.Scalar
