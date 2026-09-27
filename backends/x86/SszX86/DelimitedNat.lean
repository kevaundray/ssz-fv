import SszX86.DelimitedCore
import SszNatABI

namespace SszX86.Delimited
open SszNative

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Pair transport preserves every redundant limb, not merely significant ones. -/
theorem pair_preserved (old new : Nat → Nat → Option Nat) (pointer payload : BitVec 64)
    (value : Nat) (pair : NatMemory.Pair old pointer payload value)
    (limbs : ∀ i, i < payload.toNat → new (pointer.toNat + 8*i) 8 =
      old (pointer.toNat + 8*i) 8) :
    NatMemory.Pair new pointer payload value := by
  rcases pair with small | ⟨words, positive, aligned, space, count, contents, value⟩
  · exact Or.inl small
  · refine Or.inr ⟨words, positive, aligned, space, count, ?_, value⟩
    intro i
    rw [limbs i.val (by rw [count]; exact i.isLt)]
    exact contents i

/-- A call's pushed return word is disjoint from the borrowed operand span. -/
theorem pair_store (m : DataMem) (address : BitVec 64) (stored : Int)
    (pointer payload : BitVec 64) (value : Nat)
    (pair : NatMemory.Pair (UintCodec.widthLoad m) pointer payload value)
    (apart : ∀ i, i < payload.toNat → ∀ j < 8, ∀ k < 8,
      BitVec.ofNat 64 (pointer.toNat + 8*i) + BitVec.ofNat 64 j ≠ address + BitVec.ofNat 64 k) :
    NatMemory.Pair (UintCodec.widthLoad (Mem.storeInt m address 8 stored)) pointer payload value := by
  apply pair_preserved _ _ pointer payload value pair
  intro i hi
  unfold UintCodec.widthLoad
  rw [BoolCodec.load_store_disjoint m _ address 8 8 stored (apart i hi)]

end SszX86.Delimited
