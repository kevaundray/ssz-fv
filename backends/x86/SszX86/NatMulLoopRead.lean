import SszX86.NatMulProductStep
import SszX86.NatAddCarryMath

namespace SszX86.NatMul.Product
open SszNative
open UintCodec

/-- Current memory observations at a moving limb index, with no future write premise. -/
def ReadAt (m : DataMem) (pointer : BitVec 64) (index : Nat)
    (words : List (BitVec 64)) : Prop :=
  ∀ j : Fin words.length, Mem.loadInt m (pointer + BitVec.ofNat 64 (8 * (index + j.val))) 8 =
    some (words[j].toNat : Int)

theorem ReadAt.head {m : DataMem} {pointer : BitVec 64} {index : Nat}
    {limb : BitVec 64} {words : List (BitVec 64)} (read : ReadAt m pointer index (limb :: words)) :
    Mem.loadInt m (pointer + BitVec.ofNat 64 (8 * index)) 8 = some (limb.toNat : Int) := by
  simpa using read ⟨0, by simp⟩

theorem ReadAt.tail {m : DataMem} {pointer : BitVec 64} {index : Nat}
    {limb : BitVec 64} {words : List (BitVec 64)} (read : ReadAt m pointer index (limb :: words)) :
    ReadAt m pointer (index+1) words := by
  intro j
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    read ⟨j.val+1, by have := j.isLt; simp⟩

/-- A store before the unread suffix preserves each of its actual memory loads. -/
theorem ReadAt.store_before {m : DataMem} {pointer : BitVec 64} {index : Nat}
    {words : List (BitVec 64)} (read : ReadAt m pointer (index+1) words)
    (span : pointer.toNat + 8 * (index + 1 + words.length) ≤ 2^64) (limb : BitVec 64) :
    ReadAt (Mem.storeInt m (pointer + BitVec.ofNat 64 (8*index)) 8 limb.toInt)
      pointer (index+1) words := by
  intro j
  rw [BoolCodec.load_store_disjoint]
  · exact read j
  · intro a ha b hb
    rw [memmove_addr_add, memmove_addr_add]
    intro same
    have inject := memmove_addr_injective pointer (8*(index+1+words.length))
      (8*(index+1+j.val)+a) (8*index+b) span
      (by have := j.isLt; omega) (by have := j.isLt; omega) same
    omega

/-- Source and destination may each alias other immutable inputs, but not each other. -/
theorem ReadAt.store_disjoint {m : DataMem} {source dst : BitVec 64}
    {index start capacity sourceCapacity : Nat} {words : List (BitVec 64)}
    (read : ReadAt m source start words)
    (apart : Large.Disjoint source dst sourceCapacity capacity)
    (sourceBound : 8*(start+words.length) ≤ sourceCapacity)
    (writeBound : 8*(index+1) ≤ capacity) (limb : BitVec 64) :
    ReadAt (Mem.storeInt m (dst + BitVec.ofNat 64 (8*index)) 8 limb.toInt)
      source start words := by
  intro j
  rw [BoolCodec.load_store_disjoint]
  · exact read j
  · intro a ha b hb
    rw [memmove_addr_add, memmove_addr_add]
    exact apart (8*(start+j.val)+a) (by have := j.isLt; omega)
      (8*index+b) (by omega)

theorem ReadAt.of_wordsAt {m : DataMem} {pointer : BitVec 64}
    {words : List (BitVec 64)} (read : NatMemory.wordsAt (widthLoad m) pointer.toNat words) :
    ReadAt m pointer 0 words := by
  intro j
  have loaded := widthLoad_eq m _ _ _ (read j)
  simpa [width_address] using loaded

end SszX86.NatMul.Product
