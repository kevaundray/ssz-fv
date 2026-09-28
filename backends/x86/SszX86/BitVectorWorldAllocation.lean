import SszX86.BitVectorWorldLocal

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

def outcomeCursor {α : Type} (outcome : NatArithmetic.Outcome α) : BitVec 64 :=
  BitVec.ofNat 64 outcome.used

theorem StableFrame.words {s : MachineData} {address capacity used : BitVec 64} {after : DataMem}
    (frame : StableFrame s address capacity used after) (pointer : Nat) (words : List (BitVec 64))
    (stored : NatMemory.wordsAt (widthLoad s.dmem) pointer words)
    (protectedSpan : Protected s address capacity used pointer (8 * words.length)) :
    NatMemory.wordsAt (widthLoad after) pointer words := by
  intro i
  rw [frame.width (protectedSpan.subrange (8 * i.val) 8 (by have := i.isLt; omega))]
  exact stored i

theorem World.arithmetic {α : Type} {s : MachineData} {saved : Saved} {length : NatOperand}
    {data : Ssz.Bytes} {address capacity initialUsed currentUsed : BitVec 64}
    {writes : List (Nat × Nat)} {before after : DataMem}
    (world : World s saved length data address capacity initialUsed currentUsed writes before)
    (outcome : NatArithmetic.Outcome α)
    (frame : WriteFrame s before after (SszNative.BitVector.allocationWrites outcome))
    (mapping : Mapping.Extends before after)
    (progress : currentUsed.toNat ≤ outcome.used) (bound : outcome.used ≤ capacity.toNat)
    (geometry : ∀ reservation, outcome.allocation = some reservation →
      address.toNat + currentUsed.toNat ≤ reservation.pointer ∧
      reservation.pointer + 8 * outcome.written.length ≤ address.toNat + capacity.toNat)
    (cursor : Mem.loadInt after (s.regs.rbx.toBitVec + 16) 8 = some (outcome.used : Int)) :
    World s saved length data address capacity initialUsed (outcomeCursor outcome)
      (writes ++ SszNative.BitVector.allocationWrites outcome) after := by
  have usedSmall : outcome.used < 2^64 := Nat.lt_of_le_of_lt bound capacity.isLt
  have cursorValue : (outcomeCursor outcome).toNat = outcome.used := by
    simp only [outcomeCursor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt usedSmall]
  apply world.advance frame mapping
  · intro span member
    cases allocated : outcome.allocation with
    | none => simp only [SszNative.BitVector.allocationWrites, allocated, List.not_mem_nil] at member
    | some reservation =>
      simp only [SszNative.BitVector.allocationWrites, allocated, List.mem_singleton] at member
      subst span
      exact geometry reservation allocated
  · simpa only [cursorValue] using progress
  · simpa only [cursorValue] using bound
  · simpa only [cursorValue] using cursor

/-- The full written allocation, including high zero limbs, is protected against
all subsequent body work and all later helper allocations. -/
theorem World.reservation_protected {s : MachineData} {saved : Saved} {length : NatOperand}
    {data : Ssz.Bytes} {address capacity initialUsed currentUsed next : BitVec 64}
    {writes : List (Nat × Nat)} {m : DataMem}
    (world : World s saved length data address capacity initialUsed currentUsed writes m)
    (pointer count : Nat)
    (start : address.toNat + currentUsed.toNat ≤ pointer)
    (finish : pointer + count ≤ address.toNat + next.toNat)
    (nextBound : next.toNat ≤ capacity.toNat) :
    Protected s address capacity next pointer count := by
  have storage := world.physical.arena_bound
  have out : Body.Apart (address.toNat + currentUsed.toNat) (capacity.toNat - currentUsed.toNat)
      s.regs.rdi.toNat 80 := world.physical.arena_output
  have work : Body.Apart (address.toNat + currentUsed.toNat) (capacity.toNat - currentUsed.toNat)
      (workStart s) workSize := world.physical.arena_work
  have header : Body.Apart (address.toNat + currentUsed.toNat) (capacity.toNat - currentUsed.toNat)
      s.regs.rbx.toNat 24 := world.physical.arena_header
  have usedBound := world.physical.used_bound
  constructor
  · omega
  · unfold Body.Apart at out ⊢
    omega
  · unfold Body.Apart at work ⊢
    omega
  · unfold Body.Apart at header ⊢
    omega
  · unfold Body.Apart
    omega

end SszX86.BitVector
