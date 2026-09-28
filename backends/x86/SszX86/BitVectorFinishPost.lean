import SszX86.BitVectorFinishMemory
import SszX86.BitVectorWorld

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem finish_protected_width (s : MachineData) (before after : DataMem)
    (address capacity used : BitVec 64) (p n : Nat)
    (frame : RegionsFrame before after (finishRegions s))
    (region : Protected s address capacity used p n) :
    widthLoad after p n = widthLoad before p n := by
  apply frame.width p n region.bound
  intro span member
  simp only [finishRegions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact region.output
  · exact region.work

/-- Final fixed stores retain all allocated words, not merely the normalized Nat. -/
theorem finish_written (s : MachineData) (before after : DataMem)
    (address capacity used : BitVec 64) (outcome : SszNative.BitVector.Outcome)
    (frame : RegionsFrame before after (finishRegions s))
    (stored : outcome.writtenAt (widthLoad before))
    (protectedWrites : ∀ span ∈ outcome.writes,
      Protected s address capacity used span.1 span.2) :
    outcome.writtenAt (widthLoad after) := by
  have words (pointer : Nat) (limbs : List (BitVec 64))
      (region : Protected s address capacity used pointer (8 * limbs.length))
      (storedWords : NatMemory.wordsAt (widthLoad before) pointer limbs) :
      NatMemory.wordsAt (widthLoad after) pointer limbs := by
    intro i
    rw [finish_protected_width s before after address capacity used _ _ frame
      (region.subrange (8 * i.val) 8 (by have := i.isLt; omega))]
    exact storedWords i
  have allocation {α : Type} (allocatedOutcome : NatArithmetic.Outcome α)
      (included : ∀ span ∈ SszNative.BitVector.allocationWrites allocatedOutcome,
        span ∈ outcome.writes)
      (allocatedAt : SszNative.BitVector.allocationAt (widthLoad before) allocatedOutcome) :
      SszNative.BitVector.allocationAt (widthLoad after) allocatedOutcome := by
    intro reservation reserved
    have member : (reservation.pointer, 8 * allocatedOutcome.written.length) ∈
        SszNative.BitVector.allocationWrites allocatedOutcome := by
      simp only [SszNative.BitVector.allocationWrites, reserved, List.mem_singleton]
    exact words reservation.pointer allocatedOutcome.written
      (protectedWrites _ (included _ member)) (allocatedAt reservation reserved)
  refine ⟨allocation outcome.divided ?_ stored.1, ?_⟩
  · intro span member
    exact List.mem_append_left _ member
  · intro rounded roundedAt
    apply allocation rounded
    · intro span member
      simp only [SszNative.BitVector.Outcome.writes, roundedAt, List.mem_append]
      exact Or.inr member
    · exact stored.2 rounded roundedAt

/-- A reached physical world and actual terminal execution recover the complete
public postcondition, including every allocation word and the exact write frame. -/
theorem finish_post (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity initialUsed currentUsed : BitVec 64)
    (before : DataMem) (outcome : SszNative.BitVector.Outcome)
    (actual : outcome = SszNative.BitVector.run length data
      ⟨address.toNat, capacity.toNat, initialUsed.toNat⟩)
    (world : World s saved length data address capacity initialUsed currentUsed outcome.writes before)
    (cursorValue : currentUsed.toNat = outcome.used)
    (writtenBefore : outcome.writtenAt (widthLoad before))
    (protectedWrites : ∀ span ∈ outcome.writes,
      Protected s address capacity currentUsed span.1 span.2)
    (t : MachineState) (terminal : Terminal s saved before data outcome.result t) :
    Post s saved length data address capacity initialUsed t := by
  subst outcome
  have frame : RegionsFrame before t.1.dmem (finishRegions s) := terminal.frame
  have headerRead (off : Nat) (inside : off + 8 ≤ 24) :
      widthLoad t.1.dmem (s.regs.rbx.toNat + off) 8 =
        widthLoad before (s.regs.rbx.toNat + off) 8 := by
    apply frame.width _ _ (by
      have bound : s.regs.rbx.toNat + 24 ≤ 2^64 := world.physical.header_bound
      omega)
    intro span member
    simp only [finishRegions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · have apart : Body.Apart s.regs.rbx.toNat 24 s.regs.rdi.toNat 80 :=
        world.physical.header_output
      unfold Body.Apart at apart ⊢
      omega
    · have apart : Body.Apart s.regs.rbx.toNat 24 (workStart s) workSize :=
        world.physical.header_work
      unfold Body.Apart at apart ⊢
      omega
  have descriptorRead (off : Nat) (inside : off + 8 ≤ 24) :
      widthLoad t.1.dmem (s.regs.rbp.toNat + off) 8 =
        widthLoad before (s.regs.rbp.toNat + off) 8 := by
    exact finish_protected_width {s with dmem := before} before t.1.dmem
      address capacity currentUsed _ _ frame
      (world.physical.descriptor_owned.subrange off 8 inside)
  have operand : length.At (widthLoad t.1.dmem) := by
    apply frame.operand length world.physical.descriptor.2.2
    intro pointer words equal span member
    subst length
    simp only [finishRegions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact world.physical.operand_owned.output
    · exact world.physical.operand_owned.work
  refine {
    observed := terminal.observed
    written := finish_written s before t.1.dmem address capacity currentUsed _ frame
      writtenBefore protectedWrites
    returned := terminal.returned
    frame := ?_
    arenaBase := ?_
    arenaCapacity := ?_
    cursor := ?_
    descriptor := ?_
    source := ?_ }
  · intro a output work cursor outside
    have kept := frame a (by
      intro span member
      simp only [finishRegions, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact output
      · exact work)
    exact kept.trans (world.frame a output work cursor outside)
  · have kept := headerRead 0 (by decide)
    simp only [Nat.add_zero] at kept
    rw [kept]
    simp only [widthLoad, ← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      world.physical.address_load, Option.map_some, Int.toNat_natCast]
  · have capacityRead : Mem.loadInt before (s.regs.rbx.toBitVec + 8#64) 8 =
        some (capacity.toNat : Int) := world.physical.capacity_load
    rw [headerRead 8 (by decide)]
    simp only [widthLoad, ← UInt64.toNat_toBitVec, width_address,
      capacityRead, Option.map_some, Int.toNat_natCast]
  · have cursorRead : Mem.loadInt before (s.regs.rbx.toBitVec + 16#64) 8 =
        some (currentUsed.toNat : Int) := world.physical.used_load
    rw [headerRead 16 (by decide), ← cursorValue]
    simp only [widthLoad, ← UInt64.toNat_toBitVec, width_address,
      cursorRead, Option.map_some, Int.toNat_natCast]
  · refine ⟨?_, ?_, operand⟩
    · rw [descriptorRead 8 (by decide)]
      exact world.physical.descriptor.1
    · simpa only [Nat.add_assoc, Nat.reduceAdd, descriptorRead 16 (by decide)] using
        world.physical.descriptor.2.1
  · apply frame.bytes s.regs.rdx.toNat data world.physical.source_owned.bound world.physical.source
    intro span member
    simp only [finishRegions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact world.physical.source_owned.output
    · exact world.physical.source_owned.work

end SszX86.BitVector
