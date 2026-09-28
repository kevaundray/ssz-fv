import SszX86.BitVectorWorldAllocation
import SszX86.BitVectorResources

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- Lift the linked divider's precise writes into the caller's physical world.
The helper result is its real Post, not a replacement arithmetic assumption. -/
theorem World.division {s u : MachineData} {saved : Saved} {length : NatOperand}
    {data : Ssz.Bytes} {address capacity initialUsed currentUsed ra : BitVec 64}
    {writes : List (Nat × Nat)} {t : MachineState}
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (owned : NatDivision.Owned u length 8 address capacity currentUsed ra)
    (output : u.regs.rdi.toNat = s.regs.rsp.toNat + 16)
    (stack : u.regs.rsp.toNat = s.regs.rsp.toNat - 8)
    (arena : u.regs.r8 = s.regs.rbx)
    (post : NatDivision.Post u length 8 address capacity currentUsed ra t)
    (mapping : Mapping.Extends u.dmem t.1.dmem) :
    World s saved length data address capacity initialUsed
      (outcomeCursor (SszNative.NatDivision.run length 8 address.toNat capacity.toNat currentUsed.toNat))
      (writes ++ SszNative.BitVector.allocationWrites
        (SszNative.NatDivision.run length 8 address.toNat capacity.toNat currentUsed.toNat)) t.1.dmem := by
  have low : 72 ≤ s.regs.rsp.toNat := world.physical.stack_low
  have bounds := division_used_bounds u length address capacity currentUsed ra owned world.physical.used_bound
  have frame : WriteFrame s u.dmem t.1.dmem (SszNative.BitVector.allocationWrites
      (SszNative.NatDivision.run length 8 address.toNat capacity.toNat currentUsed.toNat)) := by
    intro a _ work cursor outside
    apply post.frame a
    · change Body.Outside a.toNat (s.regs.rsp.toNat - 72) 296 at work
      unfold Body.Outside at *
      omega
    · change Body.Outside a.toNat (s.regs.rsp.toNat - 72) 296 at work
      unfold Body.Outside at *
      omega
    · intro reservation allocated
      refine ⟨?_, ?_⟩
      · simpa only [arena] using cursor
      · apply outside (reservation.pointer, 8 *
          (SszNative.NatDivision.run length 8 address.toNat capacity.toNat currentUsed.toNat).written.length)
        simp only [SszNative.BitVector.allocationWrites, allocated, List.mem_singleton]
  have cursor := post.cursor
  rw [arena] at cursor
  have cursorRead := widthLoad_eq _ _ _ _ cursor
  change Mem.loadInt t.1.dmem (BitVec.ofNat 64 (s.regs.rbx.toBitVec.toNat + 16)) 8 =
    some ((SszNative.NatDivision.run length 8 address.toNat capacity.toNat currentUsed.toNat).used : Int)
    at cursorRead
  rw [width_address] at cursorRead
  apply world.arithmetic _ frame mapping bounds.1 bounds.2 _ cursorRead
  intro reservation allocated
  have geometry := NatDivision.allocation_bounds u length 8 address capacity currentUsed ra owned reservation allocated
  exact ⟨geometry.2.2.1, by omega⟩

theorem World.division_written_protected {s u : MachineData} {saved : Saved} {length : NatOperand}
    {data : Ssz.Bytes} {address capacity initialUsed currentUsed ra : BitVec 64}
    {writes : List (Nat × Nat)}
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (owned : NatDivision.Owned u length 8 address capacity currentUsed ra)
    (reservation : Arena.Reservation)
    (allocated : (SszNative.NatDivision.run length 8 address.toNat capacity.toNat currentUsed.toNat).allocation =
      some reservation) :
    Protected s address capacity
      (outcomeCursor (SszNative.NatDivision.run length 8 address.toNat capacity.toNat currentUsed.toNat))
      reservation.pointer (8 *
        (SszNative.NatDivision.run length 8 address.toNat capacity.toNat currentUsed.toNat).written.length) := by
  have bounds := division_used_bounds u length address capacity currentUsed ra owned world.physical.used_bound
  have usedSmall : (SszNative.NatDivision.run length 8 address.toNat capacity.toNat currentUsed.toNat).used < 2^64 :=
    Nat.lt_of_le_of_lt bounds.2 capacity.isLt
  have cursorValue : (outcomeCursor
      (SszNative.NatDivision.run length 8 address.toNat capacity.toNat currentUsed.toNat)).toNat =
      (SszNative.NatDivision.run length 8 address.toNat capacity.toNat currentUsed.toNat).used := by
    simp only [outcomeCursor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt usedSmall]
  have geometry := NatDivision.allocation_bounds u length 8 address capacity currentUsed ra owned reservation allocated
  have cursor := (SszNative.NatDivision.allocation_resources length 8 address.toNat capacity.toNat
    currentUsed.toNat reservation allocated).1
  apply world.reservation_protected
  · exact geometry.2.2.1
  · rw [cursorValue, cursor]
    exact Nat.le_of_eq geometry.2.2.2.1
  · simpa only [cursorValue] using bounds.2

end SszX86.BitVector
