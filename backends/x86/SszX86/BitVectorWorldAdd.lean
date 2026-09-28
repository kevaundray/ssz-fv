import SszX86.BitVectorWorldAllocation
import SszX86.BitVectorRoundResources

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem World.add {s u : MachineData} {saved : Saved} {length quotient : NatOperand}
    {data : Ssz.Bytes} {address capacity initialUsed currentUsed ra : BitVec 64}
    {writes : List (Nat × Nat)} {t : MachineState}
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (owned : NatAdd.Owned u quotient (.small 1) address capacity currentUsed ra)
    (output : u.regs.rdi.toNat = s.regs.rsp.toNat + 16)
    (stack : u.regs.rsp.toNat = s.regs.rsp.toNat - 8)
    (arena : u.regs.r9 = s.regs.rbx)
    (post : NatAdd.Post u quotient (.small 1) address capacity currentUsed ra t)
    (mapping : Mapping.Extends u.dmem t.1.dmem) :
    World s saved length data address capacity initialUsed
      (outcomeCursor (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat))
      (writes ++ SszNative.BitVector.allocationWrites
        (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat)) t.1.dmem := by
  have low : 72 ≤ s.regs.rsp.toNat := world.physical.stack_low
  have bounds := add_used_bounds u quotient (.small 1) address capacity currentUsed ra owned
  have frame : WriteFrame s u.dmem t.1.dmem (SszNative.BitVector.allocationWrites
      (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat)) := by
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
          (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat).written.length)
        simp only [SszNative.BitVector.allocationWrites, allocated, List.mem_singleton]
  have cursor := post.cursor
  rw [arena] at cursor
  have cursorRead := widthLoad_eq _ _ _ _ cursor
  change Mem.loadInt t.1.dmem (BitVec.ofNat 64 (s.regs.rbx.toBitVec.toNat + 16)) 8 =
    some ((SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat).used : Int)
    at cursorRead
  rw [width_address] at cursorRead
  apply world.arithmetic _ frame mapping bounds.1 bounds.2 _ cursorRead
  intro reservation allocated
  have geometry := NatAdd.allocation_bounds u quotient (.small 1) address capacity currentUsed ra owned reservation allocated
  exact ⟨geometry.2.2.1, by omega⟩

theorem World.add_written_protected {s u : MachineData} {saved : Saved} {length quotient : NatOperand}
    {data : Ssz.Bytes} {address capacity initialUsed currentUsed ra : BitVec 64}
    {writes : List (Nat × Nat)}
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (owned : NatAdd.Owned u quotient (.small 1) address capacity currentUsed ra)
    (reservation : Arena.Reservation)
    (allocated : (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat).allocation =
      some reservation) :
    Protected s address capacity
      (outcomeCursor (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat))
      reservation.pointer (8 *
        (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat).written.length) := by
  have bounds := add_used_bounds u quotient (.small 1) address capacity currentUsed ra owned
  have usedSmall : (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat).used < 2^64 :=
    Nat.lt_of_le_of_lt bounds.2 capacity.isLt
  have cursorValue : (outcomeCursor
      (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat)).toNat =
      (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat).used := by
    simp only [outcomeCursor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt usedSmall]
  have geometry := NatAdd.allocation_bounds u quotient (.small 1) address capacity currentUsed ra owned reservation allocated
  have cursor := (SszNative.NatAdd.allocation_exact quotient (.small 1) address.toNat capacity.toNat
    currentUsed.toNat reservation allocated).1
  apply world.reservation_protected
  · exact geometry.2.2.1
  · rw [cursorValue, cursor]
    exact Nat.le_of_eq geometry.2.2.2.1
  · simpa only [cursorValue] using bounds.2

theorem World.round_result_protected {s u : MachineData} {saved : Saved} {length quotient expected : NatOperand}
    {data : Ssz.Bytes} {address capacity initialUsed currentUsed ra : BitVec 64}
    {writes : List (Nat × Nat)}
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (owned : NatAdd.Owned u quotient (.small 1) address capacity currentUsed ra)
    (success : (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat).result =
      .ok expected) :
    OperandProtected s address capacity
      (outcomeCursor (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat)) expected := by
  cases expected with
  | small limb => trivial
  | large pointer words =>
    obtain ⟨reservation, allocated, pointerEq, lengthBound⟩ :=
      round_large_allocation quotient address.toNat capacity.toNat currentUsed.toNat pointer words success
    have protectedSpan := world.add_written_protected owned reservation allocated
    have geometry := NatAdd.allocation_bounds u quotient (.small 1) address capacity currentUsed ra owned reservation allocated
    have length := (SszNative.NatAdd.allocation_geometry quotient (.small 1) address.toNat capacity.toNat
      currentUsed.toNat reservation allocated).2.2.2
    have positive : 0 < (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat currentUsed.toNat).written.length := by
      rw [length]
      split <;> omega
    have pointerBound : reservation.pointer < 2^64 := by omega
    have pointerValue : pointer.toNat = reservation.pointer := by
      rw [pointerEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound]
    change Protected s address capacity _ pointer.toNat (8 * words.length)
    rw [pointerValue]
    simpa only [Nat.add_zero] using protectedSpan.subrange 0 (8 * words.length) (by omega)

end SszX86.BitVector
