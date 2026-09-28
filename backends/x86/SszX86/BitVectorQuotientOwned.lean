import SszX86.BitVectorEntryOwned
import SszX86.BitVectorResources
import SszX86.BitVectorRebase

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

def divisionCursor (length : NatOperand) (address capacity used : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).used

theorem division_cursor_value (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used ra : BitVec 64)
    (owned : Owned s saved length data address capacity used) :
    (divisionCursor length address capacity used).toNat =
      (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).used := by
  have bounds := division_used_bounds (divisionReady s length ra) length address capacity used ra
    (division_owned s saved length data address capacity used ra owned) owned.used_bound
  have capacityBound := capacity.isLt
  have usedSmall :
      (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).used < 2^64 := by
    omega
  simp only [divisionCursor, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt usedSmall

/-- A retained Large quotient is in the used prefix, not in the next helper's
free suffix. This follows from the actual division allocation provenance, not
from canonical input assumptions or a borrowed-input fiction. -/
theorem division_quotient_owned (s : MachineData) (saved : Saved) (length quotient : NatOperand)
    (data : Ssz.Bytes) (address capacity used ra remainder : BitVec 64)
    (owned : Owned s saved length data address capacity used)
    (success : (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).result =
      .ok (quotient, remainder)) :
    OperandProtected s address capacity (divisionCursor length address capacity used) quotient := by
  cases quotient with
  | small limb => trivial
  | large pointer words =>
    obtain ⟨reservation, allocated, pointerEq, lengthBound⟩ :=
      division_large_allocation length address.toNat capacity.toNat used.toNat pointer remainder words success
    obtain ⟨positive, aligned, start, finish, cursorBound, endBound⟩ :=
      NatDivision.allocation_bounds (divisionReady s length ra) length 8 address capacity used ra
        (division_owned s saved length data address capacity used ra owned) reservation allocated
    have resources := SszNative.NatDivision.allocation_resources length 8 address.toNat capacity.toNat
      used.toNat reservation allocated
    have writtenPositive : 0 <
        (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).written.length := by
      rw [resources.2.1]
      split <;> omega
    have pointerBound : reservation.pointer < 2^64 := by omega
    have pointerValue : pointer.toNat = reservation.pointer := by
      rw [pointerEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound]
    have current := division_cursor_value s saved length data address capacity used ra owned
    rw [resources.1] at current
    change Protected s address capacity (divisionCursor length address capacity used)
      pointer.toNat (8 * words.length)
    constructor
    · omega
    · have apart := owned.arena_output
      unfold Body.Apart at *
      omega
    · have apart := owned.arena_work
      unfold Body.Apart at *
      omega
    · have apart := owned.arena_header
      unfold Body.Apart at *
      omega
    · unfold Body.Apart
      omega

end SszX86.BitVector
