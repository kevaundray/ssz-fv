import SszX86.NatDivisionLoop
import SszX86.NatDivisionReserveWideResources

namespace SszX86.NatDivision.Loop
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Translate the loop's byte footprint into the complete helper's footprint. -/
theorem owned_frame (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (before after : DataMem) (count : Nat) (positive : 0 < count)
    (reservation : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat count = some reservation)
    (outcome : NatArithmetic.Outcome (NatOperand × BitVec 64))
    (allocated : outcome.allocation = some reservation) (length : outcome.written.length = count)
    (earlier : NatDivision.Frame s before outcome)
    (frame : Frame before after (BitVec.ofNat 64 reservation.pointer)
      (s.regs.rsp.toBitVec - 56#64) count) :
    NatDivision.Frame s after outcome := by
  have bounds := Reservation.reserve_bounds s operand divisor address capacity used ra owned
    count positive reservation reserved
  intro a output activation allocation
  have outside := (allocation reservation allocated).2
  rw [length] at outside
  have same : after.get? a = before.get? a := by
    apply frame
    · intro i hi equal
      simp only [Body.Outside] at outside
      bv_omega
    · intro i hi equal
      have low := owned.stack_low
      simp only [Body.Outside, ← UInt64.toNat_toBitVec] at activation low
      bv_omega
  exact same.trans (earlier a output activation allocation)

/-- Any owned non-stack region disjoint from both writes retains all its bytes. -/
theorem owned_region (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (before after : DataMem) (count : Nat) (positive : 0 < count)
    (reservation : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat count = some reservation)
    (frame : Frame before after (BitVec.ofNat 64 reservation.pointer)
      (s.regs.rsp.toBitVec - 56#64) count)
    (p : BitVec 64) (byteCount : Nat) (bound : p.toNat + byteCount ≤ 2^64)
    (arenaApart : Body.Apart p.toNat byteCount (address.toNat+used.toNat) (capacity.toNat-used.toNat))
    (stackApart : Body.Apart p.toNat byteCount (s.regs.rsp.toNat-64) 64) :
    ∀ i < byteCount, after.get? (p + BitVec.ofNat 64 i) = before.get? (p + BitVec.ofNat 64 i) := by
  have bounds := Reservation.reserve_bounds s operand divisor address capacity used ra owned
    count positive reservation reserved
  intro i hi
  apply frame
  · intro j hj equal
    simp only [Body.Apart] at arenaApart
    bv_omega
  · intro j hj equal
    have low := owned.stack_low
    simp only [Body.Apart, ← UInt64.toNat_toBitVec] at stackApart low
    bv_omega

/-- Scratch and saved words are above the nested CALL slot and outside scratch allocation. -/
theorem owned_activation (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (before after : DataMem) (count : Nat) (positive : 0 < count)
    (reservation : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat count = some reservation)
    (frame : Frame before after (BitVec.ofNat 64 reservation.pointer)
      (s.regs.rsp.toBitVec - 56#64) count) :
    ∀ i < 56, after.get? (s.regs.rsp.toBitVec - 56#64 + BitVec.ofNat 64 i) =
      before.get? (s.regs.rsp.toBitVec - 56#64 + BitVec.ofNat 64 i) := by
  have bounds := Reservation.reserve_bounds s operand divisor address capacity used ra owned
    count positive reservation reserved
  intro i hi
  apply frame
  · intro j hj equal
    have apart := owned.arena_stack
    have low := owned.stack_low
    simp only [Body.Apart, ← UInt64.toNat_toBitVec] at apart low
    bv_omega
  · intro j hj equal
    bv_omega

theorem owned_saved (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (before after : DataMem) (count : Nat) (positive : 0 < count)
    (reservation : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat count = some reservation)
    (frame : Frame before after (BitVec.ofNat 64 reservation.pointer)
      (s.regs.rsp.toBitVec - 56#64) count)
    (saved : SavedAt before (s.regs.rsp.toBitVec - 56#64) s) :
    SavedAt after (s.regs.rsp.toBitVec - 56#64) s := by
  apply savedAt_congr before after _ s _ saved
  intro i hi
  rw [memmove_addr_add]
  exact owned_activation s operand divisor address capacity used ra owned before after count
    positive reservation reserved frame (8+i) (by omega)

theorem owned_spill (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (before after : DataMem) (count : Nat) (positive : 0 < count)
    (reservation : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat count = some reservation)
    (frame : Frame before after (BitVec.ofNat 64 reservation.pointer)
      (s.regs.rsp.toBitVec - 56#64) count) :
    Mem.loadInt after (s.regs.rsp.toBitVec - 56#64) 8 =
      Mem.loadInt before (s.regs.rsp.toBitVec - 56#64) 8 := by
  apply memmove_loadInt_congr
  intro i hi
  exact owned_activation s operand divisor address capacity used ra owned before after count
    positive reservation reserved frame i (by omega)

end SszX86.NatDivision.Loop
