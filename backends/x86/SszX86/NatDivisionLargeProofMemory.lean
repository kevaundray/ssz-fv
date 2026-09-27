import SszX86.NatDivisionLargeProofPrepare
import SszX86.NatDivisionReserveLarge

namespace SszX86.NatDivision
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem large_spill_activation (s : MachineData) (a : BitVec 64)
    (outside : ∀ i < 64, a ≠ s.regs.rsp.toBitVec - 64 + BitVec.ofNat 64 i) :
    (largeSpillMem s).get? a = s.dmem.get? a := by
  exact (stack_store_frame (pushedMem s) s.regs.rsp.toBitVec a 64 56 8
    s.regs.rdi.toBitVec.toInt (by decide) (by decide) outside).trans
      (pushed_activation_frame s a outside)

theorem large_spill_header_load {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra)
    (off byteCount : Nat) (inside : off + byteCount ≤ 24) :
    Mem.loadInt (largeSpillMem s) (s.regs.r8.toBitVec + BitVec.ofNat 64 off) byteCount =
      Mem.loadInt s.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 off) byteCount := by
  have bound := owned.header_bound
  have apart := owned.header_stack
  have same := activation_load_congr s owned.stack_low s.dmem (largeSpillMem s)
    (large_spill_activation s) (s.regs.r8.toNat + off) byteCount
    (by omega) (by unfold Body.Apart at *; omega)
  simpa only [← UInt64.toNat_toBitVec, width_address] using same

theorem large_counted_header {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) (flags : StatusFlags) :
    Reservation.Large.Header (largeCountedState s operand flags) address capacity used := by
  constructor
  · simpa only [largeCountedState, prologueState, pushedState, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero] using (large_spill_header_load owned 0 8 (by decide)).trans
        (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using owned.address_load)
  · exact (large_spill_header_load owned 8 8 (by decide)).trans owned.capacity_load
  · exact (large_spill_header_load owned 16 8 (by decide)).trans owned.used_load

theorem large_spill_saved (s : MachineData) :
    SavedAt (largeSpillMem s) (s.regs.rsp.toBitVec - 56) s :=
  savedAt_scratch _ _ _ _ (pushed_saved s)

/-- The actual cursor store after the counted frontier. -/
def largeReservedState (s : MachineData) (operand : NatOperand)
    (address used : BitVec 64) (before after : StatusFlags) : MachineData :=
  Reservation.Large.reservedState (largeCountedState s operand before) address used after

theorem large_reserved_mapped (s : MachineData) (operand : NatOperand)
    (address used pointer : BitVec 64) (before after : StatusFlags) (length : Nat)
    (hm : Large.Mapped s.dmem pointer length) :
    Large.Mapped (largeReservedState s operand address used before after).dmem pointer length := by
  apply Large.mapped_store
  exact large_spill_mapped s pointer length hm

/-- Cursor commit preserves arbitrary physical loads disjoint from its eight
bytes, including the output spill and all six saved-register words. -/
theorem large_reserved_load (s : MachineData) (operand : NatOperand)
    (address used pointer : BitVec 64) (before after : StatusFlags) (byteCount : Nat)
    (apart : ∀ i < byteCount, ∀ j < 8,
      pointer + BitVec.ofNat 64 i ≠ s.regs.r8.toBitVec + 16 + BitVec.ofNat 64 j) :
    Mem.loadInt (largeReservedState s operand address used before after).dmem pointer byteCount =
      Mem.loadInt (largeSpillMem s) pointer byteCount :=
  BoolCodec.load_store_disjoint _ _ _ _ _ _ apart

theorem large_reserved_spill {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) (before after : StatusFlags) :
    Mem.loadInt (largeReservedState s operand address used before after).dmem
      (s.regs.rsp.toBitVec - 56) 8 = some (s.regs.rdi.toNat : Int) := by
  rw [large_reserved_load]
  · exact large_spill_output s
  · intro i hi j hj
    have apart := owned.header_stack
    have bound := owned.header_bound
    have low := owned.stack_low
    simp only [Body.Apart, ← UInt64.toNat_toBitVec] at apart bound low
    bv_omega

theorem large_reserved_saved {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) (before after : StatusFlags) :
    SavedAt (largeReservedState s operand address used before after).dmem
      (s.regs.rsp.toBitVec - 56) s := by
  apply savedAt_congr _ _ _ _ _ (large_spill_saved s)
  intro i hi
  apply Reservation.Large.reserved_frame
  intro j hj
  have apart := owned.header_stack
  have bound := owned.header_bound
  have low := owned.stack_low
  simp only [Body.Apart, ← UInt64.toNat_toBitVec] at apart bound low
  change s.regs.rsp.toBitVec - 56 + 8 + BitVec.ofNat 64 i ≠
    s.regs.r8.toBitVec + 16 + BitVec.ofNat 64 j
  bv_omega

theorem large_reserved_frame {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra)
    (count : 2 < operand.wordCount) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat operand.wordCount = some r)
    (before after : StatusFlags) :
    Frame s (largeReservedState s operand address used before after).dmem
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat) := by
  have phase := SszNative.NatDivision.phase_reserved operand divisor address.toNat
    capacity.toNat used.toNat owned.divisor_nonzero owned.divisor_ne_one count r reserved
  have allocated : (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).allocation =
      some r := by rw [phase]
  intro a output activation allocation
  apply Eq.trans (Reservation.Large.reserved_frame _ address used after a ?_)
  · exact large_spill_frame s owned.stack_low _ a output activation allocation
  · intro i hi
    have outside := (allocation r allocated).1
    have bound := owned.header_bound
    simp only [Body.Outside, ← UInt64.toNat_toBitVec] at outside bound
    change a ≠ s.regs.r8.toBitVec + 16 + BitVec.ofNat 64 i
    bv_omega

theorem large_reserved_cursor {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra)
    (count : 2 < operand.wordCount) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat operand.wordCount = some r)
    (before after : StatusFlags) :
    widthLoad (largeReservedState s operand address used before after).dmem
      (s.regs.r8.toNat + 16) 8 =
        some (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).used := by
  have positive : 0 < operand.wordCount := by omega
  obtain ⟨checks, canonical⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ _ positive r).1 reserved
  have countBound : operand.wordCount < 2^64 := by
    have length := checks.1
    omega
  have countReg : (largeCountedState s operand before).regs.rax.toNat = operand.wordCount := by
    simp [largeCountedState, Nat.mod_eq_of_lt countBound]
  have phase := SszNative.NatDivision.phase_reserved operand divisor address.toNat
    capacity.toNat used.toNat owned.divisor_nonzero owned.divisor_ne_one count r reserved
  rw [phase]
  have cursor := Reservation.Large.reserved_cursor (largeCountedState s operand before)
    address used after (by rw [countReg]; exact checks.2.2.2.2.1)
  rw [countReg] at cursor
  have finishEq : r.used = Arena.finish address.toNat used.toNat operand.wordCount := by
    rw [canonical]
  have headerAddress : BitVec.ofNat 64 (s.regs.r8.toNat + 16) =
      s.regs.r8.toBitVec + 16#64 := by
    simpa only [UInt64.toNat_toBitVec] using width_address s.regs.r8.toBitVec 16
  change (Mem.loadInt
    (Reservation.Large.reservedState (largeCountedState s operand before) address used after).dmem
    (BitVec.ofNat 64 (s.regs.r8.toNat + 16)) 8).map Int.toNat = some r.used
  rw [headerAddress, finishEq]
  exact cursor

end SszX86.NatDivision
