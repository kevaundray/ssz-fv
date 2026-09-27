import SszX86.NatDivisionFrame
import SszX86.NatDivisionReserveMemory

namespace SszX86.NatDivision.Reservation
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Positive reservations lie in the original free suffix even when the entry
cursor was not assumed below capacity. No signed capacity bound is required. -/
theorem reserve_bounds (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (count : Nat) (positive : 0 < count) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat count = some r) :
    0 < r.pointer ∧ r.pointer % 8 = 0 ∧
      address.toNat + used.toNat ≤ r.pointer ∧
      r.pointer + 8 * count = address.toNat + r.used ∧
      r.used ≤ capacity.toNat ∧ r.pointer + 8 * count ≤ 2^64 ∧
      used.toNat ≤ capacity.toNat := by
  obtain ⟨checks, rfl⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ _ positive r).1 reserved
  dsimp only
  have cursor := Arena.used_le_start address.toNat used.toNat
  have storage := owned.arena_bound
  have fits := checks.2.2.2.2.2
  have capacityPositive : 0 < capacity.toNat := by
    unfold Arena.finish at fits
    omega
  have basePositive := owned.arena_nonzero capacityPositive
  refine ⟨by omega, ?_, by omega, ?_, fits, ?_, ?_⟩
  · rw [Arena.start_pointer]
    exact Arena.aligned_mod _
  · simp only [Arena.finish, Nat.add_assoc]
  · unfold Arena.finish at fits
    omega
  · unfold Arena.finish at fits
    omega

namespace Small

private theorem allocation_fields (address capacity used : BitVec 64) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r) :
    r.pointer = address.toNat + Arena.start address.toNat used.toNat ∧
    r.used = Arena.start address.toNat used.toNat + 16 ∧ r.used < 2^64 := by
  obtain ⟨checks, rfl⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
  exact ⟨rfl, rfl, checks.2.2.2.2.1⟩

/-- The exact two stored quotient limbs, not only the normalized result. -/
theorem reserved_words_owned (s t : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r)
    (flags : StatusFlags) :
    NatMemory.wordsAt (widthLoad (reservedState t address used flags).dmem) r.pointer
      [t.regs.rax.toBitVec, t.regs.rdx.toBitVec] := by
  have bounds := reserve_bounds s operand divisor address capacity used ra owned 2 (by decide) r reserved
  obtain ⟨pointer, finish, endBound⟩ := allocation_fields address capacity used r reserved
  have observed := reserved_payload t address used flags (by rw [← pointer]; omega)
  have low : widthLoad (reservedState t address used flags).dmem r.pointer 8 =
      some t.regs.rax.toNat := by
    simpa only [BoolCodec.observe, widthLoad, pointer, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using observed.1
  have high : widthLoad (reservedState t address used flags).dmem (r.pointer+8) 8 =
      some t.regs.rdx.toNat := by
    simpa only [BoolCodec.observe, widthLoad, pointer, BitVec.ofNat_add] using observed.2
  intro i
  have inside : i.val < 2 := i.isLt
  have cases : i.val = 0 ∨ i.val = 1 := by omega
  rcases cases with zero | one
  · simpa [zero] using low
  · simpa [one] using high

/-- The cursor observation survives both payload stores because the owned
header is disjoint from the free suffix containing the successful allocation. -/
theorem reserved_cursor_owned (s t : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (arena : t.regs.r12.toBitVec = s.regs.r8.toBitVec)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r)
    (flags : StatusFlags) :
    widthLoad (reservedState t address used flags).dmem (s.regs.r8.toNat+16) 8 = some r.used := by
  have bounds := reserve_bounds s operand divisor address capacity used ra owned 2 (by decide) r reserved
  obtain ⟨pointer, finish, endBound⟩ := allocation_fields address capacity used r reserved
  have observed := reserved_cursor t address used flags (by omega) (by
    intro i hi j hj
    rw [arena, ← pointer]
    have apart := owned.arena_header
    have headerBound := owned.header_bound
    simp only [Body.Apart, ← UInt64.toNat_toBitVec] at apart headerBound
    bv_omega)
  rw [← finish] at observed
  simpa only [BoolCodec.observe, widthLoad, ← UInt64.toNat_toBitVec,
    width_address, arena] using observed

/-- Successful reservation preserves every saved register word in the actual
56-byte activation, including when the original arena capacity exceeds isize. -/
theorem reserved_saved_owned (s t : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (arena : t.regs.r12.toBitVec = s.regs.r8.toBitVec)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r)
    (saved : SavedAt t.dmem (s.regs.rsp.toBitVec - 56#64) s)
    (flags : StatusFlags) :
    SavedAt (reservedState t address used flags).dmem (s.regs.rsp.toBitVec - 56#64) s := by
  have bounds := reserve_bounds s operand divisor address capacity used ra owned 2 (by decide) r reserved
  obtain ⟨pointer, finish, endBound⟩ := allocation_fields address capacity used r reserved
  apply savedAt_congr t.dmem _ _ s _ saved
  intro i hi
  apply reserved_frame
  · intro j hj
    rw [arena]
    have apart := owned.header_stack
    have headerBound := owned.header_bound
    have stackLow := owned.stack_low
    simp only [Body.Apart, ← UInt64.toNat_toBitVec] at apart headerBound stackLow
    bv_omega
  · intro j hj
    rw [← pointer]
    have apart := owned.arena_stack
    have stackLow := owned.stack_low
    simp only [Body.Apart, ← UInt64.toNat_toBitVec] at apart stackLow
    bv_omega

/-- Append exactly the committed cursor and both payload words to a whole-run
frame whose allocation and complete written list are already identified. -/
theorem reserved_frame_owned (s t : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (arena : t.regs.r12.toBitVec = s.regs.r8.toBitVec)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r)
    (outcome : NatArithmetic.Outcome (NatOperand × BitVec 64))
    (allocated : outcome.allocation = some r)
    (written : outcome.written = [t.regs.rax.toBitVec, t.regs.rdx.toBitVec])
    (frame : NatDivision.Frame s t.dmem outcome) (flags : StatusFlags) :
    NatDivision.Frame s (reservedState t address used flags).dmem outcome := by
  have bounds := reserve_bounds s operand divisor address capacity used ra owned 2 (by decide) r reserved
  obtain ⟨pointer, finish, endBound⟩ := allocation_fields address capacity used r reserved
  intro a output activation allocation
  have outside := allocation r allocated
  rw [written] at outside
  have same : (reservedState t address used flags).dmem.get? a = t.dmem.get? a := by
    apply reserved_frame
    · intro j hj
      rw [arena]
      have headerBound := owned.header_bound
      simp only [Body.Outside, ← UInt64.toNat_toBitVec] at outside headerBound
      bv_omega
    · intro j hj
      rw [← pointer]
      simp only [Body.Outside, List.length_cons, List.length_nil] at outside
      bv_omega
  exact same.trans (frame a output activation allocation)

end Small
end SszX86.NatDivision.Reservation
