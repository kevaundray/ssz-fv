import SszX86.NatDivisionMemory

namespace SszX86.NatDivision
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Exact geometry of every written quotient limb, including high zeros that
normalization removes from the visible result. No signed arena bound is used. -/
theorem allocation_bounds (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).allocation =
      some r) :
    0 < r.pointer ∧ r.pointer % 8 = 0 ∧
      address.toNat + used.toNat ≤ r.pointer ∧
      r.pointer + 8 * (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).written.length =
        address.toNat + r.used ∧
      r.used ≤ capacity.toNat ∧
      r.pointer + 8 * (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).written.length ≤
        2^64 := by
  obtain ⟨usedEq, length, checks, pointer, finish, success⟩ :=
    SszNative.NatDivision.allocation_resources operand divisor address.toNat capacity.toNat used.toNat r allocated
  have positive : 0 < (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).written.length := by
    rw [length]
    split <;> omega
  rw [← length] at checks finish
  have cursor := Arena.used_le_start address.toNat used.toNat
  have storage := owned.arena_bound
  have startPointer := Arena.start_pointer address.toNat used.toNat
  have aligned := Arena.aligned_mod (address.toNat + used.toNat)
  have capacityPositive : 0 < capacity.toNat := by
    have fits := checks.2.2.2.2.2
    unfold Arena.finish at fits
    omega
  have basePositive := owned.arena_nonzero capacityPositive
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [pointer, startPointer]
    exact aligned
  · omega
  · rw [pointer, finish]
    simp only [Arena.finish, Nat.add_assoc]
  · rw [finish]
    exact checks.2.2.2.2.2
  · rw [pointer]
    have fits := checks.2.2.2.2.2
    unfold Arena.finish at fits
    omega

theorem preserves_region (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (m : DataMem) (frame : Frame s m
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat))
    (p n : Nat) (hp : Protected s address capacity used p n) :
    ∀ i < n, m.get? (BitVec.ofNat 64 (p+i)) = s.dmem.get? (BitVec.ofNat 64 (p+i)) := by
  intro i inside
  have bound : p+i < 2^64 := by have := hp.bound; omega
  apply frame
  · have apart := hp.output
    unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    omega
  · have apart := hp.activation
    unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    omega
  · intro r allocated
    have apartCursor := hp.cursor
    have apartArena := hp.arena
    have bounds := allocation_bounds s operand divisor address capacity used ra owned r allocated
    have usedBound : used.toNat ≤ capacity.toNat := by omega
    unfold Body.Outside Body.Apart at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    constructor <;> omega

theorem preserves_load (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (m : DataMem) (frame : Frame s m
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat))
    (p n off count : Nat) (hp : Protected s address capacity used p n)
    (inside : off + count ≤ n) :
    widthLoad m (p + off) count = widthLoad s.dmem (p + off) count := by
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  rw [← BitVec.ofNat_add]
  simpa only [Nat.add_assoc] using
    preserves_region s operand divisor address capacity used ra owned m frame p n hp
      (off+i) (by omega)

/-- Transport the original physical operand, including all redundant zero limbs
and its original borrowed pointer rather than a normalized replacement. -/
theorem operand_preserved (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (m : DataMem) (frame : Frame s m
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat)) :
    operand.At (widthLoad m) := by
  have stored := owned.operand_at
  have hp := owned.operand_owned
  cases operand with
  | small limb => trivial
  | large pointer words =>
    obtain ⟨positive, aligned, bound, limbs⟩ := stored
    refine ⟨positive, aligned, bound, ?_⟩
    intro i
    rw [preserves_load s (.large pointer words) divisor address capacity used ra owned m frame
      pointer.toNat (8 * words.length) (8 * i.val) 8 hp (by omega)]
    exact limbs i

/-- The immutable arena-header words are outside every permitted write. -/
theorem Owned.header_protected {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    Protected s address capacity used s.regs.r8.toNat 16 := by
  have bound := owned.header_bound
  have output := owned.header_output
  have stack := owned.header_stack
  have arena := owned.arena_header
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> unfold Body.Apart at * <;> omega

/-- The caller return slot is outside the full activation and every other write. -/
theorem Owned.return_protected {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    Protected s address capacity used s.regs.rsp.toNat 8 := by
  have output := owned.output_return
  have cursor := owned.cursor_return
  have arena := owned.arena_return
  have stack := owned.stack_low
  refine ⟨owned.return_bound, ?_, ?_, ?_, ?_⟩ <;> unfold Body.Apart at * <;> omega

theorem arena_header_preserved (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (m : DataMem) (frame : Frame s m
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat)) :
    widthLoad m s.regs.r8.toNat 8 = widthLoad s.dmem s.regs.r8.toNat 8 ∧
      widthLoad m (s.regs.r8.toNat + 8) 8 = widthLoad s.dmem (s.regs.r8.toNat + 8) 8 := by
  constructor
  · simpa only [Nat.add_zero] using preserves_load s operand divisor address capacity used ra owned m frame
      s.regs.r8.toNat 16 0 8 owned.header_protected (by decide)
  · exact preserves_load s operand divisor address capacity used ra owned m frame
      s.regs.r8.toNat 16 8 8 owned.header_protected (by decide)

/-- Assemble the final physical contract from ISA observations and its byte frame;
original input preservation follows from ownership, not an execution premise. -/
theorem post_of_frame (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64) (t : MachineState)
    (owned : Owned s operand divisor address capacity used ra)
    (observed : NatArithmetic.DivisionResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).result)
    (written : ∀ r,
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).allocation = some r →
      NatMemory.wordsAt (widthLoad t.1.dmem) r.pointer
        (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).written)
    (returned : Returned s ra t)
    (frame : Frame s t.1.dmem
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat))
    (cursor : widthLoad t.1.dmem (s.regs.r8.toNat + 16) 8 =
      some (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).used) :
    Post s operand divisor address capacity used ra t :=
  ⟨observed, written, returned, frame, cursor,
    operand_preserved s operand divisor address capacity used ra owned t.1.dmem frame⟩

end SszX86.NatDivision
