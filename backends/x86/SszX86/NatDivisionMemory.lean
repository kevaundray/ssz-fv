import SszX86.NatDivisionCore
import SszX86.DelimitedMemory

namespace SszX86.NatDivision
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Read-only regions may alias each other and the consumed arena prefix, but
never the output, activation, cursor, or mutable free suffix. -/
structure Protected (s : MachineData) (address capacity used : BitVec 64)
    (p n : Nat) : Prop where
  bound : p + n ≤ 2^64
  output : Body.Apart p n s.regs.rdi.toNat 68
  activation : Body.Apart p n (s.regs.rsp.toNat - 64) 64
  cursor : Body.Apart p n (s.regs.r8.toNat + 16) 8
  arena : Body.Apart p n (address.toNat + used.toNat) (capacity.toNat - used.toNat)

def OperandProtected (s : MachineData) (address capacity used : BitVec 64) :
    NatOperand → Prop
  | .small _ => True
  | .large p words => Protected s address capacity used p.toNat (8 * words.length)

/-- Physical ownership for the production divisor-at-least-two entry. RDI is
output, RSI/RDX are the original operand pair, RCX is divisor, and R8 is arena.
The 64-byte activation covers seven pushes and the nested helper's return slot.
Neither canonical input limbs, a signed capacity bound, nor used ≤ capacity is
required: the model retains the native checked-reservation failure paths. -/
structure Owned (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64) : Prop where
  operand_pointer : s.regs.rsi.toBitVec = operand.pointer
  operand_payload : s.regs.rdx.toBitVec = operand.payload
  divisor_register : s.regs.rcx.toBitVec = divisor
  divisor_lower : 2 ≤ divisor.toNat
  operand_at : operand.At (widthLoad s.dmem)
  operand_owned : OperandProtected s address capacity used operand
  output_bound : s.regs.rdi.toNat + 68 ≤ 2^64
  output_mapped : OutputMapped s
  return_bound : s.regs.rsp.toNat + 8 ≤ 2^64
  return_load : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  stack_low : 64 ≤ s.regs.rsp.toNat
  stack_mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 64) 64
  output_return : Body.Apart s.regs.rdi.toNat 68 s.regs.rsp.toNat 8
  output_stack : Body.Apart s.regs.rdi.toNat 68 (s.regs.rsp.toNat - 64) 64
  header_bound : s.regs.r8.toNat + 24 ≤ 2^64
  address_load : Mem.loadInt s.dmem s.regs.r8.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 8) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16) 8 = some (used.toNat : Int)
  arena_bound : address.toNat + capacity.toNat ≤ 2^64
  arena_nonzero : 0 < capacity.toNat → 0 < address.toNat
  arena_mapped : Large.Mapped s.dmem address capacity.toNat
  arena_output : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rdi.toNat 68
  arena_stack : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat - 64) 64
  arena_return : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rsp.toNat 8
  arena_header : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.r8.toNat 24
  header_output : Body.Apart s.regs.r8.toNat 24 s.regs.rdi.toNat 68
  header_stack : Body.Apart s.regs.r8.toNat 24 (s.regs.rsp.toNat - 64) 64
  cursor_return : Body.Apart (s.regs.r8.toNat + 16) 8 s.regs.rsp.toNat 8

theorem Owned.divisor_nonzero {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) : divisor ≠ 0 := by
  intro zero
  have lower := owned.divisor_lower
  simp [zero] at lower

theorem Owned.divisor_ne_one {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) : divisor ≠ 1 := by
  intro one
  have lower := owned.divisor_lower
  simp [one] at lower

/-- Only output68, activation64, and (on allocation) the cursor and complete
written quotient buffer may change. Neither alignment padding nor merely the
normalized visible quotient length determines the writable arena footprint. -/
def Frame (s : MachineData) (m : DataMem)
    (outcome : NatArithmetic.Outcome (NatOperand × BitVec 64)) : Prop :=
  ∀ a : BitVec 64,
    Body.Outside a.toNat s.regs.rdi.toNat 68 →
    Body.Outside a.toNat (s.regs.rsp.toNat - 64) 64 →
    (∀ r, outcome.allocation = some r →
      Body.Outside a.toNat (s.regs.r8.toNat + 16) 8 ∧
      Body.Outside a.toNat r.pointer (8 * outcome.written.length)) →
    m.get? a = s.dmem.get? a

/-- RET restores entry RSP+8, the return slot, callee-saved GPRs, and SIMD state. -/
abbrev Returned := Delimited.Returned

structure Post (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64) (t : MachineState) : Prop where
  observed : NatArithmetic.DivisionResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
    (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).result
  written : ∀ r,
    (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).allocation = some r →
    NatMemory.wordsAt (widthLoad t.1.dmem) r.pointer
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).written
  returned : Returned s ra t
  frame : Frame s t.1.dmem
    (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat)
  cursor : widthLoad t.1.dmem (s.regs.r8.toNat + 16) 8 =
    some (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).used
  operand_at : operand.At (widthLoad t.1.dmem)

/-- The arithmetic corollary concerns the exact quotient representation and
remainder physically stored by the full model result, with no input-size or
canonicalization premise. -/
theorem Post.arithmetic {s : MachineData} {operand quotient : NatOperand}
    {divisor address capacity used ra remainder : BitVec 64} {t : MachineState}
    (post : Post s operand divisor address capacity used ra t)
    (success : (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).result =
      .ok (quotient, remainder)) :
    NatArithmetic.operandAt (widthLoad t.1.dmem) s.regs.rdi.toNat quotient ∧
      widthLoad t.1.dmem (s.regs.rdi.toNat + 16) 8 = some remainder.toNat ∧
      widthLoad t.1.dmem (s.regs.rdi.toNat + 64) 4 = some 0 ∧
      quotient.value = operand.value / divisor.toNat ∧
      remainder.toNat = operand.value % divisor.toNat ∧
      remainder.toNat < divisor.toNat := by
  have observed := post.observed
  rw [success] at observed
  exact ⟨observed.1, observed.2.1, observed.2.2,
    SszNative.NatDivision.run_success operand divisor address.toNat capacity.toNat used.toNat
      (quotient, remainder) success⟩

/-- The frame has no writable cursor or arena bytes on an unallocated path. -/
theorem Frame.no_allocation {s : MachineData} {m : DataMem}
    {outcome : NatArithmetic.Outcome (NatOperand × BitVec 64)}
    (frame : Frame s m outcome) (unallocated : outcome.allocation = none)
    (a : BitVec 64) (output : Body.Outside a.toNat s.regs.rdi.toNat 68)
    (activation : Body.Outside a.toNat (s.regs.rsp.toNat - 64) 64) :
    m.get? a = s.dmem.get? a := by
  apply frame a output activation
  intro r allocated
  rw [unallocated] at allocated
  contradiction

theorem Post.no_allocation_resources {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64} {t : MachineState}
    (post : Post s operand divisor address capacity used ra t)
    (unallocated : (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).allocation = none) :
    widthLoad t.1.dmem (s.regs.r8.toNat + 16) 8 = some used.toNat ∧
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).written = [] := by
  have resources := SszNative.NatDivision.no_allocation_resources operand divisor
    address.toNat capacity.toNat used.toNat unallocated
  exact ⟨post.cursor.trans (congrArg some resources.1), resources.2⟩

end SszX86.NatDivision
