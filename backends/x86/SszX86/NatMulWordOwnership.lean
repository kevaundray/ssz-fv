import SszX86.NatMulWordCore
import SszNatArithmeticMemory

namespace SszX86.NatMulWord
open SszNative UintCodec

/-- Read-only input may overlap the used arena prefix.  Only actual writable
regions require separation; redundant limbs remain part of the input span. -/
structure Protected (s : MachineData) (address capacity used : BitVec 64)
    (p n : Nat) : Prop where
  bound : p + n ≤ 2^64
  output : Body.Apart p n s.regs.rdi.toNat 72
  activation : Body.Apart p n (s.regs.rsp.toNat - 64) 64
  cursor : Body.Apart p n (s.regs.r8.toNat + 16) 8
  arena : Body.Apart p n (address.toNat + used.toNat) (capacity.toNat - used.toNat)

def OperandProtected (s : MachineData) (address capacity used : BitVec 64) :
    NatOperand → Prop
  | .small _ => True
  | .large p words => Protected s address capacity used p.toNat (8 * words.length)

/-- Physical entry ownership for the original five-register private ABI.
The six pushes and two spill words occupy exactly 64 bytes below entry RSP. -/
structure Owned (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) : Prop where
  operand_pointer : s.regs.rsi.toBitVec = operand.pointer
  operand_payload : s.regs.rdx.toBitVec = operand.payload
  factor : s.regs.rcx.toBitVec = factor
  operand_at : operand.At (widthLoad s.dmem)
  operand_owned : OperandProtected s address capacity used operand
  output_bound : s.regs.rdi.toNat + 72 ≤ 2^64
  output_mapped : OutputMapped s
  return_bound : s.regs.rsp.toNat + 8 ≤ 2^64
  return_load : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  stack_low : 64 ≤ s.regs.rsp.toNat
  stack_mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 64) 64
  output_return : Body.Apart s.regs.rdi.toNat 72 s.regs.rsp.toNat 8
  output_stack : Body.Apart s.regs.rdi.toNat 72 (s.regs.rsp.toNat - 64) 64
  header_bound : s.regs.r8.toNat + 24 ≤ 2^64
  address_load : Mem.loadInt s.dmem s.regs.r8.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 8) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16) 8 = some (used.toNat : Int)
  arena_bound : address.toNat + capacity.toNat ≤ 2^64
  used_bound : used.toNat ≤ capacity.toNat
  arena_nonzero : 0 < capacity.toNat → 0 < address.toNat
  free_mapped : Large.Mapped s.dmem (address + used) (capacity.toNat - used.toNat)
  arena_output : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rdi.toNat 72
  arena_stack : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat - 64) 64
  arena_return : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rsp.toNat 8
  arena_header : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.r8.toNat 24
  header_output : Body.Apart s.regs.r8.toNat 24 s.regs.rdi.toNat 72
  header_stack : Body.Apart s.regs.r8.toNat 24 (s.regs.rsp.toNat - 64) 64
  cursor_return : Body.Apart (s.regs.r8.toNat + 16) 8 s.regs.rsp.toNat 8

/-- The native envelope is 72 bytes, but success writes only its pair and status;
error writes 68 bytes. Allocation permits only its exact cursor and limb writes. -/
def Frame (s : MachineData) (m : DataMem) (outcome : NatArithmetic.Outcome NatOperand) : Prop :=
  ∀ a : BitVec 64,
    (match outcome.result with
      | .ok _ => Body.Outside a.toNat s.regs.rdi.toNat 16 ∧
          Body.Outside a.toNat (s.regs.rdi.toNat + 64) 4
      | .error _ => Body.Outside a.toNat s.regs.rdi.toNat 68) →
    Body.Outside a.toNat (s.regs.rsp.toNat - 64) 64 →
    (∀ r, outcome.allocation = some r →
      Body.Outside a.toNat (s.regs.r8.toNat + 16) 8 ∧
      Body.Outside a.toNat r.pointer (8 * outcome.written.length)) →
    m.get? a = s.dmem.get? a

abbrev Returned := Delimited.Returned

structure Post (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (t : MachineState) : Prop where
  observed : NatArithmetic.AddResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
    (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).result
  written : ∀ r,
    (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r →
    NatMemory.wordsAt (widthLoad t.1.dmem) r.pointer
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written
  returned : Returned s ra t
  frame : Frame s t.1.dmem
    (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat)
  cursor : widthLoad t.1.dmem (s.regs.r8.toNat + 16) 8 =
    some (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).used
  operand_at : operand.At (widthLoad t.1.dmem)

theorem Post.value {s : MachineData} {operand : NatOperand}
    {factor address capacity used ra : BitVec 64} {t : MachineState}
    (post : Post s operand factor address capacity used ra t) (result : NatOperand)
    (success : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).result =
      .ok result) :
    NatArithmetic.operandAt (widthLoad t.1.dmem) s.regs.rdi.toNat result ∧
      result.value = operand.value * factor.toNat := by
  have observed := post.observed
  rw [success] at observed
  exact ⟨observed.1, SszNative.NatMul.runWord_value operand factor _ _ _ result success⟩

end SszX86.NatMulWord
