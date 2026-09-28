import SszX86.NatAddMemory
import SszNatMul

namespace SszX86.NatMul
open SszNative
open UintCodec

/-- The native Result occupies 72 bytes, including its four unwritten tail bytes. -/
abbrev OutputMapped (s : MachineData) : Prop :=
  Large.Mapped s.dmem s.regs.rdi.toBitVec 72

/-- Read-only operands may alias each other and the arena's consumed prefix. -/
structure Protected (s : MachineData) (address capacity used : BitVec 64)
    (p n : Nat) : Prop where
  bound : p + n ≤ 2^64
  output : Body.Apart p n s.regs.rdi.toNat 72
  activation : Body.Apart p n (s.regs.rsp.toNat - 96) 96
  cursor : Body.Apart p n (s.regs.r9.toNat + 16) 8
  arena : Body.Apart p n (address.toNat + used.toNat) (capacity.toNat - used.toNat)

def OperandProtected (s : MachineData) (address capacity used : BitVec 64) :
    NatOperand → Prop
  | .small _ => True
  | .large p words => Protected s address capacity used p.toNat (8 * words.length)

/-- Initial physical ownership only. The six pushes occupy 48 bytes, the local
area 40, and the memset return slot 8. The tailcall restores the main frame
before entering mul_word, whose 64-byte activation fits this same envelope. -/
structure Owned (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) : Prop where
  left_pointer : s.regs.rsi.toBitVec = left.pointer
  left_payload : s.regs.rdx.toBitVec = left.payload
  right_pointer : s.regs.rcx.toBitVec = right.pointer
  right_payload : s.regs.r8.toBitVec = right.payload
  left_at : left.At (widthLoad s.dmem)
  right_at : right.At (widthLoad s.dmem)
  left_owned : OperandProtected s address capacity used left
  right_owned : OperandProtected s address capacity used right
  output_bound : s.regs.rdi.toNat + 72 ≤ 2^64
  output_mapped : OutputMapped s
  return_bound : s.regs.rsp.toNat + 8 ≤ 2^64
  return_load : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  stack_low : 96 ≤ s.regs.rsp.toNat
  stack_mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 96) 96
  output_return : Body.Apart s.regs.rdi.toNat 72 s.regs.rsp.toNat 8
  output_stack : Body.Apart s.regs.rdi.toNat 72 (s.regs.rsp.toNat - 96) 96
  header_bound : s.regs.r9.toNat + 24 ≤ 2^64
  address_load : Mem.loadInt s.dmem s.regs.r9.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.r9.toBitVec + 8) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.r9.toBitVec + 16) 8 = some (used.toNat : Int)
  arena_bound : address.toNat + capacity.toNat ≤ 2^64
  used_bound : used.toNat ≤ capacity.toNat
  arena_nonzero : 0 < capacity.toNat → 0 < address.toNat
  free_mapped : Large.Mapped s.dmem (address + used) (capacity.toNat - used.toNat)
  arena_output : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rdi.toNat 72
  arena_stack : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat - 96) 96
  arena_return : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rsp.toNat 8
  arena_header : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.r9.toNat 24
  header_output : Body.Apart s.regs.r9.toNat 24 s.regs.rdi.toNat 72
  header_stack : Body.Apart s.regs.r9.toNat 24 (s.regs.rsp.toNat - 96) 96
  cursor_return : Body.Apart (s.regs.r9.toNat + 16) 8 s.regs.rsp.toNat 8

/-- Success changes only the Nat pair and the 32-bit status. Failure additionally
zeros bytes 16 through 63. Bytes 68 through 71 are never result writes. -/
def ResultOutside (result : Except NatArithmetic.Failure NatOperand) (out a : Nat) : Prop :=
  match result with
  | .ok _ => Body.Outside a out 16 ∧ Body.Outside a (out + 64) 4
  | .error _ => Body.Outside a out 68

theorem ResultOutside.of_outside {result : Except NatArithmetic.Failure NatOperand}
    {out a : Nat} (outside : Body.Outside a out 72) : ResultOutside result out a := by
  cases result <;> simp only [ResultOutside] <;>
    unfold Body.Outside at * <;> omega

/-- Alignment gaps, unused arena suffixes, and native output padding are framed.
The cursor is writable only when the checked model committed a reservation. -/
def Frame (s : MachineData) (m : DataMem) (outcome : NatArithmetic.Outcome NatOperand) : Prop :=
  ∀ a : BitVec 64,
    ResultOutside outcome.result s.regs.rdi.toNat a.toNat →
    Body.Outside a.toNat (s.regs.rsp.toNat - 96) 96 →
    (∀ r, outcome.allocation = some r →
      Body.Outside a.toNat (s.regs.r9.toNat + 16) 8 ∧
      Body.Outside a.toNat r.pointer (8 * outcome.written.length)) →
    m.get? a = s.dmem.get? a

abbrev Returned := Delimited.Returned

structure Post (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (t : MachineState) : Prop where
  observed : NatArithmetic.AddResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
    (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result
  written : ∀ r,
    (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r →
    NatMemory.wordsAt (widthLoad t.1.dmem) r.pointer
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written
  returned : Returned s ra t
  frame : Frame s t.1.dmem
    (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat)
  cursor : widthLoad t.1.dmem (s.regs.r9.toNat + 16) 8 =
    some (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).used
  left_at : left.At (widthLoad t.1.dmem)
  right_at : right.At (widthLoad t.1.dmem)

/-- The actual result representation, rather than an equal-valued substitute,
refines multiplication of the two original arbitrary-precision operands. -/
theorem Post.value {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} {t : MachineState}
    (post : Post s left right address capacity used ra t) (result : NatOperand)
    (success : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result =
      .ok result) :
    NatArithmetic.operandAt (widthLoad t.1.dmem) s.regs.rdi.toNat result ∧
      result.value = left.value * right.value := by
  have observed := post.observed
  rw [success] at observed
  exact ⟨observed.1, SszNative.NatMul.run_value left right _ _ _ result success⟩

end SszX86.NatMul
