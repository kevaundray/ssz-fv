import SszX86.NatAddCore
import SszX86.DelimitedMemory

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Read-only regions may overlap one another and the consumed arena prefix. -/
structure Protected (s : MachineData) (address capacity used : BitVec 64)
    (p n : Nat) : Prop where
  bound : p + n ≤ 2^64
  output : Body.Apart p n s.regs.rdi.toNat 68
  activation : Body.Apart p n (s.regs.rsp.toNat - 48) 48
  cursor : Body.Apart p n (s.regs.r9.toNat + 16) 8
  arena : Body.Apart p n (address.toNat + used.toNat) (capacity.toNat - used.toNat)

def OperandProtected (s : MachineData) (address capacity used : BitVec 64) :
    NatOperand → Prop
  | .small _ => True
  | .large p words => Protected s address capacity used p.toNat (8 * words.length)

/-- The actual Rust ABI uses an explicit output pointer in RDI, with the two
Nat pairs in RSI/RDX and RCX/R8 and the arena in R9. All premises are physical. -/
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
  output_bound : s.regs.rdi.toNat + 68 ≤ 2^64
  output_mapped : OutputMapped s
  return_bound : s.regs.rsp.toNat + 8 ≤ 2^64
  return_load : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  stack_low : 48 ≤ s.regs.rsp.toNat
  stack_mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48
  output_return : Body.Apart s.regs.rdi.toNat 68 s.regs.rsp.toNat 8
  output_stack : Body.Apart s.regs.rdi.toNat 68 (s.regs.rsp.toNat - 48) 48
  header_bound : s.regs.r9.toNat + 24 ≤ 2^64
  address_load : Mem.loadInt s.dmem s.regs.r9.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.r9.toBitVec + 8) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.r9.toBitVec + 16) 8 = some (used.toNat : Int)
  arena_bound : address.toNat + capacity.toNat ≤ 2^64
  used_bound : used.toNat ≤ capacity.toNat
  arena_nonzero : 0 < capacity.toNat → 0 < address.toNat
  arena_mapped : Large.Mapped s.dmem address capacity.toNat
  arena_output : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rdi.toNat 68
  arena_stack : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat - 48) 48
  arena_return : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rsp.toNat 8
  arena_header : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.r9.toNat 24
  header_output : Body.Apart s.regs.r9.toNat 24 s.regs.rdi.toNat 68
  header_stack : Body.Apart s.regs.r9.toNat 24 (s.regs.rsp.toNat - 48) 48
  cursor_return : Body.Apart (s.regs.r9.toNat + 16) 8 s.regs.rsp.toNat 8

/-- Padding is excluded: only the exact complete written buffer can change. -/
def Frame (s : MachineData) (m : DataMem) (outcome : NatArithmetic.Outcome NatOperand) : Prop :=
  ∀ a : BitVec 64,
    Body.Outside a.toNat s.regs.rdi.toNat 68 →
    Body.Outside a.toNat (s.regs.rsp.toNat - 48) 48 →
    (∀ r, outcome.allocation = some r →
      Body.Outside a.toNat (s.regs.r9.toNat + 16) 8 ∧
      Body.Outside a.toNat r.pointer (8 * outcome.written.length)) →
    m.get? a = s.dmem.get? a

abbrev Returned := Delimited.Returned

structure Post (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (t : MachineState) : Prop where
  observed : NatArithmetic.AddResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
    (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).result
  written : ∀ r,
    (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r →
    NatMemory.wordsAt (widthLoad t.1.dmem) r.pointer
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written
  returned : Returned s ra t
  frame : Frame s t.1.dmem
    (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat)
  cursor : widthLoad t.1.dmem (s.regs.r9.toNat + 16) 8 =
    some (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used
  left_at : left.At (widthLoad t.1.dmem)
  right_at : right.At (widthLoad t.1.dmem)

/-- The arithmetic corollary applies to the exact representation in the output,
not to an existential equal-valued replacement for that representation. -/
theorem Post.value {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} {t : MachineState}
    (post : Post s left right address capacity used ra t) (result : NatOperand)
    (success : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).result =
      .ok result) :
    NatArithmetic.operandAt (widthLoad t.1.dmem) s.regs.rdi.toNat result ∧
      result.value = left.value + right.value := by
  have observed := post.observed
  rw [success] at observed
  exact ⟨observed.1, SszNative.NatAdd.run_value left right _ _ _ result success⟩

end SszX86.NatAdd
