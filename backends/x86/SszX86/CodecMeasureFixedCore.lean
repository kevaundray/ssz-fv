import SszX86.CodecMeasureFixedStack
import SszX86.CodecMeasureFixedJump
import SszX86.CodecStack
import SszX86.MeasureCore
import SszX86.DelimitedMemory
import SszFixedSizeResources

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

/-- Native Result<Option<Nat>> observations. None leaves the inactive Nat pair
opaque; failures retain the checked arithmetic error representation verbatim. -/
def ResultAt (observe : Nat → Nat → Option Nat) (out : Nat) :
    Except Serialize.Error (Option NatOperand) → Prop
  | .ok none => observe out 8 = some 0 ∧ observe (out + 64) 4 = some 0
  | .ok (some width) => observe out 8 = some 1 ∧
      NatArithmetic.operandAt observe (out + 8) width ∧ observe (out + 64) 4 = some 0
  | .error error => Measure.ErrorAt observe out error

/-- Every error-copy path copies the full 72-byte representation, including its
opaque final word. Successful paths initialize only active Option fields/status. -/
def ResultWrites (out : BitVec 64) (result : Except Serialize.Error (Option NatOperand))
    (a : BitVec 64) : Prop :=
  match result with
  | .ok none => Codec.InSpan a out 8 ∨ Codec.InSpan a (out + 64) 4
  | .ok (some _) => Codec.InSpan a out 24 ∨ Codec.InSpan a (out + 64) 4
  | .error _ => Codec.InSpan a out 72

abbrev arenaState := Measure.arenaState
abbrev CallsAt := Measure.CallsAt
abbrev AllocationWrites := Measure.AllocationWrites
abbrev Allocated := Measure.Allocated

def Writable (s : MachineData) (bytes : Nat)
    (outcome : Serialize.Outcome (Option NatOperand)) (a : BitVec 64) : Prop :=
  ResultWrites s.regs.rdi.toBitVec outcome.result a ∨
  Codec.StackWrites s.regs.rsp.toBitVec bytes a ∨
  AllocationWrites outcome.calls a ∨
  (Allocated outcome.calls ∧ Codec.InSpan a (s.regs.rdx.toBitVec + 16) 8)

/-- Physical original-entry ownership. Widths, counts, limits, field names and
masks remain the original shared raw descriptor, not a validated schema. -/
structure Owned (s : MachineData) (base : Int64) (r : Codec.Footprint)
    (desc : SszNative.Codec.Desc) (address capacity used ra : BitVec 64) (bytes : Nat) : Prop where
  descriptor : Codec.DescAt s.dmem r s.regs.rsi.toBitVec desc
  table : TableAt s.dmem base
  table_readonly : ∀ i < tableBytes.length, r (tableAddress base + BitVec.ofNat 64 i)
  stack : Codec.StackAt s.dmem s.regs.rsp.toBitVec bytes
  enough : stackBytes desc ≤ bytes
  return_bound : s.regs.rsp.toNat + 8 ≤ 2 ^ 64
  return_load : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  output_bound : s.regs.rdi.toNat + 72 ≤ 2 ^ 64
  output_mapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 72
  output_stack : Body.Apart s.regs.rdi.toNat 72 (s.regs.rsp.toNat - bytes) (bytes + 8)
  header_bound : s.regs.rdx.toNat + 24 ≤ 2 ^ 64
  address_load : Mem.loadInt s.dmem s.regs.rdx.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + 8) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + 16) 8 = some (used.toNat : Int)
  header_output : Body.Apart s.regs.rdx.toNat 24 s.regs.rdi.toNat 72
  header_stack : Body.Apart s.regs.rdx.toNat 24 (s.regs.rsp.toNat - bytes) (bytes + 8)
  arena_bound : address.toNat + capacity.toNat ≤ 2 ^ 64
  used_bound : used.toNat ≤ capacity.toNat
  arena_nonzero : 0 < capacity.toNat → 0 < address.toNat
  arena_mapped : Large.Mapped s.dmem address capacity.toNat
  arena_output : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rdi.toNat 72
  arena_stack : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat - bytes) (bytes + 8)
  arena_header : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rdx.toNat 24
  readonly : ∀ a, r a → ¬ (Codec.InSpan a s.regs.rdi.toBitVec 72 ∨
    Codec.StackWrites s.regs.rsp.toBitVec bytes a ∨
    Codec.InSpan a (s.regs.rdx.toBitVec + 16) 8 ∨
    Codec.InSpan a (address + used) (capacity.toNat - used.toNat))

structure Post (s : MachineData) (desc : SszNative.Codec.Desc)
    (address capacity used ra : BitVec 64) (bytes : Nat) (t : MachineState) : Prop where
  returned : Delimited.Returned s ra t
  observed : ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
    (FixedSize.measureFixed desc (arenaState address capacity used)).result
  cursor : widthLoad t.1.dmem (s.regs.rdx.toNat + 16) 8 =
    some (FixedSize.measureFixed desc (arenaState address capacity used)).used
  calls : CallsAt (widthLoad t.1.dmem)
    (FixedSize.measureFixed desc (arenaState address capacity used)).calls
  frame : Codec.MemoryFrame s.dmem t.1.dmem
    (Writable s bytes (FixedSize.measureFixed desc (arenaState address capacity used)))
  descriptor : ∀ r, Codec.DescAt s.dmem r s.regs.rsi.toBitVec desc →
    (∀ a, r a → ¬ Writable s bytes (FixedSize.measureFixed desc (arenaState address capacity used)) a) →
    Codec.DescAt t.1.dmem r s.regs.rsi.toBitVec desc
  header : widthLoad t.1.dmem s.regs.rdx.toNat 8 = some address.toNat ∧
    widthLoad t.1.dmem (s.regs.rdx.toNat + 8) 8 = some capacity.toNat

end SszX86.CodecMeasureFixed
