import SszX86.BitVectorCore

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- The deepest live helper frame starts 72 bytes below body RSP. Body work ends
at offset 224; the prologue saves at 312..367 are read-only until the epilogue. -/
def workStart (s : MachineData) : Nat := s.regs.rsp.toNat - 72
def workSize : Nat := 296

/-- Only writable regions are excluded. Immutable descriptors, limbs and input
bytes may alias one another, the used arena prefix, and the read-only saves. -/
structure Protected (s : MachineData) (address capacity used : BitVec 64)
    (p n : Nat) : Prop where
  bound : p + n ≤ 2^64
  output : Body.Apart p n s.regs.rdi.toNat 80
  work : Body.Apart p n (workStart s) workSize
  cursor : Body.Apart p n (s.regs.rbx.toNat + 16) 8
  arena : Body.Apart p n (address.toNat + used.toNat) (capacity.toNat - used.toNat)

def OperandProtected (s : MachineData) (address capacity used : BitVec 64) :
    NatOperand → Prop
  | .small _ => True
  | .large p words => Protected s address capacity used p.toNat (8 * words.length)

/-- Physical post-dispatch entry ABI. No internal quotient, helper execution,
canonical Nat, allocation success or semantic result is assumed. -/
structure Owned (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used : BitVec 64) : Prop where
  output_bound : s.regs.rdi.toNat + 80 ≤ 2^64
  output_mapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 80
  stack_low : 72 ≤ s.regs.rsp.toNat
  stack_bound : s.regs.rsp.toNat + 368 ≤ 2^64
  work_mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 72#64) workSize
  saved_at : SavedAt s.dmem s.regs.rsp.toBitVec saved
  output_work : Body.Apart s.regs.rdi.toNat 80 (workStart s) workSize
  output_saved : Body.Apart s.regs.rdi.toNat 80 (s.regs.rsp.toNat + 312) 56
  descriptor : NatArithmetic.operandAt (widthLoad s.dmem) (s.regs.rbp.toNat + 8) length
  descriptor_owned : Protected s address capacity used s.regs.rbp.toNat 24
  operand_owned : OperandProtected s address capacity used length
  data_length : data.size = s.regs.r14.toNat
  source : SszNative.ByteView.BytesAt (widthLoad s.dmem) s.regs.rdx.toNat data
  source_owned : Protected s address capacity used s.regs.rdx.toNat data.size
  header_bound : s.regs.rbx.toNat + 24 ≤ 2^64
  address_load : Mem.loadInt s.dmem s.regs.rbx.toBitVec 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt s.dmem (s.regs.rbx.toBitVec + 8) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt s.dmem (s.regs.rbx.toBitVec + 16) 8 = some (used.toNat : Int)
  arena_bound : address.toNat + capacity.toNat ≤ 2^64
  used_bound : used.toNat ≤ capacity.toNat
  arena_nonzero : 0 < capacity.toNat → 0 < address.toNat
  arena_mapped : Large.Mapped s.dmem address capacity.toNat
  arena_output : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rdi.toNat 80
  arena_work : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (workStart s) workSize
  arena_saved : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat + 312) 56
  arena_header : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rbx.toNat 24
  header_output : Body.Apart s.regs.rbx.toNat 24 s.regs.rdi.toNat 80
  header_work : Body.Apart s.regs.rbx.toNat 24 (workStart s) workSize
  cursor_saved : Body.Apart (s.regs.rbx.toNat + 16) 8 (s.regs.rsp.toNat + 312) 56

/-- The caller's free suffix is not a blanket write permission: only the exact
helper limb writes are excluded. Reservation alignment padding is preserved. -/
def Frame (s : MachineData) (m : DataMem) (outcome : SszNative.BitVector.Outcome) : Prop :=
  ∀ a : BitVec 64,
    Body.Outside a.toNat s.regs.rdi.toNat 80 →
    Body.Outside a.toNat (workStart s) workSize →
    Body.Outside a.toNat (s.regs.rbx.toNat + 16) 8 →
    (∀ span ∈ outcome.writes, Body.Outside a.toNat span.1 span.2) →
    m.get? a = s.dmem.get? a

/-- Complete outer Value/Error observation and retained allocator effects. -/
structure Post (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used : BitVec 64) (t : MachineState) : Prop where
  observed : SszNative.BitVector.ResultAt (widthLoad t.1.dmem)
    s.regs.rdi.toNat s.regs.rdx.toNat data
    (SszNative.BitVector.run length data ⟨address.toNat, capacity.toNat, used.toNat⟩).result
  written : (SszNative.BitVector.run length data
    ⟨address.toNat, capacity.toNat, used.toNat⟩).writtenAt (widthLoad t.1.dmem)
  returned : Body.Returned s saved t
  frame : Frame s t.1.dmem
    (SszNative.BitVector.run length data ⟨address.toNat, capacity.toNat, used.toNat⟩)
  arenaBase : widthLoad t.1.dmem s.regs.rbx.toNat 8 = some address.toNat
  arenaCapacity : widthLoad t.1.dmem (s.regs.rbx.toNat + 8) 8 = some capacity.toNat
  cursor : widthLoad t.1.dmem (s.regs.rbx.toNat + 16) 8 = some
    (SszNative.BitVector.run length data ⟨address.toNat, capacity.toNat, used.toNat⟩).used
  descriptor : NatArithmetic.operandAt (widthLoad t.1.dmem) (s.regs.rbp.toNat + 8) length
  source : SszNative.ByteView.BytesAt (widthLoad t.1.dmem) s.regs.rdx.toNat data

/-- Erasure keeps host scratch failure outside the pinned SSZ result. -/
theorem Post.erased {s : MachineData} {saved : Saved} {length : NatOperand}
    {data : Ssz.Bytes} {address capacity used : BitVec 64} {t : MachineState}
    (post : Post s saved length data address capacity used t) :
    match (SszNative.BitVector.run length data
      ⟨address.toNat, capacity.toNat, used.toNat⟩).erase data with
    | .ok value => SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat value
    | .error reason => SszNative.BitVector.failureAt (widthLoad t.1.dmem) s.regs.rdi.toNat reason :=
  SszNative.BitVector.ResultAt.erased _ _ _ _ _ post.observed

end SszX86.BitVector
