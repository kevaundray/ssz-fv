import SszX86.BitListCore

namespace SszX86.BitList
open SszNative UintCodec BoolCodec

/-- The tail helper reuses bytes 256..359 of the already-restored activation.
The ordinary call uses the 112 bytes below bodySP and its local Some value. -/
def workStart (s : MachineData) (tail : Bool) : Nat :=
  if tail then s.regs.rsp.toNat + 256 else s.regs.rsp.toNat - 112

def workBytes (tail : Bool) : Nat := if tail then 104 else 152

structure Protected (s : MachineData) (tail : Bool)
    (address capacity used : BitVec 64) (p n : Nat) : Prop where
  bound : p + n ≤ 2^64
  output : Body.Apart p n s.regs.rdi.toNat 80
  work : Body.Apart p n (workStart s tail) (workBytes tail)
  cursor : Body.Apart p n (s.regs.rbx.toNat + 16) 8
  arena : Body.Apart p n (address.toNat + used.toNat) (capacity.toNat - used.toNat)

/-- Original wrapper ownership, before any of its instructions have executed.
Only the available arena suffix is exclusive; used bytes and immutable inputs
may alias. Output ownership covers the complete physical 80-byte object. -/
structure Owned (s : MachineData) (saved : Saved) (tail : Bool) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) : Prop where
  output_bound : s.regs.rdi.toNat + 80 ≤ 2^64
  output_mapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 80
  stack_low : tail = false → 112 ≤ s.regs.rsp.toNat
  stack_bound : s.regs.rsp.toNat + 368 ≤ 2^64
  work_mapped : Large.Mapped s.dmem (BitVec.ofNat 64 (workStart s tail)) (workBytes tail)
  saved : SavedAt s.dmem s.regs.rsp.toBitVec saved
  output_work : Body.Apart s.regs.rdi.toNat 80 (workStart s tail) (workBytes tail)
  output_saved : Body.Apart s.regs.rdi.toNat 80 (s.regs.rsp.toNat + 312) 56
  length : data.size = s.regs.r14.toNat
  source : Large.BytesAt s.dmem s.regs.rdx.toBitVec data
  source_owned : Protected s tail address capacity used s.regs.rdx.toNat data.size
  descriptor : Protected s tail address capacity used s.regs.rbp.toNat (if tail then 32 else 24)
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
    (workStart s tail) (workBytes tail)
  arena_saved : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat + 312) 56
  arena_header : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rbx.toNat 24
  header_output : Body.Apart s.regs.rbx.toNat 24 s.regs.rdi.toNat 80
  header_work : Body.Apart s.regs.rbx.toNat 24 (workStart s tail) (workBytes tail)
  cursor_saved : Body.Apart (s.regs.rbx.toNat + 16) 8 (s.regs.rsp.toNat + 312) 56

structure ListOwned (s : MachineData) (saved : Saved) (cap : Nat)
    (pointer payload : BitVec 64) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) : Prop extends Owned s saved false data address capacity used where
  pointer_load : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8) 8 = some (pointer.toNat : Int)
  payload_load : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16) 8 = some (payload.toNat : Int)
  cap_pair : NatMemory.Pair (widthLoad s.dmem) pointer payload cap
  borrowed : ∀ limbs, NatMemory.largeAt (widthLoad s.dmem) (s.regs.rbp.toNat + 8)
    pointer.toNat limbs → Protected s false address capacity used pointer.toNat (8 * limbs.length)

structure ProgressiveOwned (s : MachineData) (saved : Saved) (limit : Option Nat)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    : Prop extends Owned s saved true data address capacity used where
  option_at : NatMemory.OptionAt (widthLoad s.dmem) (s.regs.rbp.toNat + 8) limit
  borrowed : ∀ cap, limit = some cap → ∀ p limbs,
    NatMemory.largeAt (widthLoad s.dmem) (s.regs.rbp.toNat + 16) p limbs →
    Protected s true address capacity used p (8 * limbs.length)

/-- The full committed resource model is retained in the native postcondition. -/
def Frame (s : MachineData) (tail : Bool) (m : DataMem)
    (reserved : Option SszNative.Arena.Reservation) : Prop :=
  ∀ a : BitVec 64,
    Body.Outside a.toNat s.regs.rdi.toNat 76 →
    Body.Outside a.toNat (workStart s tail) (workBytes tail) →
    (∀ r, reserved = some r → Body.Outside a.toNat (s.regs.rbx.toNat + 16) 8 ∧
      Body.Outside a.toNat r.pointer 16) →
    m.get? a = s.dmem.get? a

structure Returned (s : MachineData) (saved : Saved) (t : MachineState) : Prop where
  pc : t.2 = Int64.ofBitVec saved.rip
  sp : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 368
  rbx : t.1.regs.rbx.toBitVec = saved.rbx
  rbp : t.1.regs.rbp.toBitVec = saved.rbp
  r12 : t.1.regs.r12.toBitVec = saved.r12
  r13 : t.1.regs.r13.toBitVec = saved.r13
  r14 : t.1.regs.r14.toBitVec = saved.r14
  r15 : t.1.regs.r15.toBitVec = saved.r15
  simd : t.1.zmms = s.zmms
  returnSlot : Mem.loadInt t.1.dmem (s.regs.rsp.toBitVec + 360) 8 =
    some (Int.ofBytes (wordBytes saved.rip))

structure Post (s : MachineData) (saved : Saved) (tail : Bool) (limit : Option Nat)
    (data : Ssz.Bytes) (address capacity used : BitVec 64) (t : MachineState) : Prop where
  observed : SszNative.Delimited.ResultAt (widthLoad t.1.dmem)
    s.regs.rdi.toNat s.regs.rdx.toNat (if tail then s.regs.rbp.toNat + 8 else s.regs.rbp.toNat) data
    (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩)
  prepared : SszNative.Delimited.Outcome.PreparedAt (widthLoad t.1.dmem)
    (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩)
  returned : Returned s saved t
  frame : Frame s tail t.1.dmem
    (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩).allocation
  cursor : widthLoad t.1.dmem (s.regs.rbx.toNat + 16) 8 =
    some (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩).used

end SszX86.BitList
