import SszX86.CodecIsFixedStack
import SszX86.CodecIsFixedReturn
import SszX86.CodecIsFixedTable
import SszX86.CodecStack
import SszX86.DelimitedMemory
import SszFixedSize

namespace SszX86.CodecIsFixed
open SszNative UintCodec

/-- All observations are at the original function entry. The one readonly
footprint contains the complete finite descriptor graph and the actual dispatch
bytes; its regions may overlap arbitrarily. -/
structure Owned (s : MachineData) (base : Int64) (r : Codec.Footprint)
    (desc : SszNative.Codec.Desc) (ra : BitVec 64) (bytes : Nat) : Prop where
  descriptor : Codec.DescAt s.dmem r s.regs.rdi.toBitVec desc
  table : TableAt s.dmem base
  table_readonly : ∀ i < tableBytes.length, r (tableAddress base + BitVec.ofNat 64 i)
  stack : Codec.StackAt s.dmem s.regs.rsp.toBitVec bytes
  enough : stackBytes desc ≤ bytes
  return_bound : s.regs.rsp.toNat + 8 ≤ 2 ^ 64
  return_load : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 =
    some (Int.ofBytes (wordBytes ra))
  readonly : ∀ a, r a → ¬ Codec.StackWrites s.regs.rsp.toBitVec bytes a

/-- The result is the native Boolean in AL, not a promise about unspecified
high RAX bytes. Stack mapping is retained for the caller's next field visit. -/
structure Post (s : MachineData) (desc : SszNative.Codec.Desc) (ra : BitVec 64)
    (bytes : Nat) (t : MachineState) : Prop where
  returned : Delimited.Returned s ra t
  result : t.1.regs.rax.toBitVec.setWidth 8 =
    if FixedSize.isFixed desc then 1#8 else 0#8
  frame : Codec.MemoryFrame s.dmem t.1.dmem (Codec.StackWrites s.regs.rsp.toBitVec bytes)
  «mapped» : ∀ p n, Large.Mapped s.dmem p n → Large.Mapped t.1.dmem p n

/-- A body has already saved RBX/R14. Its own scratch allowance is below the
current RSP; the saved words and original return address are above it. -/
structure BodyPost (s : MachineData) (bytes : Nat) (value : Bool)
    (base : Int64) (t : MachineState) : Prop where
  pc : t.2 = if value then base + 53 else base + 124
  result : t.1.regs.rax.toBitVec.setWidth 8 = if value then 1#8 else 0#8
  stack : t.1.regs.rsp = s.regs.rsp
  rbp : t.1.regs.rbp = s.regs.rbp
  r12 : t.1.regs.r12 = s.regs.r12
  r13 : t.1.regs.r13 = s.regs.r13
  r15 : t.1.regs.r15 = s.regs.r15
  vectors : t.1.zmms = s.zmms
  frame : Codec.MemoryFrame s.dmem t.1.dmem (Codec.StackWrites s.regs.rsp.toBitVec bytes)
  «mapped» : ∀ p n, Large.Mapped s.dmem p n → Large.Mapped t.1.dmem p n

theorem saved_frame (s : MachineData) (bytes : Nat) (enough : 24 ≤ bytes) :
    Codec.MemoryFrame s.dmem (savedMem s) (Codec.StackWrites s.regs.rsp.toBitVec bytes) := by
  intro a outside
  apply saved_lookup s a
  intro i hi equal
  apply outside
  apply Codec.stack_subspan s.regs.rsp.toBitVec 0 24 bytes (by omega) a
  exact ⟨i, hi, equal⟩

theorem table_frame {m n : DataMem} {base : Int64} {r writable : Codec.Footprint}
    (table : TableAt m base)
    (read : ∀ i < tableBytes.length, r (tableAddress base + BitVec.ofNat 64 i))
    (frame : Codec.MemoryFrame m n writable)
    (readonly : ∀ a, r a → ¬ writable a) : TableAt n base := by
  intro i hi
  rw [frame _ (readonly _ (read i hi))]
  exact table i hi

theorem Owned.activation_mapped {s : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {ra : BitVec 64} {bytes : Nat}
    (owned : Owned s base r desc ra bytes) :
    Large.Mapped s.dmem (s.regs.rsp.toBitVec - 24) 24 := by
  have activation := owned.stack.substack 0 24
    (Nat.le_trans (stackBytes_activation desc) owned.enough)
  simpa only [BitVec.ofNat_zero, BitVec.sub_zero] using activation.mapped

end SszX86.CodecIsFixed
