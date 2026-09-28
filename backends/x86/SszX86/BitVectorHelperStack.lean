import SszX86.BitVectorProtected
import SszX86.BitVectorStackReads

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem division_stack_protected (s u : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (owned : Owned {s with dmem := u.dmem} saved length data address capacity used)
    (outputNat : u.regs.rdi.toNat = s.regs.rsp.toNat + 16)
    (stackNat : u.regs.rsp.toNat = s.regs.rsp.toNat - 8)
    (arena : u.regs.r8.toBitVec = s.regs.rbx.toBitVec)
    (off count : Nat) (inside : off + count ≤ 224)
    (privateApart : off + count ≤ 16 ∨ 84 ≤ off) :
    NatDivision.Protected u address capacity used (s.regs.rsp.toNat + off) count := by
  have low : 72 ≤ s.regs.rsp.toNat := owned.stack_low
  have high : s.regs.rsp.toNat + 368 ≤ 2^64 := owned.stack_bound
  have arenaNat : u.regs.r8.toNat = s.regs.rbx.toNat := congrArg BitVec.toNat arena
  have headerWork : Body.Apart s.regs.rbx.toNat 24 (s.regs.rsp.toNat - 72) 296 := owned.header_work
  have arenaWork : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat - 72) 296 := owned.arena_work
  constructor
  · omega
  · unfold Body.Apart
    omega
  · unfold Body.Apart
    omega
  · unfold Body.Apart at headerWork ⊢
    omega
  · unfold Body.Apart at arenaWork ⊢
    omega

theorem add_stack_protected (s u : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (owned : Owned {s with dmem := u.dmem} saved length data address capacity used)
    (outputNat : u.regs.rdi.toNat = s.regs.rsp.toNat + 16)
    (stackNat : u.regs.rsp.toNat = s.regs.rsp.toNat - 8)
    (arena : u.regs.r9.toBitVec = s.regs.rbx.toBitVec)
    (off count : Nat) (inside : off + count ≤ 224)
    (privateApart : off + count ≤ 16 ∨ 84 ≤ off) :
    NatAdd.Protected u address capacity used (s.regs.rsp.toNat + off) count := by
  have hp := division_stack_protected s {u with regs := {u.regs with r8 := u.regs.r9}}
    saved length data address capacity used owned outputNat stackNat arena off count inside privateApart
  refine ⟨hp.bound, hp.output, ?_, hp.cursor, hp.arena⟩
  have low : 72 ≤ s.regs.rsp.toNat := owned.stack_low
  unfold Body.Apart
  omega

theorem division_stack_load (s u : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : NatDivision.Owned u operand divisor address capacity used ra)
    (m : DataMem) (frame : NatDivision.Frame u m
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat))
    (off count : Nat)
    (hp : NatDivision.Protected u address capacity used (s.regs.rsp.toNat + off) count) :
    Mem.loadInt m (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count =
      Mem.loadInt u.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count := by
  apply memmove_loadInt_congr
  intro i hi
  have equality := NatDivision.preserves_region u operand divisor address capacity used ra
    owned m frame (s.regs.rsp.toNat + off) count hp i hi
  have pointer : BitVec.ofNat 64 (s.regs.rsp.toNat + off + i) =
      s.regs.rsp.toBitVec + BitVec.ofNat 64 off + BitVec.ofNat 64 i := by
    change BitVec.ofNat 64 (s.regs.rsp.toBitVec.toNat + off + i) = _
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simpa only [pointer] using equality

theorem add_stack_load (s u : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64)
    (owned : NatAdd.Owned u left right address capacity used ra)
    (m : DataMem) (frame : NatAdd.Frame u m
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat))
    (off count : Nat)
    (hp : NatAdd.Protected u address capacity used (s.regs.rsp.toNat + off) count) :
    Mem.loadInt m (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count =
      Mem.loadInt u.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count := by
  apply memmove_loadInt_congr
  intro i hi
  have equality := NatAdd.preserves_region u left right address capacity used ra
    owned m frame (s.regs.rsp.toNat + off) count hp i hi
  have pointer : BitVec.ofNat 64 (s.regs.rsp.toNat + off + i) =
      s.regs.rsp.toBitVec + BitVec.ofNat 64 off + BitVec.ofNat 64 i := by
    change BitVec.ofNat 64 (s.regs.rsp.toBitVec.toNat + off + i) = _
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simpa only [pointer] using equality

end SszX86.BitVector
