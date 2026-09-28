import SszX86.NatMulMemoryStack

namespace SszX86.NatMul
open SszNative
open UintCodec

/-- The free suffix is disjoint from the local area and nested-call return slot.
The used prefix is deliberately absent, so immutable input aliases remain legal. -/
theorem Owned.free_stack_disjoint {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra) :
    Large.Disjoint (address+used) ((s.regs.rsp.toBitVec-88)-8)
      (capacity.toNat-used.toNat) 48 := by
  intro i hi j hj equal
  have apart := owned.arena_stack
  have low := owned.stack_low
  have storage := owned.arena_bound
  have cursor := owned.used_bound
  change 96 ≤ s.regs.rsp.toBitVec.toNat at low
  change Body.Apart (address.toNat+used.toNat) (capacity.toNat-used.toNat)
    (s.regs.rsp.toBitVec.toNat-96) 96 at apart
  unfold Body.Apart at apart
  bv_omega

/-- Every initial stack subinterval remains mapped after the prologue. -/
theorem Owned.stack_subrange {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    (off count : Nat) (inside : off+count ≤ 96) :
    Large.Mapped (pushedMem s) ((s.regs.rsp.toBitVec-96) + BitVec.ofNat 64 off) count :=
  Delimited.Reservation.mapped_subrange _ _ 96 off count
    (pushed_mapped s _ _ owned.stack_mapped) inside

/-- The word helper's restored-entry activation is a strict subinterval of the
main envelope; it is not nested below the unreleased 88-byte main frame. -/
theorem Owned.word_stack_mapped {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra) :
    Large.Mapped (pushedMem s) (s.regs.rsp.toBitVec-64) 64 := by
  have hm := owned.stack_subrange 32 64 (by decide)
  have pointer : (s.regs.rsp.toBitVec-96) + BitVec.ofNat 64 32 = s.regs.rsp.toBitVec-64 := by
    bv_omega
  rwa [pointer] at hm

end SszX86.NatMul
