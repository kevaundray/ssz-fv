import SszArm.MeasureUintProduced

namespace SszArm.Measure.Uint

open SszNative (NatOperand)
open UintCodec (widthLoad)

variable {s : ArmState} {args : Args} {uintCap number : NatOperand}

theorem body_stack_safe (owned : Owned s args (.uint uintCap) (.uint number))
    (stack : r (.GPR 31#5) s = args.bodySP) : 16 ≤ (r (.GPR 31#5) s).toNat := by
  rw [stack]
  have low := owned.stackLow
  unfold Args.bodySP
  bv_omega

theorem lowering_slot (owned : Owned s args (.uint uintCap) (.uint number))
    (stack : r (.GPR 31#5) s = args.bodySP) :
    ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writesFor args (outcome s args (.uint uintCap) (.uint number)) := by
  have low := owned.stackLow
  have position : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 288 := by
    rw [stack]
    unfold Args.bodySP
    bv_omega
  simp [position, writesFor, localWrites, stackWrites, bodyStackWrites]

theorem operand_source (owned : Owned s args (.uint uintCap) (.uint number))
    (stack : r (.GPR 31#5) s = args.bodySP) (pointer : BitVec 64) (words : List (BitVec 64))
    (member : NatOperand.large pointer words ∈ [uintCap, number]) :
    NatCompare.Source s pointer words := by
  have member' : NatOperand.large pointer words ∈
      Emit.descriptorOperands (.uint uintCap) ++ Emit.valueOperands (.uint number) := by
    simpa [Emit.descriptorOperands, Emit.valueOperands] using member
  exact NatNarrow.large_source s pointer words (writesFor args (outcome s args (.uint uintCap) (.uint number)))
    (owned.operand_at _ member') (owned.operandOwned _ member')
    (lowering_slot owned stack) (body_stack_safe owned stack)

theorem operand_words (owned : Owned s args (.uint uintCap) (.uint number))
    (pointer : BitVec 64) (words : List (BitVec 64))
    (member : NatOperand.large pointer words ∈ [uintCap, number]) :
    NatCompare.Words s pointer words := by
  apply NatNarrow.large_words s pointer words
  exact owned.operand_at _ (by simpa [Emit.descriptorOperands, Emit.valueOperands] using member)

theorem descriptor_pair (owned : Owned s args (.uint uintCap) (.uint number)) :
    read_mem_bytes 8 (args.descriptor + 8#64) s = uintCap.pointer ∧
    read_mem_bytes 8 (args.descriptor + 16#64) s = uintCap.payload := by
  obtain ⟨pointer, payload, _⟩ := owned.descriptor.2
  constructor
  · apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using Option.some.inj pointer
  · apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, Nat.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.add_assoc] using Option.some.inj payload

theorem number_pair (owned : Owned s args (.uint uintCap) (.uint number)) :
    read_mem_bytes 8 (args.value + 8#64) s = number.pointer ∧
    read_mem_bytes 8 (args.value + 16#64) s = number.payload := by
  obtain ⟨pointer, payload, _⟩ := owned.value_at.2
  constructor
  · apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using Option.some.inj pointer
  · apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, Nat.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.add_assoc] using Option.some.inj payload

end SszArm.Measure.Uint
