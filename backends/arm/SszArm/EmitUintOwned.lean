import SszArm.EmitObservations
import SszArm.NatToU128Memory
import SszNatNarrow

namespace SszArm.Emit.Uint

open SszNative (NatOperand)
open UintCodec (widthLoad)

variable {s : ArmState} {args : Args} {width number : NatOperand} {size : Nat}

theorem expected_width
    (owned : Owned s args (.uint width) (.uint number) size) : width.value = size := by
  have expected := owned.expected
  simp only [SszNative.Serialize.expectedSize] at expected
  split at expected
  · exact Except.ok.inj expected
  · cases expected

theorem width_fits_word
    (owned : Owned s args (.uint width) (.uint number) size) : width.wordCount ≤ 1 := by
  apply (width.wordCount_le_iff_value_lt 1).2
  simpa only [Nat.mul_one, expected_width owned] using owned.representable

theorem width_capacity
    (owned : Owned s args (.uint width) (.uint number) size) :
    width.value ≤ args.capacity.toNat := by
  rw [expected_width owned]
  exact owned.fitting

theorem body_stack_safe
    (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) : 16 ≤ (r (.GPR 31#5) s).toNat := by
  rw [registers.stack]
  have low := owned.stackLow
  unfold Args.bodySP
  bv_omega

theorem lowering_slot
    (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) :
    ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writesFor args size := by
  have low := owned.stackLow
  have slot : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 176 := by
    rw [registers.stack]
    unfold Args.bodySP
    bv_omega
  simp [slot, writesFor, stackWrites]

theorem operand_source
    (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (pointer : BitVec 64) (words : List (BitVec 64))
    (member : NatOperand.large pointer words ∈ [width, number]) :
    NatCompare.Source s pointer words := by
  have member' : NatOperand.large pointer words ∈
      descriptorOperands (.uint width) ++ valueOperands (.uint number) := by
    simpa [descriptorOperands, valueOperands] using member
  exact NatNarrow.large_source s pointer words (writesFor args size)
    (owned.operand_at _ member') (owned.operandOwned _ member')
    (lowering_slot owned registers) (body_stack_safe owned registers)

theorem operand_words
    (owned : Owned s args (.uint width) (.uint number) size)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (member : NatOperand.large pointer words ∈ [width, number]) :
    NatCompare.Words s pointer words := by
  apply NatNarrow.large_words s pointer words
  exact owned.operand_at _ (by simpa [descriptorOperands, valueOperands] using member)

theorem descriptor_pair
    (owned : Owned s args (.uint width) (.uint number) size) :
    read_mem_bytes 8 (args.descriptor + 8#64) s = width.pointer ∧
    read_mem_bytes 8 (args.descriptor + 16#64) s = width.payload := by
  obtain ⟨pointer, payload, _⟩ := owned.descriptor.2
  constructor
  · apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using Option.some.inj pointer
  · apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, Nat.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.add_assoc] using Option.some.inj payload

theorem number_pair
    (owned : Owned s args (.uint width) (.uint number) size) :
    read_mem_bytes 8 (args.value + 8#64) s = number.pointer ∧
    read_mem_bytes 8 (args.value + 16#64) s = number.payload := by
  obtain ⟨pointer, payload, _⟩ := owned.value_at.2
  constructor
  · apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using Option.some.inj pointer
  · apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, Nat.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.add_assoc] using Option.some.inj payload

end SszArm.Emit.Uint
