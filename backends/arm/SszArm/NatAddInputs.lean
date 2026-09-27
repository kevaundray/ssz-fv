import SszArm.NatAddContract
import SszArm.NatAddBlocks

namespace SszArm.NatAdd

open UintCodec
open Delimited (Protected MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The comparison pilot's readonly source predicate is exactly the static
lowering-slot part of this function's stronger caller ownership. -/
theorem source_of_owned (s : ArmState)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (input : (SszNative.NatOperand.large pointer words).At (widthLoad s))
    (owned : OperandOwned (writesFor s result) (.large pointer words)) :
    NatCompare.Source s pointer words := by
  refine ⟨stack, input.2.2.1, ?_⟩
  by_cases empty : words = []
  · exact Or.inl empty
  · right
    have slot : ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writesFor s result := by
      cases allocated : result.allocation <;> simp [writesFor, allocated, localWrites]
    change Protected (writesFor s result) pointer.toNat (8 * words.length) at owned
    rcases owned with zero | separate
    · have : words.length = 0 := by omega
      exact False.elim (empty (List.eq_nil_of_length_eq_zero this))
    · have apart := separate _ slot
      change pointer.toNat + 8 * words.length ≤ (r (.GPR 31#5) s).toNat - 16 ∨
        (r (.GPR 31#5) s).toNat ≤ pointer.toNat
      omega

theorem words_of_at (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64))
    (input : (SszNative.NatOperand.large pointer words).At (widthLoad s)) :
    NatCompare.Words s pointer words := by
  intro i
  apply BitVec.eq_of_toNat_eq
  have hi := Option.some.inj (input.2.2.2 i)
  simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using hi

theorem operand_of_owned (s : ArmState)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand)
    (operand : SszNative.NatOperand)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (input : operand.At (widthLoad s))
    (owned : OperandOwned (writesFor s result) operand) :
    NatCompare.Operand s operand.pointer operand.payload operand.words := by
  cases operand with
  | small word => exact Or.inl ⟨rfl, rfl⟩
  | large pointer words =>
    have positive := input.1
    have count : words.length < 2^64 := by have := input.2.2.1; omega
    refine Or.inr ⟨?_, ?_, source_of_owned s result pointer words stack input owned,
      words_of_at s pointer words input⟩
    · intro zero
      simp only [SszNative.NatOperand.pointer] at zero
      simp [zero] at positive
    · simp only [SszNative.NatOperand.payload, SszNative.NatOperand.words,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt count]

theorem Owned.operands {s : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right) :
    NatCompare.Operand s (r (.GPR 1#5) s) (r (.GPR 2#5) s) left.words ∧
    NatCompare.Operand s (r (.GPR 3#5) s) (r (.GPR 4#5) s) right.words := by
  rw [owned.leftPointer, owned.leftPayload, owned.rightPointer, owned.rightPayload]
  exact ⟨operand_of_owned s _ left owned.stackBound owned.leftAt owned.leftOwned,
    operand_of_owned s _ right owned.stackBound owned.rightAt owned.rightOwned⟩

theorem scan_memory {s t : ArmState} (hf : NatCompare.Frame s t)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) : MemoryFrame (localWrites s) s t := by
  intro a outside
  apply hf.memory
  have apart := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [localWrites])
  omega

theorem scan_preserves_inputs {s t : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right) (hf : NatCompare.Frame s t) :
    InputsPreserved s t left right :=
  inputs_preserved owned (local_frame _ (scan_memory hf owned.stackBound))

end SszArm.NatAdd
