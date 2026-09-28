import SszArm.NatMulActivationFrame
import SszArm.NatAddInputs

namespace SszArm.NatMul

open UintCodec (widthLoad)
open Delimited (Protected)

theorem activation_scan_covered (s : ArmState)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand)
    (stack : 144 ≤ (r (.GPR 31#5) s).toNat) :
    BitVector.Covers (writesFor s result)
      [((r (.GPR 31#5) (activated s)).toNat - 16, 16)] := by
  intro span member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst span
  refine ⟨((r (.GPR 31#5) s).toNat - 144, 144), ?_, ?_, ?_⟩
  · cases allocated : result.allocation <;> cases value : result.result <;>
      simp [writesFor, localWrites, allocated, value]
  · rw [activated_sp]; bv_omega
  · rw [activated_sp]; bv_omega

theorem activation_operand (s : ArmState)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand)
    (operand : SszNative.NatOperand)
    (stack : 144 ≤ (r (.GPR 31#5) s).toNat)
    (input : operand.At (widthLoad s))
    (owned : NatAdd.OperandOwned (writesFor s result) operand) :
    NatCompare.Operand (activated s) operand.pointer operand.payload operand.words := by
  have frame := (activation_covered s result).frame (activation_frame s (by omega))
  have current := NatAdd.operand_at_preserved frame operand input owned
  have slotBound : 16 ≤ (r (.GPR 31#5) (activated s)).toNat := by
    rw [activated_sp]; bv_omega
  cases operand with
  | small word => exact Or.inl ⟨rfl, rfl⟩
  | large pointer words =>
    have positive := current.1
    have count : words.length < 2^64 := by have bound := current.2.2.1; omega
    have protectedSlot : Protected [((r (.GPR 31#5) (activated s)).toNat - 16, 16)]
        pointer.toNat (8 * words.length) :=
      (activation_scan_covered s result stack).protected owned
    have source : NatCompare.Source (activated s) pointer words := by
      refine ⟨slotBound, current.2.2.1, ?_⟩
      rcases protectedSlot with empty | separate
      · left; apply List.eq_nil_of_length_eq_zero; omega
      · right
        have apart := separate _ (by simp)
        change pointer.toNat + 8 * words.length ≤ (r (.GPR 31#5) (activated s)).toNat - 16 ∨
          (r (.GPR 31#5) (activated s)).toNat ≤ pointer.toNat
        omega
    refine Or.inr ⟨?_, ?_, source, NatAdd.words_of_at _ pointer words current⟩
    · intro zero
      simp only [SszNative.NatOperand.pointer] at zero
      simp [zero] at positive
    · simp only [SszNative.NatOperand.payload, SszNative.NatOperand.words,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt count]

theorem activated_operands {s : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right) :
    NatCompare.Operand (activated s) (r (.GPR 1#5) (activated s))
      (r (.GPR 2#5) (activated s)) left.words ∧
    NatCompare.Operand (activated s) (r (.GPR 3#5) (activated s))
      (r (.GPR 4#5) (activated s)) right.words := by
  rw [activated_registers s 1#5 (by decide), activated_registers s 2#5 (by decide),
    activated_registers s 3#5 (by decide), activated_registers s 4#5 (by decide),
    owned.leftPointer, owned.leftPayload, owned.rightPointer, owned.rightPayload]
  exact ⟨activation_operand s _ left owned.stackBound owned.leftAt owned.leftOwned,
    activation_operand s _ right owned.stackBound owned.rightAt owned.rightOwned⟩

end SszArm.NatMul
