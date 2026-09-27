import SszArm.NatDivisionActivation
import SszArm.NatDivisionReturn
import SszArm.NatCompareMemory

namespace SszArm.NatDivision

open Delimited (Span Protected MemoryFrame)
open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem local_member (s : ArmState) (operand : SszNative.NatOperand)
    (span : Span) (member : span ∈ localWrites s) :
    span ∈ writesFor s (outcome s operand) := by
  cases allocated : (outcome s operand).allocation <;>
    simp [writesFor, allocated, member]

theorem prologue_local_frame (s : ArmState) (base : BitVec 64)
    (stack : 80 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame (localWrites s) s (block base prologueOps s) := by
  intro a outside
  apply prologue_frame s base stack a
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  have hs := outside ((r (.GPR 31#5) s).toNat - 80, 80) (by simp [localWrites])
  simp only [Prod.fst, Prod.snd] at hs ⊢
  omega

theorem prologue_input (s : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) (owned : Owned s operand) :
    operand.At (widthLoad (block base prologueOps s)) := by
  apply operand_at_preserved (local_frame (outcome s operand)
    (prologue_local_frame s base owned.stackBound)) operand owned.operandAt owned.operandOwned

/-- Any body state with the actual activation SP inherits the original output
ownership. This is a physical consequence of Owned, not an execution premise. -/
theorem Owned.return_space {original s : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned original operand)
    (sp : r (.GPR 31#5) s = r (.GPR 31#5) original - 64#64)
    (out : r (.GPR 19#5) s = r (.GPR 0#5) original) : ReturnSpace s := by
  have lower := owned.stackBound
  have upper := (r (.GPR 31#5) original).isLt
  have output := owned.outputBound
  have apart := owned.outputStack
  have separate : (r (.GPR 0#5) original).toNat + 68 ≤
      (r (.GPR 31#5) original).toNat - 80 ∨
      (r (.GPR 31#5) original).toNat ≤ (r (.GPR 0#5) original).toNat := by
    rcases apart with empty | apart
    · omega
    · have h := apart ((r (.GPR 31#5) original).toNat - 80, 80) (by simp)
      simp only [Prod.fst, Prod.snd] at h
      omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sp]
    bv_omega
  · rw [sp]
    bv_omega
  · rw [out]
    exact output
  · rw [sp, out]
    bv_omega

/-- The exact original physical slice meets the scanning loop's requirements,
including redundant high zeros and empty Large operands. -/
theorem Owned.large_source {original s : ArmState} (pointer : BitVec 64)
    (words : List (BitVec 64))
    (owned : Owned original (.large pointer words))
    (sp : r (.GPR 31#5) s = r (.GPR 31#5) original - 64#64) :
    NatCompare.Source s pointer words := by
  have lower := owned.stackBound
  have physical := owned.operandAt.2.2.1
  refine ⟨by change 16 ≤ (r (.GPR 31#5) s).toNat; rw [sp]; bv_omega, physical, ?_⟩
  by_cases empty : words = []
  · exact Or.inl empty
  · right
    have positive : 0 < 8 * words.length := by
      cases words <;> simp_all
    have inputOwned : Protected (writesFor original (outcome original (.large pointer words)))
        pointer.toNat (8 * words.length) := owned.operandOwned
    rcases inputOwned with noBytes | separate
    · omega
    · have apart := separate ((r (.GPR 31#5) original).toNat - 80, 80)
        (local_member original (.large pointer words) _ (by simp [localWrites]))
      simp only [Prod.fst, Prod.snd] at apart
      change pointer.toNat + 8 * words.length ≤ (r (.GPR 31#5) s).toNat - 16 ∨
        (r (.GPR 31#5) s).toNat ≤ pointer.toNat
      rw [sp]
      bv_omega

theorem large_words (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64))
    (stored : (.large pointer words : SszNative.NatOperand).At (widthLoad s)) :
    NatCompare.Words s pointer words := by
  intro i
  apply BitVec.eq_of_toNat_eq
  have observed := Option.some.inj (stored.2.2.2 i)
  simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using observed

end SszArm.NatDivision
