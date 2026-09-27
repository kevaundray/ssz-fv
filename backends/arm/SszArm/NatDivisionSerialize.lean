import SszArm.NatDivisionOutput
import SszArm.NatDivisionFinish

namespace SszArm.NatDivision

open UintCodec (widthLoad)
open Delimited (MemoryFrame Protected)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem fast_output_ready (s : ArmState) (base : BitVec 64) (space : ReturnSpace s)
    (operand : SszNative.NatOperand) (remainder : BitVec 64)
    (pointer : r (.GPR 9#5) s = operand.pointer)
    (payload : r (.GPR 10#5) s = operand.payload)
    (rem : r (.GPR 22#5) s - r (.GPR 0#5) s * r (.GPR 20#5) s = remainder)
    (input : operand.At (widthLoad s)) (owned : OperandOwned (returnWrites s) operand) :
    ReturnReady (block base fastOutputOps s) (.ok (operand, remainder)) := by
  have args := fast_output_arguments s base space
  have head := fast_output_head s base space
  have frame := fast_output_frame s base space
  have writes : returnWrites (block base fastOutputOps s) = returnWrites s := by
    simp only [returnWrites, args.2.2.2.2.1, args.2.2.2.2.2]
  refine ⟨args.2.2.2.1, args.2.1.trans rem, ?_, ?_, ?_,
    operand_at_preserved frame operand input owned, ?_⟩
  · rw [args.2.2.1]
    rfl
  · rw [args.2.2.2.2.1]
    exact head.1.trans pointer
  · rw [args.2.2.2.2.1]
    exact head.2.trans payload
  · rw [writes]
    exact owned

theorem payload_ready (s : ArmState) (base : BitVec 64) (space : ReturnSpace s)
    (operand : SszNative.NatOperand) (remainder : BitVec 64)
    (pointer : read_mem_bytes 8 (r (.GPR 19#5) s) s = operand.pointer)
    (payload : r (.GPR 10#5) s = operand.payload)
    (rem : r (.GPR 1#5) s = remainder) (status : (r (.GPR 8#5) s).setWidth 32 = 0#32)
    (input : operand.At (widthLoad s)) (owned : OperandOwned (returnWrites s) operand) :
    ReturnReady (block base payloadOps s) (.ok (operand, remainder)) := by
  have args := payload_arguments s base
  have head := payload_head s base space
  have frame := payload_frame s base space
  have writes : returnWrites (block base payloadOps s) = returnWrites s := by
    simp only [returnWrites, args.2.2.2.2.1, args.2.2.2.2.2]
  refine ⟨args.2.2.2.1, args.2.1.trans rem, ?_, ?_, ?_,
    operand_at_preserved frame operand input owned, ?_⟩
  · rw [args.2.2.1]
    exact status
  · rw [args.2.2.2.2.1]
    exact head.1.trans pointer
  · rw [args.2.2.2.2.1]
    exact head.2.trans payload
  · rw [writes]
    exact owned

/-- A serializer's output and temporary writes cannot overwrite the saved
activation; this is derived from its physical separation, not assumed saved data. -/
theorem Saved.output_preserved {original s t : ArmState}
    (saved : Saved original s) (stack : 80 ≤ (r (.GPR 31#5) original).toNat)
    (space : ReturnSpace s) (frame : MemoryFrame (returnWrites s) s t)
    (sp : r (.GPR 31#5) t = r (.GPR 31#5) s)
    (high : ∀ reg : BitVec 5, 25 ≤ reg.toNat → reg.toNat ≤ 29 →
      r (.GPR reg) t = r (.GPR reg) s)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64) :
    Saved original t := by
  apply saved.preserve stack frame
  · right
    intro span member
    simp only [returnWrites, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl
    · have apart := space.separate
      rw [saved.sp] at apart
      simp only [Prod.fst, Prod.snd]
      bv_omega
    · simp only [Prod.fst, Prod.snd]
      rw [saved.sp]
      right
      bv_omega
  · exact sp
  · exact high
  · exact vectors

theorem fast_output_saved (original s : ArmState) (base : BitVec 64)
    (saved : Saved original s) (stack : 80 ≤ (r (.GPR 31#5) original).toNat)
    (space : ReturnSpace s) : Saved original (block base fastOutputOps s) := by
  apply saved.output_preserved stack space (fast_output_frame s base space)
  · exact (fast_output_arguments s base space).2.2.2.2.2
  · intro reg low high
    have keep : reg ≠ 1#5 ∧ reg ≠ 8#5 ∧ reg ≠ 9#5 ∧ reg ≠ 10#5 ∧ reg ≠ 31#5 := by bv_omega
    simp [block, fastOutputOps, Op.effect, put, next, state_simp_rules,
      keep.1, keep.2.1, keep.2.2.1, keep.2.2.2.1, keep.2.2.2.2]
  · intro reg low high
    simp [block, fastOutputOps, Op.effect, put, next, state_simp_rules]

theorem payload_saved (original s : ArmState) (base : BitVec 64)
    (saved : Saved original s) (stack : 80 ≤ (r (.GPR 31#5) original).toNat)
    (space : ReturnSpace s) : Saved original (block base payloadOps s) := by
  apply saved.output_preserved stack space (payload_frame s base space)
  · exact (payload_arguments s base).2.2.2.2.2
  · intro reg low high
    have keep : reg ≠ 9#5 := by bv_omega
    simp [block, payloadOps, Op.effect, put, next, state_simp_rules, keep]
  · intro reg low high
    simp [block, payloadOps, Op.effect, put, next, state_simp_rules]

end SszArm.NatDivision
