import SszX86.NatToU128Exec
import SszX86.NatToU128Memory

namespace SszX86.NatToU128
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Complete linked leaf execution, including the actual RET and exact Option
layout. The original operand may be Small or any physically safe Large value,
including empty storage and redundant high zero limbs. -/
theorem to_u128_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (ra : BitVec 64)
    (owned : Owned s operand ra) :
    Eventually (step e) (Post s operand ra) (s, base + Int64.ofNat entry) := by
  rw [show Int64.ofNat entry = 0 by decide, Int64.add_zero]
  apply prepare_cps e base hc s operand owned.operand_pointer owned.operand_payload owned.operand_at
  · intro absent t frame tag upper
    have out : t.regs.rdi = s.regs.rdi :=
      UInt64.eq_of_toBitVec_eq (frame.registers .rdi (by decide) (by decide) (by decide) (by decide))
    have rsp : t.regs.rsp = s.regs.rsp :=
      UInt64.eq_of_toBitVec_eq (frame.registers .rsp (by decide) (by decide) (by decide) (by decide))
    have hm : OutputMapped t := by
      simpa only [OutputMapped, frame.memory, out] using owned.output_mapped
    have hret : Mem.loadInt (noneMem t.dmem t.regs.rdi.toBitVec) s.regs.rsp.toBitVec 8 =
        some (Int.ofBytes (wordBytes ra)) := by
      simpa only [resultMem, frame.memory, out] using result_return_load s operand ra owned none
    apply publish_none_cps e base hc t hm tag upper
    apply (ret_cps e base hc _ ra _ ?_ ?_).1
    · simpa only [rsp] using hret
    · apply post_of_memory s operand ra owned
      · simp only [absent, resultMem, frame.memory, out]
      · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, frame.vectors, hret⟩
        · simp only [rsp]
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .rbx (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .rbp (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r12 (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r13 (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r14 (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r15 (by decide) (by decide) (by decide) (by decide))
      · simpa only [absent, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using tag
  · intro value present t frame high low
    have out : t.regs.rdi = s.regs.rdi :=
      UInt64.eq_of_toBitVec_eq (frame.registers .rdi (by decide) (by decide) (by decide) (by decide))
    have rsp : t.regs.rsp = s.regs.rsp :=
      UInt64.eq_of_toBitVec_eq (frame.registers .rsp (by decide) (by decide) (by decide) (by decide))
    have hm : OutputMapped t := by
      simpa only [OutputMapped, frame.memory, out] using owned.output_mapped
    have hret : Mem.loadInt (someMem t.dmem t.regs.rdi.toBitVec value) s.regs.rsp.toBitVec 8 =
        some (Int.ofBytes (wordBytes ra)) := by
      simpa only [resultMem, frame.memory, out] using result_return_load s operand ra owned (some value)
    apply publish_some_cps e base hc t value hm high low
    intro flags
    apply (ret_cps e base hc _ ra _ ?_ ?_).2
    · simpa only [someState, rsp] using hret
    · apply post_of_memory s operand ra owned
      · simp only [someState, present, resultMem, frame.memory, out]
      · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, frame.vectors, hret⟩
        · simp only [someState, rsp]
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .rbx (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .rbp (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r12 (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r13 (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r14 (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r15 (by decide) (by decide) (by decide) (by decide))
      · simp only [someState, present, Option.isSome_some, ↓reduceIte]
        decide

theorem to_u128_refines (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (ra : BitVec 64)
    (owned : Owned s operand ra) :
    Eventually (step e)
      (fun t => NatNarrow.U128ResultAt (UintCodec.widthLoad t.1.dmem) s.regs.rdi.toNat
        (NatNarrow.toU128 operand)) (s, base + Int64.ofNat entry) := by
  apply eventually_weaken (step e) (Post s operand ra)
  · intro t post
    exact post.observed
  · exact to_u128_correct e base hc s operand ra owned

end SszX86.NatToU128
