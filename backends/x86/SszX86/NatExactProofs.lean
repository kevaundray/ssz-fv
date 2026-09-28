import SszX86.NatExactExec
import SszX86.NatExactMemory

namespace SszX86.NatExact
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Actual codec::exact entry through its real RET. It compares the full native
natural against usize; failure keeps the original pair and all borrowed limbs.
Success defines only output+64's four-byte status. RAX is status, not an sret pointer. -/
theorem exact_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (expected : NatOperand) (actual ra : BitVec 64)
    (owned : Owned s expected actual ra) :
    Eventually (step e) (Post s expected actual ra) (s, base + Int64.ofNat entry) := by
  rw [show Int64.ofNat entry = 0 by decide, Int64.add_zero]
  apply prepare_cps e base hc s expected actual owned.actual_register owned.expected_at
  · intro success t frame status
    have out : t.regs.rdi = s.regs.rdi :=
      UInt64.eq_of_toBitVec_eq (frame.registers .rdi (by decide) (by decide) (by decide) (by decide) (by decide))
    have rsp : t.regs.rsp = s.regs.rsp :=
      UInt64.eq_of_toBitVec_eq (frame.registers .rsp (by decide) (by decide) (by decide) (by decide) (by decide))
    have hm : OutputMapped t := by
      simpa only [OutputMapped, frame.memory, out] using owned.output_mapped
    have hret : Mem.loadInt (successMem t.dmem t.regs.rdi.toBitVec) s.regs.rsp.toBitVec 8 =
        some (Int.ofBytes (wordBytes ra)) := by
      simpa only [resultMem, success, ↓reduceIte, frame.memory, out] using
        result_return_load s expected actual ra owned
    apply publish_success_cps e base hc t hm status
    apply ret_cps e base hc _ ra _
    · simpa only [rsp] using hret
    · apply post_of_memory s expected actual ra owned
      · simp only [resultMem, success, ↓reduceIte, frame.memory, out]
      · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, frame.vectors, hret⟩
        · simp only [rsp]
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .rbx (by decide) (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .rbp (by decide) (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r12 (by decide) (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r13 (by decide) (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r14 (by decide) (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r15 (by decide) (by decide) (by decide) (by decide) (by decide))
      · simpa only [success, ↓reduceIte] using status
  · intro failure t frame
    have out : t.regs.rdi = s.regs.rdi :=
      UInt64.eq_of_toBitVec_eq (frame.registers .rdi (by decide) (by decide) (by decide) (by decide) (by decide))
    have metadata : t.regs.rsi = s.regs.rsi :=
      UInt64.eq_of_toBitVec_eq (frame.registers .rsi (by decide) (by decide) (by decide) (by decide) (by decide))
    have actualReg : t.regs.rdx.toBitVec = actual := by
      have equal : t.regs.rdx = s.regs.rdx :=
        UInt64.eq_of_toBitVec_eq (frame.registers .rdx (by decide) (by decide) (by decide) (by decide) (by decide))
      exact (congrArg UInt64.toBitVec equal).trans owned.actual_register
    have rsp : t.regs.rsp = s.regs.rsp :=
      UInt64.eq_of_toBitVec_eq (frame.registers .rsp (by decide) (by decide) (by decide) (by decide) (by decide))
    have hm : OutputMapped t := by
      simpa only [OutputMapped, frame.memory, out] using owned.output_mapped
    have pointerRead : Mem.loadInt (errorHeaderMem t.dmem t.regs.rdi.toBitVec)
        t.regs.rsi.toBitVec 8 = some (expected.pointer.toNat : Int) := by
      simpa only [frame.memory, out, metadata] using (header_reads s expected actual ra owned).1
    have payloadRead : Mem.loadInt (errorHeaderMem t.dmem t.regs.rdi.toBitVec)
        (t.regs.rsi.toBitVec+8) 8 = some (expected.payload.toNat : Int) := by
      simpa only [frame.memory, out, metadata] using (header_reads s expected actual ra owned).2
    have hret : Mem.loadInt
        (failureMem t.dmem t.regs.rdi.toBitVec expected.pointer expected.payload actual)
        s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)) := by
      simpa only [resultMem, failure, Bool.false_eq_true, ↓reduceIte, frame.memory, out] using
        result_return_load s expected actual ra owned
    apply publish_failure_cps e base hc t expected.pointer expected.payload actual hm actualReg
      pointerRead payloadRead
    apply ret_cps e base hc _ ra _
    · simpa only [failureState, rsp] using hret
    · apply post_of_memory s expected actual ra owned
      · simp only [failureState, resultMem, failure, Bool.false_eq_true, ↓reduceIte, frame.memory, out]
      · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, frame.vectors, hret⟩
        · simp only [failureState, rsp]
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .rbx (by decide) (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .rbp (by decide) (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r12 (by decide) (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r13 (by decide) (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r14 (by decide) (by decide) (by decide) (by decide) (by decide))
        · exact UInt64.eq_of_toBitVec_eq (frame.registers .r15 (by decide) (by decide) (by decide) (by decide) (by decide))
      · simp only [failureState, failure, Bool.false_eq_true, ↓reduceIte]
        decide

theorem exact_refines (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (expected : NatOperand) (actual ra : BitVec 64)
    (owned : Owned s expected actual ra) :
    Eventually (step e)
      (fun t => NatNarrow.ExactResultAt (UintCodec.widthLoad t.1.dmem) s.regs.rdi.toNat expected actual)
      (s, base + Int64.ofNat entry) := by
  apply eventually_weaken (step e) (Post s expected actual ra)
  · intro t post
    exact post.observed
  · exact exact_correct e base hc s expected actual ra owned

end SszX86.NatExact
