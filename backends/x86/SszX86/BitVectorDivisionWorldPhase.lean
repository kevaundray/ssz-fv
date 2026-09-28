import SszX86.BitVectorDivide
import SszX86.BitVectorWorldDivide
import SszX86.BitVectorWorldStack

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem helper_fixed (s : MachineData) (ra : BitVec 64) (t : MachineState)
    (returned : Delimited.Returned (callState s ra) ra t) : Fixed s t.1 := by
  refine ⟨?_, returned.rbx, returned.r14, returned.r15, returned.r12, returned.simd⟩
  apply UInt64.eq_of_toBitVec_eq
  have stack := returned.sp
  change t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64 + 8#64 at stack
  simpa only [BitVec.sub_add_cancel] using stack

theorem division_ready_positions (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used ra : BitVec 64)
    (owned : Owned s saved length data address capacity used) :
    (divisionReady s length ra).regs.rdi.toNat = s.regs.rsp.toNat + 16 ∧
    (divisionReady s length ra).regs.rsp.toNat = s.regs.rsp.toNat - 8 := by
  have low : 72 ≤ s.regs.rsp.toBitVec.toNat := owned.stack_low
  have high : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := owned.stack_bound
  have output : (divisionReady s length ra).regs.rdi.toBitVec = s.regs.rsp.toBitVec + 16#64 := by
    simp only [divisionReady, callState, NatDivision.callState, entryState, UInt64.toBitVec_ofBitVec]
  have stack : (divisionReady s length ra).regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64 := by
    simp only [divisionReady, callState, NatDivision.callState, entryState, UInt64.toBitVec_ofBitVec]
    rw [show (8 : BitVec 64) = 8#64 by decide]
  constructor
  · change (divisionReady s length ra).regs.rdi.toBitVec.toNat = s.regs.rsp.toBitVec.toNat + 16
    rw [output]
    bv_omega
  · change (divisionReady s length ra).regs.rsp.toBitVec.toNat = s.regs.rsp.toBitVec.toNat - 8
    rw [stack]
    bv_omega

/-- Initial physical ownership suffices through the real linked divider and RET;
the continuation receives actual helper observations and a fully owned reached
world carrying precisely the divider's executed limb-write spans. -/
theorem division_world_phase (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s : MachineData) (saved : Saved) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (owned : Owned s saved length data address capacity used) :
    Eventually (step e)
      (fun t => NatDivision.Post (divisionReady s length (base + 157).toBitVec) length 8
          address capacity used (base + 157).toBitVec t ∧
        World s saved length data address capacity used
          (outcomeCursor (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat))
          (SszNative.BitVector.allocationWrites
            (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat)) t.1.dmem ∧
        Fixed (entryState s length) t.1)
      (s, base + 115) := by
  apply entry_cps e base hc.body s saved length data address capacity used owned
  apply division_call_cps e base hc.body (entryState s length) _
    (entry_call_mapped s saved length data address capacity used owned)
  apply eventually_trans (step e)
    (fun t => NatDivision.Post (divisionReady s length (base + 157).toBitVec) length 8
      address capacity used (base + 157).toBitVec t ∧
      Mapping.Extends (divisionReady s length (base + 157).toBitVec).dmem t.1.dmem) _ _
  · apply Mapping.eventually_extends e
      (NatDivision.Post (divisionReady s length (base + 157).toBitVec) length 8
        address capacity used (base + 157).toBitVec)
      _ _ (divisionReady s length (base + 157).toBitVec).dmem (Mapping.Extends.refl _)
    simpa only [divisionReady, NatDivision.step, step,
      show Int64.ofNat NatDivision.entry = 0 by decide, Int64.add_zero] using
      NatDivision.divide_correct e (base + Int64.ofInt divisionOffset) hc.division hc.udiv
        (divisionReady s length (base + 157).toBitVec) length 8 address capacity used
        (base + 157).toBitVec
        (division_owned s saved length data address capacity used (base + 157).toBitVec owned)
  · intro t post
    apply Eventually.done
    refine ⟨post.1, ?_, helper_fixed (entryState s length) (base + 157).toBitVec t post.1.returned⟩
    have initial := entry_world s saved length data address capacity used (base + 157).toBitVec owned
    have positions := division_ready_positions s saved length data address capacity used (base + 157).toBitVec owned
    exact initial.division
      (division_owned s saved length data address capacity used (base + 157).toBitVec owned)
      positions.1 positions.2 rfl post.1 post.2

end SszX86.BitVector
