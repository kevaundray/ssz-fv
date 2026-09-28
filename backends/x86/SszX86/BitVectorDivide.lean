import SszX86.BitVectorEntryOwned
import SszX86.BitVectorCall
import SszX86.BitVectorMappingClosure

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem entry_call_mapped (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (owned : Owned s saved length data address capacity used) :
    CallSlot (entryState s length) := by
  have hm : Large.Mapped (entryMem s) (s.regs.rsp.toBitVec - 72#64) workSize := by
    unfold entryMem
    repeat' first | exact owned.work_mapped | apply Large.mapped_store
  have h := Large.mapped_load (entryMem s) (s.regs.rsp.toBitVec - 72#64) workSize 64 8 hm (by decide)
  simpa only [CallSlot, entryState, show s.regs.rsp.toBitVec - 72#64 + BitVec.ofNat 64 64 =
    s.regs.rsp.toBitVec - 8#64 by bv_omega] using h

/-- Actual postdispatch entry through division's real RET at157. The generic
instruction invariant retains every mapped byte needed by later helper calls. -/
theorem division_phase (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s : MachineData) (saved : Saved) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (owned : Owned s saved length data address capacity used) :
    Eventually (step e)
      (fun t => NatDivision.Post (divisionReady s length (base + 157).toBitVec) length 8
        address capacity used (base + 157).toBitVec t ∧ Mapping.Extends s.dmem t.1.dmem)
      (s, base + 115) := by
  apply entry_cps e base hc.body s saved length data address capacity used owned
  apply division_call_cps e base hc.body (entryState s length) _
    (entry_call_mapped s saved length data address capacity used owned)
  apply Mapping.eventually_extends e
    (NatDivision.Post (divisionReady s length (base + 157).toBitVec) length 8
      address capacity used (base + 157).toBitVec)
    _ _ s.dmem (initial_mapped s length (base + 157).toBitVec)
  simpa only [divisionReady, NatDivision.step, step,
      show Int64.ofNat NatDivision.entry = 0 by decide, Int64.add_zero] using
    NatDivision.divide_correct e (base + Int64.ofInt divisionOffset) hc.division hc.udiv
      (divisionReady s length (base + 157).toBitVec) length 8 address capacity used
      (base + 157).toBitVec
      (division_owned s saved length data address capacity used (base + 157).toBitVec owned)

end SszX86.BitVector
