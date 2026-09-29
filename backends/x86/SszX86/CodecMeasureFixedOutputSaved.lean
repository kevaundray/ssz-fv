import SszX86.CodecMeasureFixedOutputReturn
import SszX86.CodecMeasureFixedPush
import SszX86.DispatchMemory

namespace SszX86.CodecMeasureFixed.Output
open BoolCodec UintCodec

def originalSaved (s : MachineData) (ra : BitVec 64) : Saved :=
  ⟨s.regs.rbx.toBitVec, s.regs.r12.toBitVec, s.regs.r13.toBitVec,
    s.regs.r14.toBitVec, s.regs.r15.toBitVec, s.regs.rbp.toBitVec, ra⟩

private theorem subtract_offset (sp a b : BitVec 64) : sp - a + b = sp - (a-b) := by
  bv_omega

/-- The actual PUSH image establishes all six saves without needing old stack values. -/
theorem original_saved_at (s : MachineData) (ra : BitVec 64)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    SavedAt (savedMem s) (s.regs.rsp.toBitVec - 136#64) (originalSaved s ra) := by
  have saved := Dispatch.saved_at s ra ret
  simpa only [SavedAt, originalSaved, BoolCodec.SavedAt, Dispatch.saved,
    subtract_offset, BitVec.reduceSub] using saved

/-- Local reservation does not touch the saved memory image. -/
theorem allocated_saved_at (s : MachineData) (ra : BitVec 64) (flags : StatusFlags)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    SavedAt (allocatedState (savedState s) flags).dmem
      (allocatedState (savedState s) flags).regs.rsp.toBitVec (originalSaved s ra) := by
  simpa only [allocatedState, savedState, Dispatch.savedState, UInt64.toBitVec_ofBitVec,
    UInt64.toBitVec_sub, UInt64.toBitVec_ofNat, BitVec.sub_sub, BitVec.reduceAdd]
    using original_saved_at s ra ret

/-- Byte frames transport all seven original loads; the protected span includes RET. -/
theorem SavedAt.frame (before after : DataMem) (sp : BitVec 64) (saved : Saved)
    (writes : Codec.Footprint) (frame : Codec.MemoryFrame before after writes)
    (protected : ∀ i < 56, ¬ writes (sp + 88#64 + BitVec.ofNat 64 i))
    (stored : SavedAt before sp saved) : SavedAt after sp saved := by
  have load (off : Nat) (low : 88 ≤ off) (high : off+8 ≤ 144) :
      Mem.loadInt after (sp + BitVec.ofNat 64 off) 8 =
        Mem.loadInt before (sp + BitVec.ofNat 64 off) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    apply frame
    have address : (sp + BitVec.ofNat 64 off) + BitVec.ofNat 64 i =
        sp + 88#64 + BitVec.ofNat 64 (off-88+i) := by
      rw [memmove_addr_add, memmove_addr_add]
      congr 1
      congr 1
      omega
    rw [address]
    exact protected (off-88+i) (by omega)
  simpa only [SavedAt, load 88 (by decide) (by decide),
    load 96 (by decide) (by decide), load 104 (by decide) (by decide),
    load 112 (by decide) (by decide), load 120 (by decide) (by decide),
    load 128 (by decide) (by decide), load 136 (by decide) (by decide)] using stored

/-- Restoring the saved image yields the original caller ABI, not a fresh ABI assumption. -/
theorem returned_abi (original body : MachineData) (ra : BitVec 64)
    (sp : body.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136#64)
    (simd : body.zmms = original.zmms)
    (stored : SavedAt body.dmem body.regs.rsp.toBitVec (originalSaved original ra)) :
    Delimited.Returned original ra (returned body (originalSaved original ra), Int64.ofBitVec ra) := by
  have ret := stored.2.2.2.2.2.2
  have address : body.regs.rsp.toBitVec + 136#64 = original.regs.rsp.toBitVec := by
    rw [sp]
    bv_omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, simd, ?_⟩
  · change body.regs.rsp.toBitVec + 144#64 = original.regs.rsp.toBitVec + 8
    rw [sp]
    bv_omega
  all_goals try rfl
  simpa only [returned, originalSaved, address] using ret

end SszX86.CodecMeasureFixed.Output
