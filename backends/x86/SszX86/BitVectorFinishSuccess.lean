import SszX86.BitVectorFinishMemory
import SszX86.BitVectorConstructMath

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- The borrow path publishes the original pointer and executes the actual RET. -/
theorem finish_success_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s u : MachineData) (saved : Saved) (data : Ssz.Bytes) (count : BitVec 128)
    (original : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (stack : u.regs.rsp = s.regs.rsp)
    (out : u.regs.rdx.toBitVec = s.regs.rdi.toBitVec)
    (size : u.regs.r14.toNat = data.size)
    (lowWord : u.regs.rax.toBitVec = constructLow count)
    (highWord : u.regs.rcx.toBitVec = constructHigh count)
    (scope : data.size = (count.toNat + 7) / 8)
    (outputMapped : Large.Mapped u.dmem s.regs.rdi.toBitVec 80)
    (outputBound : s.regs.rdi.toNat + 80 ≤ 2^64)
    (stackLow : 72 ≤ s.regs.rsp.toNat) (stackHigh : s.regs.rsp.toNat + 368 ≤ 2^64)
    (outputWork : Body.Apart s.regs.rdi.toNat 80 (workStart s) workSize)
    (outputSaved : Body.Apart s.regs.rdi.toNat 80 (s.regs.rsp.toNat + 312) 56)
    (stored : SavedAt u.dmem s.regs.rsp.toBitVec saved)
    (source : SszNative.ByteView.BytesAt (widthLoad u.dmem) s.regs.rdx.toNat data)
    (sourceBound : s.regs.rdx.toNat + data.size ≤ 2^64)
    (sourceOutput : Body.Apart s.regs.rdx.toNat data.size s.regs.rdi.toNat 80)
    (cached : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 104#64) 8 =
      some (s.regs.rdx.toNat : Int)) :
    Eventually (step e) (Terminal s saved u.dmem data (.ok count)) (u, base + 5317) := by
  have sourceCache : Mem.loadInt
      (Mem.storeInt u.dmem (u.regs.rdx.toBitVec + 16#64) 1 3)
      (u.regs.rsp.toBitVec + 104#64) 8 = some (s.regs.rdx.toNat : Int) := by
    rw [stack, out]
    rw [load_store_disjoint]
    · exact cached
    · intro i hi j hj
      have lowBV : 72 ≤ s.regs.rsp.toBitVec.toNat := stackLow
      have highBV : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := stackHigh
      have outputBV : s.regs.rdi.toBitVec.toNat + 80 ≤ 2^64 := outputBound
      simp [Body.Apart, workStart, workSize] at outputWork
      change s.regs.rdi.toBitVec.toNat + 80 ≤ s.regs.rsp.toBitVec.toNat - 72 ∨
        s.regs.rsp.toBitVec.toNat - 72 + 296 ≤ s.regs.rdi.toBitVec.toNat at outputWork
      bv_omega
  have frame := finish_success_frame s u.dmem s.regs.rdx.toBitVec u.regs.r14.toBitVec
    u.regs.rax.toBitVec u.regs.rcx.toBitVec outputBound
  have savedAfter := finish_saved s saved u.dmem _ stackLow stackHigh outputSaved stored frame
  apply success_stores_cps e base hc u s.regs.rdx.toBitVec
    (by simpa only [out] using outputMapped) sourceCache
  apply epilogue_cps e base hc _ saved
  · simpa only [successReady, out, stack] using savedAfter
  refine ⟨?_, ?_, ?_⟩
  · change SszNative.BitVector.ResultAt
      (widthLoad (successMem u.dmem u.regs.rdx.toBitVec s.regs.rdx.toBitVec
        u.regs.r14.toBitVec u.regs.rax.toBitVec u.regs.rcx.toBitVec)) _ _ _ _
    rw [out]
    apply success_observed _ _ _ _ _ _ data count outputBound sourceBound sourceOutput source size
    · rw [lowWord]
      exact BitVec.toNat_setWidth _ _
    · rw [highWord]
      simp only [constructHigh, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow]
      have bound := count.isLt
      omega
    · exact scope
  · apply finish_returned s (successReady u s.regs.rdx.toBitVec) saved original stack
    simpa only [successReady, out] using savedAfter
  · simpa only [returned, successReady, out, finishRegions] using frame

end SszX86.BitVector
