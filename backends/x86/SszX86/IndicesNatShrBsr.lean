import SszX86.IndicesNatShrBsrSteps
import SszX86.IndicesNatShrMemory

set_option autoImplicit false

namespace SszX86.IndicesNatShr
open UintCodec

def bsrResult (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with dmem := bsrMem s,
    regs := {s.regs with r11 := UInt64.ofNat s.regs.r11.toNat.log2}, status := flags}

/-- Complete actual PC80→PC140 lowering, including its own two stores and
restoring R9/R10/RSP. Only the selected nonzero limb and physical stack mapping
are preconditions; loop termination is discharged from that limb. -/
theorem bsr_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (stackLow : 16 ≤ s.regs.rsp.toNat)
    (mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 16#64) 16)
    (nonzero : s.regs.r11.toBitVec ≠ 0)
    (post : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) post (bsrResult s flags, base + 140)) :
    Eventually (step e) post (s, base + 80) := by
  apply bsr_push_cps e base code s mapped
  apply bsr_start_cps e base code (bsrPushed s) nonzero
  intro initialFlags
  have finish : ∀ flags, Eventually (step e) post
      (bsrState (bsrPushed s) (BitVec.ofNat 64 s.regs.r11.toNat.log2) 0 flags,
        base + 117) := by
    intro loopFlags
    apply bsr_publish_cps e base code
    intro publishFlags
    apply bsr_restore_cps e base code _ s.regs.r9.toBitVec s.regs.r10.toBitVec
    · exact (bsr_saved_reads s stackLow).1
    · exact (bsr_saved_reads s stackLow).2
    · simpa [bsrRestored, bsrPublished, bsrState, bsrPushed, bsrResult,
        BitVec.sub_add_cancel, UInt64.ofBitVec_toBitVec] using next publishFlags
  simpa [bsrPushed] using
    bsr_loop_cps e base code (bsrPushed s) s.regs.r11.toBitVec nonzero post finish
      s.regs.r11.toNat.log2 0 (by simp only [Nat.zero_add, UInt64.toNat_toBitVec]) initialFlags

/-- Even undefined flags do not enlarge the byte frame of the lowering. -/
theorem bsr_memory_frame (s : MachineData) :
    Codec.MemoryFrame s.dmem (bsrMem s)
      (fun a => Codec.InSpan a (s.regs.rsp.toBitVec - 16#64) 16) := by
  simpa only [bsrMem, Large.fillMem, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.add_zero, Nat.mul_zero, BitVec.add_zero,
    Nat.reduceAdd, Nat.reduceMul] using
    fill_frame s.dmem (s.regs.rsp.toBitVec - 16#64)
      [s.regs.r10.toBitVec, s.regs.r9.toBitVec]

end SszX86.IndicesNatShr
