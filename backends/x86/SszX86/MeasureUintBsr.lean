import SszX86.MeasureUintBsrSteps
import SszSerializeMeasure

namespace SszX86.Measure.Uint
open UintCodec SszNative.Serialize

/-- Termination and exact highest-bit result of the original SHR64 loop. -/
theorem bsr_loop_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (nonzero : limb ≠ 0)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (bsrState s (BitVec.ofNat 64 limb.toNat.log2) 0 flags, base + 1773)) :
    ∀ remaining i, i + remaining = limb.toNat.log2 → ∀ flags,
    Eventually (step e) P
      (bsrState s (BitVec.ofNat 64 i - 1) (limb >>> i) flags, base + 1765) := by
  have cert := bsr_certificate limb nonzero
  intro remaining
  induction remaining with
  | zero =>
    intro i same flags
    have equal : i = limb.toNat.log2 := by omega
    subst i
    apply bsr_iteration_cps e base hc
    intro fl
    rw [← BitVec.shiftRight_add, cert.1]
    simpa only [BitVec.sub_add_cancel, BitVec.ofNat_eq_ofNat, ↓reduceIte] using next fl
  | succ remaining ih =>
    intro i same flags
    apply bsr_iteration_cps e base hc
    intro fl
    rw [← BitVec.shiftRight_add]
    have nonempty : limb >>> (i + 1) ≠ 0#64 := by
      simpa only [BitVec.ofNat_eq_ofNat] using cert.2 (i + 1) (by omega)
    rw [ite_eq_right nonempty]
    have counter : BitVec.ofNat 64 i - 1 + 1 = BitVec.ofNat 64 (i + 1) - 1 := by
      bv_omega
    rw [counter]
    exact ih (i + 1) (by omega) fl

def bsrResult (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    dmem := bsrMem s
    regs := {s.regs with rdi := UInt64.ofNat s.regs.rcx.toNat.log2}
    status := flags}

/-- The entire real lowering starts at1736, takes all saved-word reads from its
own stores, restores R10/R11/RSP, and leaves only its private sixteen-byte frame. -/
theorem bsr_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (memoryMapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 16#64) 16)
    (nonzero : s.regs.rcx.toBitVec ≠ 0)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (bsrResult s flags, base + 1796)) :
    Eventually (step e) P (s, base + 1736) := by
  apply bsr_push_cps e base hc s memoryMapped
  apply bsr_start_cps e base hc (bsrPushed s) nonzero
  intro initialFlags
  have finish : ∀ flags, Eventually (step e) P
      (bsrState (bsrPushed s) (BitVec.ofNat 64 s.regs.rcx.toNat.log2) 0 flags,
        base + 1773) := by
    intro loopFlags
    apply bsr_publish_cps e base hc
    intro publishFlags
    apply bsr_restore_cps e base hc _ s.regs.r10.toBitVec s.regs.r11.toBitVec
    · exact (bsr_saved_reads s).1
    · exact (bsr_saved_reads s).2
    · have result := next publishFlags
      simp [bsrRestored, bsrPublished, bsrState, bsrPushed, bsrResult,
        BitVec.sub_add_cancel, UInt64.ofBitVec_toBitVec] at result ⊢
      with_unfolding_all exact result
  simpa [bsrPushed] using bsr_loop_cps e base hc (bsrPushed s) s.regs.rcx.toBitVec nonzero P
    finish s.regs.rcx.toNat.log2 0 (by simp only [Nat.zero_add, UInt64.toNat_toBitVec]) initialFlags

end SszX86.Measure.Uint
