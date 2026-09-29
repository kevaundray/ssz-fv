import SszX86.IndicesNatShrSteps
import SszSerializeMeasure

set_option autoImplicit false

namespace SszX86.IndicesNatShr
open SszNative.Serialize

/-- Only the two actual lowering registers are changed by the scan loop. -/
def bsrState (s : MachineData) (counter bits : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r9 := UInt64.ofBitVec counter,
    r10 := UInt64.ofBitVec bits}, status := flags}

/-- Literal original INC R9 / SHR R10 / JNE at PCs109,112,115. -/
theorem bsr_iteration_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (counter bits : BitVec 64) (flags : StatusFlags)
    (post : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) post
      (bsrState s (counter + 1) (bits >>> 1) flags,
        if bits >>> 1 = 0#64 then base + 117 else base + 109)) :
    Eventually (step e) post (bsrState s counter bits flags, base + 109) := by
  have target := code.targets ("indices_nat_shr_u109", 109) (by decide)
  simp only [bsrState]
  indices_shr_step 28 using code
  indices_shr_step 29 using code
  simp (config := {instances := true})
    [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      BitVec.take, Effects.All]
  constructor <;> indices_shr_step 30 using code
  all_goals
    by_cases zero : bits >>> 1 = 0#64
    · have registerZero : UInt64.ofBitVec bits >>> 1 = UInt64.ofBitVec (0#64) := by
        change UInt64.ofBitVec bits >>> UInt64.ofNat 1 = UInt64.ofBitVec (0#64)
        rw [← UInt64.ofBitVec_shiftRight bits 1 (by decide), zero]
      simpa [registerZero, zero, bsrState, StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, target, bsrState, StatusFlags.from_result, Effects.All] using next _

/-- The finite original loop terminates at exactly the limb's highest set bit;
its measure is source-derived, not supplied fuel or an assumed execution. -/
theorem bsr_loop_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (nonzero : limb ≠ 0)
    (post : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) post
      (bsrState s (BitVec.ofNat 64 limb.toNat.log2) 0 flags, base + 117)) :
    ∀ remaining position, position + remaining = limb.toNat.log2 → ∀ flags,
      Eventually (step e) post
        (bsrState s (BitVec.ofNat 64 position - 1) (limb >>> position) flags,
          base + 109) := by
  have certificate := bsr_certificate limb nonzero
  intro remaining
  induction remaining with
  | zero =>
      intro position same flags
      have equal : position = limb.toNat.log2 := by omega
      subst position
      apply bsr_iteration_cps e base code
      intro finalFlags
      rw [← BitVec.shiftRight_add, certificate.1]
      simpa only [BitVec.sub_add_cancel, BitVec.ofNat_eq_ofNat, ↓reduceIte] using next finalFlags
  | succ remaining ih =>
      intro position same flags
      apply bsr_iteration_cps e base code
      intro loopFlags
      rw [← BitVec.shiftRight_add]
      have nonempty : limb >>> (position + 1) ≠ 0#64 :=
        certificate.2 (position + 1) (by omega)
      rw [ite_eq_right nonempty]
      have counter : BitVec.ofNat 64 position - 1 + 1 =
          BitVec.ofNat 64 (position + 1) - 1 := by
        simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat,
          BitVec.sub_add_cancel, BitVec.add_sub_cancel]
      rw [counter]
      exact ih (position + 1) (by omega) loopFlags

end SszX86.IndicesNatShr
