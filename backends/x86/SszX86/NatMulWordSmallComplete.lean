import SszX86.NatMulWordSmallAllocated

namespace SszX86.NatMulWord
open SszNative UintCodec

theorem WideReady.flagged {s t : MachineData} {wide : BitVec 128}
    (ready : WideReady s t wide) (flags : StatusFlags) :
    WideReady s {t with status := flags} wide :=
  ⟨⟨ready.memory, ready.sp, ready.output, ready.arena, ready.simd⟩, ready.low, ready.high⟩

private theorem inline_return_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (small : operand.wordCount ≤ 1)
    (ready : WideReady s t (SszNative.NatMul.wordProduct operand factor))
    (fits : (SszNative.NatMul.wordProduct operand factor).toNat < 2^64) :
    Eventually (step e) (Post s operand factor address capacity used ra) (t, base + 407) := by
  apply small_inline_publish_cps e base hc t (ready.toPureFrame.output_mapped owned)
  apply small_memory_finish_cps e base hc s _ operand factor address capacity used ra owned nonzero notone small
  · simp only [smallResultMem, NatFromU128.resultMem, wideBase, fits, ↓reduceIte,
      ready.memory, ready.output, ready.low, successMem, NatFromU128.successMem]
  · exact ready.sp
  · exact ready.simd

theorem small_product_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (small : operand.wordCount ≤ 1)
    (ready : WideReady s t (SszNative.NatMul.wordProduct operand factor)) :
    Eventually (step e) (Post s operand factor address capacity used ra) (t, base + 402) := by
  apply product_select_cps e base hc t
  · intro zero flags
    have fits := (NatFromU128.wide_small_iff (SszNative.NatMul.wordProduct operand factor)).2
      (ready.high.symm.trans zero)
    exact inline_return_cps e base hc s _ operand factor address capacity used ra owned
      nonzero notone small (ready.flagged flags) fits
  · intro nonzeroHigh flags
    have large : ¬ (SszNative.NatMul.wordProduct operand factor).toNat < 2^64 := by
      intro fits
      exact nonzeroHigh (ready.high.trans ((NatFromU128.wide_small_iff _).1 fits))
    exact small_reservation_finish_cps e base hc s _ operand factor address capacity used ra owned
      nonzero notone small (ready.flagged flags) large

/-- Starting with the physically fetched low limb, the scalar path performs
MUL, handles every allocator outcome, writes the native result and really RETs. -/
theorem small_multiply_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (small : operand.wordCount ≤ 1)
    (frame : PureFrame s t) (low : t.regs.r9.toBitVec = SszNative.NatMul.lowWord operand)
    (factorReg : t.regs.rcx.toBitVec = factor) :
    Eventually (step e) (Post s operand factor address capacity used ra) (t, base + 396) := by
  apply product_cps e base hc t
  intro flags
  exact small_product_finish_cps e base hc s _ operand factor address capacity used ra owned
    nonzero notone small (product_ready s t operand factor frame low factorReg flags)

end SszX86.NatMulWord
