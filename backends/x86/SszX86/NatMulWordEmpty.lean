import SszX86.NatMulWordSmallComplete
import SszX86.WordNormalize

namespace SszX86.NatMulWord
open SszNative

private theorem unsigned_zero_high (factor : BitVec 64) :
    BitVec.ofInt 64 (((0#64).unsigned * factor.unsigned) >>> 64) = 0#64 := by
  change productHigh (0#64) factor = 0#64
  simp only [productHigh_eq, BitVec.toNat_zero, Nat.zero_mul, Nat.zero_div]

private theorem product_state_zero (s : MachineData) (zero : s.regs.r9.toBitVec = 0#64)
    (flags : StatusFlags) :
    productState s flags = {s with regs := {s.regs with rax := 0, rdx := 0}, status := flags} := by
  simp (config := {instances := true}) only [productState, productHigh, zero,
    BitVec.zero_mul, unsigned_zero_high, WordNormalize.numeral]

private theorem empty_product_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (zero : s.regs.r9.toBitVec = 0#64) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (productState s flags, base+407)) :
    Eventually (step e) P (s, base+516) := by
  have target := hc.targets ("natMulWord_u407", 407) (by decide)
  have widthDifferent : (Width.W64 == Width.W8) = false := by decide
  have zeroReg : s.regs.r9 = 0 := UInt64.toBitVec_inj.mp zero
  natmulword_step 4:8 using hc
  natmulword_step 4:9 using hc
  simp only [widthDifferent, Bool.false_eq_true, ↓reduceIte]
  constructor <;> constructor <;> constructor <;> constructor
  all_goals
    natmulword_step 4:10 using hc
    constructor <;> natmulword_step 4:11 using hc
    all_goals simpa [product_state_zero s zero, zero, zeroReg, unsigned_zero_high,
      StatusFlags.from_result, target, Effects.All] using next _

/-- A physically empty Large takes the distinct 516/519/522/525 sequence,
without inventing a readable word zero. -/
theorem empty_multiply_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (small : operand.wordCount ≤ 1)
    (frame : PureFrame s t) (low : t.regs.r9.toBitVec = SszNative.NatMul.lowWord operand)
    (factorReg : t.regs.rcx.toBitVec = factor) (zero : t.regs.r9.toBitVec = 0#64) :
    Eventually (step e) (Post s operand factor address capacity used ra) (t, base+516) := by
  have lowZero : SszNative.NatMul.lowWord operand = 0#64 := low.symm.trans zero
  have fits : (SszNative.NatMul.wordProduct operand factor).toNat < 2^64 := by
    simp [SszNative.NatMul.wordProduct, lowZero, LimbMul.wideProduct]
  apply empty_product_cps e base hc t zero
  intro flags
  have ready := product_ready s t operand factor frame low factorReg flags
  apply small_inline_publish_cps e base hc _ (ready.toPureFrame.output_mapped owned)
  apply small_memory_finish_cps e base hc s _ operand factor address capacity used ra owned nonzero notone small
  · simp only [smallResultMem, NatFromU128.resultMem, wideBase, fits, ↓reduceIte,
      ready.memory, ready.output, ready.low, successMem, NatFromU128.successMem]
  · exact ready.sp
  · exact ready.simd

end SszX86.NatMulWord
