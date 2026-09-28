import SszX86.MeasureUintWideMath
import SszX86.MeasureUintScan

namespace SszX86.Measure.Uint

macro "measure_uint_shift" : tactic => `(tactic|
  simp (config := {instances := true})
    [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      Width.bits, BitVec.take, Effects.All])

def scaledShiftState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rdx := UInt64.ofBitVec (s.regs.rax.toBitVec >>> 58),
    rax := UInt64.ofBitVec (s.regs.rax.toBitVec <<< 6)}, status := flags}

def scaledState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rdx := UInt64.ofBitVec (scaledHigh s.regs.rax.toBitVec),
    rax := UInt64.ofBitVec (scaledLow s.regs.rax.toBitVec)}, status := flags}

/-- Both halves of the 128-bit multiplication by64 are literal shifts. -/
theorem scaled_shifts_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (scaledShiftState s flags, base + 866)) :
    Eventually (step e) P (s, base + 855) := by
  measure_step 94 using hc
  measure_step 95 using hc
  measure_uint_shift
  constructor <;> constructor <;> measure_step 96 using hc
  all_goals
    measure_uint_shift
    constructor <;> constructor <;> simpa [scaledShiftState] using next _

private def adcMinusOneState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rdx := UInt64.ofBitVec
        (18446744073709551615#64 + s.regs.rdx.toBitVec +
          BitVec.ofNat 64 s.status.cf.toNat)}
    status := flags}

private theorem adc_minus_one_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (adcMinusOneState s flags, base + 1736)) :
    Eventually (step e) P (s, base + 870) := by
  measure_step 98 using hc
  measure_step 99 using hc
  simpa [adcMinusOneState] using next _

private def addMinus57State (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (18446744073709551559#64 + s.regs.rax.toBitVec)}
    status := flags}

private theorem add_minus57_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags,
      flags.cf = decide (2 ^ 64 ≤ s.regs.rax.toBitVec.toNat + 18446744073709551559) →
      Eventually (step e) P (addMinus57State s flags, base + 870)) :
    Eventually (step e) P (s, base + 866) := by
  simp only [addMinus57State] at next
  measure_step 97 using hc
  apply next
  simp [StatusFlags.from_result, Udivti3.radix, Nat.add_comm]

/-- ADD −57/ADC −1 computes the exact predecessor limb contribution plus7. -/
theorem scaled_adjust_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (flags : StatusFlags) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (scaledState s flags, base + 1736)) :
    Eventually (step e) P (scaledShiftState s flags, base + 866) := by
  apply add_minus57_cps e base hc
  intro additionFlags carry
  simp only [scaledShiftState, UInt64.toBitVec_ofBitVec] at carry
  apply adc_minus_one_cps e base hc
  intro resultFlags
  simpa [adcMinusOneState, addMinus57State, scaledShiftState, scaledState,
    scaledLow, scaledHigh, carry, BitVec.add_comm] using next resultFlags

theorem scaled_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (scaledState s flags, base + 1736)) :
    Eventually (step e) P (s, base + 855) := by
  apply scaled_shifts_cps e base hc
  intro flags
  exact scaled_adjust_cps e base hc s flags P next

def incrementedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rdi := UInt64.ofBitVec ((s.regs.rdi.toBitVec.setWidth 32 + 1#32).setWidth 64)}
    status := flags}

def sumState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rdi := UInt64.ofBitVec (sumLow s.regs.rax.toBitVec
      ((s.regs.rdi.toBitVec.setWidth 32 + 1#32).setWidth 64)),
    rdx := UInt64.ofBitVec (sumHigh s.regs.rax.toBitVec s.regs.rdx.toBitVec
      ((s.regs.rdi.toBitVec.setWidth 32 + 1#32).setWidth 64))}, status := flags}

/-- The native INC32 converts the exact BSR index into a bit count. -/
theorem increment_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (incrementedState s flags, base + 1798)) :
    Eventually (step e) P (s, base + 1796) := by
  measure_step 251 using hc
  simpa [incrementedState] using next _

private def adcCarryState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rdx := UInt64.ofBitVec (s.regs.rdx.toBitVec + BitVec.ofNat 64 s.status.cf.toNat)}
    status := flags}

private theorem adc_carry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (adcCarryState s flags, base + 1805)) :
    Eventually (step e) P (s, base + 1801) := by
  measure_step 253 using hc
  simpa [adcCarryState] using next _

/-- The carry is consumed immediately by ADC before any shift can clobber it. -/
theorem sum_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (flags : StatusFlags) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (sumState s flags, base + 1805)) :
    Eventually (step e) P (incrementedState s flags, base + 1798) := by
  simp only [incrementedState]
  measure_step 252 using hc
  apply adc_carry_cps e base hc
  intro resultFlags
  simpa [adcCarryState, sumState, sumLow, sumHigh, StatusFlags.from_result,
    Udivti3.cf_add, Udivti3.radix] using next resultFlags

def quotientState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rdi := UInt64.ofBitVec (dividedLow s.regs.rdi.toBitVec s.regs.rdx.toBitVec),
    rdx := UInt64.ofBitVec (dividedHigh s.regs.rdx.toBitVec)}, status := flags}

/-- Literal SHRD/SHR plus the original jump to width metadata loading. -/
theorem quotient_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (quotientState s flags, base + 2686)) :
    Eventually (step e) P (s, base + 1805) := by
  measure_step 254 using hc
  measure_uint_shift
  constructor <;> constructor <;> measure_step 255 using hc
  all_goals
    measure_uint_shift
    constructor <;> constructor <;> measure_step 256 using hc
  all_goals
    simpa [quotientState, dividedLow, dividedHigh, BitVec.take,
      BitVec.setWidth_eq_extractLsb' (show 64 ≤ 128 by decide)] using next _

/-- Full rounded 128-bit requirement, before width inspection. -/
theorem round_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags₁ flags₂, Eventually (step e) P
      (quotientState (sumState s flags₁) flags₂, base + 2686)) :
    Eventually (step e) P (s, base + 1796) := by
  apply increment_cps e base hc
  intro incrementFlags
  apply sum_cps e base hc s incrementFlags
  intro additionFlags
  apply quotient_cps e base hc
  exact next additionFlags

end SszX86.Measure.Uint
