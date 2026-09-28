import SszX86.MeasureBitsEntry
import SszX86.MeasureUintWideMath

namespace SszX86.Measure.Bits
open SszNative UintCodec

macro "measure_bits_shift" : tactic => `(tactic|
  simp (config := {instances := true})
    [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      Width.bits, BitVec.take, Effects.All])

def encodedWide (wide : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (wide.toNat / 8 + 1)

theorem count_pair (wide : BitVec 128) :
    Uint.pairValue (wide.setWidth 64) ((wide >>> 64).setWidth 64) = wide.toNat := by
  simpa only [Uint.pairValue, Limbs.value, Nat.mul_zero, Nat.add_zero] using
    NatArithmetic.wide_words_value wide

private theorem pair_halves (lo hi : BitVec 64) (n : Nat) (bound : n < 2^128)
    (equal : Uint.pairValue lo hi = n) :
    lo = (BitVec.ofNat 128 n).setWidth 64 ∧
    hi = ((BitVec.ofNat 128 n) >>> 64).setWidth 64 := by
  have loBound := lo.isLt
  have hiBound := hi.isLt
  unfold Uint.pairValue at equal
  constructor <;> apply BitVec.eq_of_toNat_eq
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    omega
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    omega

/-- The native two-word shift and carry produce the entire encoded width,
including the boundary where it is exactly2^64. -/
theorem encoded_words (wide : BitVec 128) :
    Uint.sumLow (Uint.dividedLow (wide.setWidth 64) ((wide >>> 64).setWidth 64)) 1 =
      (encodedWide wide).setWidth 64 ∧
    Uint.sumHigh (Uint.dividedLow (wide.setWidth 64) ((wide >>> 64).setWidth 64))
      (Uint.dividedHigh ((wide >>> 64).setWidth 64)) 1 =
      ((encodedWide wide) >>> 64).setWidth 64 := by
  have physical := wide.isLt
  have quotient := Uint.divided_value (wide.setWidth 64) ((wide >>> 64).setWidth 64)
  rw [count_pair] at quotient
  have sum := Uint.sum_value
    (Uint.dividedLow (wide.setWidth 64) ((wide >>> 64).setWidth 64))
    (Uint.dividedHigh ((wide >>> 64).setWidth 64)) 1
    (by rw [quotient]; change wide.toNat / 8 + 1 < 2^128; omega)
  have exactSum : Uint.pairValue
      (Uint.sumLow (Uint.dividedLow (wide.setWidth 64) ((wide >>> 64).setWidth 64)) 1)
      (Uint.sumHigh (Uint.dividedLow (wide.setWidth 64) ((wide >>> 64).setWidth 64))
        (Uint.dividedHigh ((wide >>> 64).setWidth 64)) 1) = wide.toNat / 8 + 1 := by
    simpa only [quotient, show (1 : BitVec 64).toNat = 1 by decide] using sum
  exact pair_halves _ _ _ (by omega) exactSum

def progressiveDivided (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    r15 := UInt64.ofBitVec (Uint.dividedLow s.regs.r15.toBitVec s.regs.r14.toBitVec)
    r14 := UInt64.ofBitVec (Uint.dividedHigh s.regs.r14.toBitVec)}, status := flags}

theorem progressive_divide_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (progressiveDivided s flags, base + 1630)) :
    Eventually (step e) P (s, base + 1621) := by
  measure_step 209 using hc
  measure_bits_shift
  constructor <;> constructor <;> measure_step 210 using hc
  all_goals
    measure_bits_shift
    constructor <;> constructor <;>
      simpa [progressiveDivided, Uint.dividedLow, Uint.dividedHigh, BitVec.take,
        BitVec.setWidth_eq_extractLsb' (show 64 ≤ 128 by decide)] using next _

private def incrementCarryState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r14 := UInt64.ofBitVec (s.regs.r14.toBitVec + BitVec.ofNat 64 s.status.cf.toNat)}
    status := flags}

private theorem progressive_adc_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (incrementCarryState s flags, base + 1638)) :
    Eventually (step e) P (s, base + 1634) := by
  measure_step 212 using hc
  simpa [incrementCarryState] using next _

private theorem list_adc_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (incrementCarryState s flags, base + 2101)) :
    Eventually (step e) P (s, base + 2097) := by
  measure_step 292 using hc
  simpa [incrementCarryState] using next _

def progressiveIncremented (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    r15 := UInt64.ofBitVec (Uint.sumLow s.regs.r15.toBitVec 1)
    r14 := UInt64.ofBitVec (Uint.sumHigh s.regs.r15.toBitVec s.regs.r14.toBitVec 1)}, status := flags}

theorem progressive_increment_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (progressiveIncremented s flags, base + 1638)) :
    Eventually (step e) P (s, base + 1630) := by
  have carry : (18446744073709551616 ≤ 1 + s.regs.r15.toNat) ↔
      18446744073709551615 ≤ s.regs.r15.toNat := by omega
  measure_step 211 using hc
  apply progressive_adc_cps e base hc
  intro resultFlags
  simpa [incrementCarryState, progressiveIncremented, Uint.sumLow, Uint.sumHigh,
    StatusFlags.from_result, Udivti3.cf_add, Udivti3.radix, BitVec.add_comm,
    UInt64.add_comm, carry] using next resultFlags

theorem progressive_constructor_prepare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with
        rdi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 24#64)
        rsi := s.regs.r15, rdx := s.regs.r14}}, base + 2114)) :
    Eventually (step e) P (s, base + 1638) := by
  measure_step 213 using hc
  measure_step 214 using hc
  measure_step 215 using hc
  measure_step 216 using hc
  simpa [BitVec.add_comm] using next

def listDivided (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rsi := UInt64.ofBitVec (Uint.dividedLow s.regs.rsi.toBitVec s.regs.r14.toBitVec)
    r14 := UInt64.ofBitVec (Uint.dividedHigh s.regs.r14.toBitVec)}, status := flags}

theorem list_divide_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (listDivided s flags, base + 2093)) :
    Eventually (step e) P (s, base + 2084) := by
  measure_step 289 using hc
  measure_bits_shift
  constructor <;> constructor <;> measure_step 290 using hc
  all_goals
    measure_bits_shift
    constructor <;> constructor <;>
      simpa [listDivided, Uint.dividedLow, Uint.dividedHigh, BitVec.take,
        BitVec.setWidth_eq_extractLsb' (show 64 ≤ 128 by decide)] using next _

def listIncremented (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rsi := UInt64.ofBitVec (Uint.sumLow s.regs.rsi.toBitVec 1)
    r14 := UInt64.ofBitVec (Uint.sumHigh s.regs.rsi.toBitVec s.regs.r14.toBitVec 1)}, status := flags}

theorem list_increment_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (listIncremented s flags, base + 2101)) :
    Eventually (step e) P (s, base + 2093) := by
  have carry : (18446744073709551616 ≤ 1 + s.regs.rsi.toNat) ↔
      18446744073709551615 ≤ s.regs.rsi.toNat := by omega
  measure_step 291 using hc
  apply list_adc_cps e base hc
  intro resultFlags
  simpa [incrementCarryState, listIncremented, Uint.sumLow, Uint.sumHigh,
    StatusFlags.from_result, Udivti3.cf_add, Udivti3.radix, BitVec.add_comm,
    UInt64.add_comm, carry] using next resultFlags

theorem list_count_reload_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (low : BitVec 64) (P : MachineState → Prop)
    (stored : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16#64) 8 = some (low.toNat : Int))
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rsi := UInt64.ofBitVec low}}, base + 2084)) :
    Eventually (step e) P (s, base + 2079) := by
  measure_step 288 using hc
  natfrom_load stored
  simpa using next

theorem list_constructor_prepare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (header : BitVec 64) (P : MachineState → Prop)
    (stored : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (header.toNat : Int))
    (next : Eventually (step e) P
      ({s with regs := {s.regs with
        rdi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 24#64)
        rdx := s.regs.r14, rcx := UInt64.ofBitVec header}}, base + 2114)) :
    Eventually (step e) P (s, base + 2101) := by
  measure_step 293 using hc
  measure_step 294 using hc
  measure_step 295 using hc
  natfrom_load stored
  simpa [BitVec.add_comm] using next

end SszX86.Measure.Bits
