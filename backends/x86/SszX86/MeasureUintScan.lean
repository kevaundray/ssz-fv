import SszX86.MeasureOwned
import SszX86.NatDivisionCore

namespace SszX86.Measure
open SszNative SszNative.Serialize SszNative.Limbs UintCodec

namespace Uint

/-- The first countdown changes only the index, selected limb, and flags. -/
def numberScanState (s : MachineData) (index limb : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec index
      rcx := UInt64.ofBitVec limb}
    status := flags}

/-- The width countdown retains both original descriptor words in RCX/RAX. -/
def widthScanState (s : MachineData) (index previous : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rsi := UInt64.ofBitVec index
      r8 := UInt64.ofBitVec previous}
    status := flags}

macro "measure_uint_load " h:term : tactic => `(tactic|
  (have observed := $h
   try simp only [BitVec.ofNat_eq_ofNat] at observed
   simp only [MachineData.load, Width.bytes, Width.bits,
     BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt, Effects.All]
   rw [observed]
   simp only [Effects.All, Delimited.word_cast]))

/-- One actual high-zero scan iteration; no read is made when the count is zero. -/
theorem number_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (old limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n + 2 < 2 ^ 64)
    (stored : Mem.loadInt s.dmem
      (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8 * n)) 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (numberScanState s (BitVec.ofNat 64 (n + 1)) limb flags,
        if limb = 0#64 then base + 832 else base + 855)) :
    Eventually (step e) P
      (numberScanState s (BitVec.ofNat 64 (n + 2)) old flags, base + 832) := by
  have target := hc.targets ("measure_u832", 832) (by decide)
  have different : BitVec.ofNat 64 (n + 2) ≠ 1#64 := by bv_omega
  have decrementReg : UInt64.ofNat n + 2 - 1 = UInt64.ofNat n + 1 := by
    apply UInt64.toBitVec_inj.mp
    change BitVec.ofNat 64 n + 2#64 - 1#64 = BitVec.ofNat 64 n + 1#64
    bv_omega
  have address : s.regs.rdx.toBitVec + BitVec.ofNat 64 (n + 2) * 8#64 +
      18446744073709551600#64 = s.regs.rdx.toBitVec + BitVec.ofNat 64 (8 * n) := by
    bv_omega
  simp only [numberScanState]
  measure_step 88 using hc
  measure_step 89 using hc
  simp [StatusFlags.from_result, different, Effects.All]
  measure_step 90 using hc
  simp only [MachineData.load, Width.bytes, Effects.All]
  rw [address, stored]
  simp only [Effects.All, Width.bits, Delimited.word_cast]
  measure_step 91 using hc
  measure_step 92 using hc
  constructor <;> measure_step 93 using hc
  all_goals
    by_cases zero : limb = 0#64
    · simpa (config := {instances := true})
        [UInt64.instOfNat, decrementReg, zero, target, numberScanState, StatusFlags.from_result,
          Effects.All] using next _
    · simpa (config := {instances := true})
        [UInt64.instOfNat, decrementReg, zero, numberScanState, StatusFlags.from_result,
          Effects.All] using next _

/-- Physical-length induction implements the literal descending scan, including
arbitrarily long high-zero padding and Large []. -/
theorem number_scan_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length + 1 < 2 ^ 64)
    (stored : ∀ i : Fin words.length, Mem.loadInt s.dmem
      (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8 * i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ old flags,
    (significantCount words n = 0 → ∀ old flags, Eventually (step e) P
      (numberScanState s 1 old flags, base + 2011)) →
    (0 < significantCount words n → ∀ flags, Eventually (step e) P
      (numberScanState s (BitVec.ofNat 64 (significantCount words n))
        (words[significantCount words n - 1]?.getD 0) flags, base + 855)) →
    Eventually (step e) P
      (numberScanState s (BitVec.ofNat 64 (n + 1)) old flags, base + 832) := by
  intro n
  induction n with
  | zero =>
    intro within old flags empty nonempty
    have target := hc.targets ("measure_u2011", 2011) (by decide)
    simp only [numberScanState]
    measure_step 88 using hc
    measure_step 89 using hc
    simpa [StatusFlags.from_result, target, Effects.All, numberScanState] using
      empty (by simp [significantCount]) old _
  | succ n ih =>
    intro within old flags empty nonempty
    have readLimb : Mem.loadInt s.dmem
        (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8 * n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using
        stored ⟨n, by omega⟩
    apply number_scan_step e base hc s old _ flags n (by omega) readLimb P
    intro fl
    by_cases zero : words[n]?.getD 0#64 = 0
    · have branchZero : words[n]?.getD 0#64 = 0#64 := by
        simpa only [BitVec.ofNat_eq_ofNat] using zero
      rw [ite_eq_left branchZero]
      apply ih (by omega) _ fl
      · intro h old fl'
        exact empty (by simpa [significantCount, zero] using h) old fl'
      · intro h fl'
        simpa [significantCount, zero] using
          nonempty (by simpa [significantCount, zero] using h) fl'
    · have branchNonzero : words[n]?.getD 0#64 ≠ 0#64 := by
        simpa only [BitVec.ofNat_eq_ofNat] using zero
      rw [ite_eq_right branchNonzero]
      have counted : significantCount words (n + 1) = n + 1 := by
        simp only [significantCount, BitVec.ofNat_eq_ofNat, branchNonzero, ↓reduceIte]
      simpa only [counted, Nat.add_sub_cancel, BitVec.ofNat_eq_ofNat] using
        nonempty (by rw [counted]; omega) fl

/-- Isolate the memory comparison from the preceding index comparison. -/
private theorem width_scan_tail (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) (n : Nat)
    (stored : Mem.loadInt s.dmem
      (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8 * n)) 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (widthScanState s (BitVec.ofNat 64 (n + 1)) (BitVec.ofNat 64 (n + 1)) flags,
        if limb = 0#64 then base + 2704 else base + 2725)) :
    Eventually (step e) P
      (widthScanState s (BitVec.ofNat 64 (n + 2)) (BitVec.ofNat 64 (n + 1)) flags,
        base + 2714) := by
  have target := hc.targets ("measure_u2704", 2704) (by decide)
  have address : s.regs.rcx.toBitVec + BitVec.ofNat 64 (n + 2) * 8#64 +
      18446744073709551600#64 = s.regs.rcx.toBitVec + BitVec.ofNat 64 (8 * n) := by
    bv_omega
  simp only [widthScanState]
  measure_step 355 using hc
  simp only [MachineData.load, Width.bytes, Effects.All]
  rw [address, stored]
  simp only [Effects.All, Width.bits, Delimited.word_cast]
  measure_step 356 using hc
  measure_step 357 using hc
  by_cases zero : limb = 0#64
  · simpa [zero, target, widthScanState, StatusFlags.from_result,
      Effects.All] using next _
  · simpa [zero, widthScanState, StatusFlags.from_result,
      Effects.All] using next _

/-- The second scan uses the original width allocation and retains its exact pair. -/
theorem width_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (old limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n + 2 < 2 ^ 64)
    (stored : Mem.loadInt s.dmem
      (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8 * n)) 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (widthScanState s (BitVec.ofNat 64 (n + 1)) (BitVec.ofNat 64 (n + 1)) flags,
        if limb = 0#64 then base + 2704 else base + 2725)) :
    Eventually (step e) P
      (widthScanState s (BitVec.ofNat 64 (n + 2)) old flags, base + 2704) := by
  have different : BitVec.ofNat 64 (n + 2) ≠ 1#64 := by bv_omega
  have decrementReg : UInt64.ofNat n + 2 + 18446744073709551615 = UInt64.ofNat n + 1 := by
    apply UInt64.toBitVec_inj.mp
    change BitVec.ofNat 64 n + 2#64 + 18446744073709551615#64 = BitVec.ofNat 64 n + 1#64
    bv_omega
  simp only [widthScanState]
  measure_step 352 using hc
  measure_step 353 using hc
  simp [StatusFlags.from_result, different, Effects.All]
  measure_step 354 using hc
  simpa (config := {instances := true})
    [widthScanState, UInt64.instOfNat, decrementReg] using
      width_scan_tail e base hc s limb _ n stored P next

/-- Widths with three significant limbs remain valid widths; the scan does not
impose a host-sized cap or discard their original stored representation. -/
theorem width_scan_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length + 1 < 2 ^ 64)
    (stored : ∀ i : Fin words.length, Mem.loadInt s.dmem
      (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8 * i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ old flags,
    (significantCount words n = 0 → ∀ old flags, Eventually (step e) P
      (widthScanState s 1 old flags, base + 2746)) →
    (0 < significantCount words n → ∀ flags, Eventually (step e) P
      (widthScanState s (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 2725)) →
    Eventually (step e) P
      (widthScanState s (BitVec.ofNat 64 (n + 1)) old flags, base + 2704) := by
  intro n
  induction n with
  | zero =>
    intro within old flags empty nonempty
    have target := hc.targets ("measure_u2746", 2746) (by decide)
    simp only [widthScanState]
    measure_step 352 using hc
    measure_step 353 using hc
    simpa [StatusFlags.from_result, target, Effects.All, widthScanState] using
      empty (by simp [significantCount]) old _
  | succ n ih =>
    intro within old flags empty nonempty
    have readLimb : Mem.loadInt s.dmem
        (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8 * n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using
        stored ⟨n, by omega⟩
    apply width_scan_step e base hc s old _ flags n (by omega) readLimb P
    intro fl
    by_cases zero : words[n]?.getD 0#64 = 0
    · have branchZero : words[n]?.getD 0#64 = 0#64 := by
        simpa only [BitVec.ofNat_eq_ofNat] using zero
      rw [ite_eq_left branchZero]
      apply ih (by omega) _ fl
      · intro h old fl'
        exact empty (by simpa [significantCount, zero] using h) old fl'
      · intro h fl'
        simpa [significantCount, zero] using
          nonempty (by simpa [significantCount, zero] using h) fl'
    · have branchNonzero : words[n]?.getD 0#64 ≠ 0#64 := by
        simpa only [BitVec.ofNat_eq_ofNat] using zero
      rw [ite_eq_right branchNonzero]
      have counted : significantCount words (n + 1) = n + 1 := by
        simp only [significantCount, BitVec.ofNat_eq_ofNat, branchNonzero, ↓reduceIte]
      simpa only [counted] using nonempty (by rw [counted]; omega) fl

end Uint
end SszX86.Measure
