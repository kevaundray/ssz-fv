import SszArm.MeasureBitsWidthLow
import SszArm.MeasureBitsWidthPrepare

namespace SszArm.Measure.Bits.Width

def carry (s : ArmState) : Bool :=
  decide (2^64 ≤ (quotientLow (r (.GPR 26#5) s) (r (.GPR 25#5) s)).toNat + 1)

@[irreducible] def result (s : ArmState) (base : BitVec 64) : ArmState :=
  finishResult (carry s) (prepareResult (lowResult s base) base) base

theorem executes (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1852#64) (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) :
    run (6 + (6 + (finishOps (carry s)).length)) s = result s base := by
  let q := lowResult s base
  have first := low_run s base code error aligned pc stackLow
  have qprogram : q.program = s.program := by simp [q, lowResult, NatCompare.saved, state_simp_rules]
  have qerror : read_err q = .None := by
    simpa [q, lowResult, NatCompare.saved, state_simp_rules] using error
  have qpc : read_pc q = base + 1876#64 := by simp [q, lowResult, state_simp_rules]
  have second := prepare_run q base (code.congr qprogram) qerror qpc
  let p := prepareResult q base
  have pprogram : p.program = s.program := by
    simp [p, prepareResult, state_simp_rules, qprogram]
  have perror : read_err p = .None := by
    simpa [p, prepareResult, state_simp_rules] using qerror
  have carryBit :
      (AddWithCarry (quotientLow (r (.GPR 26#5) s) (r (.GPR 25#5) s)) 1#64 0#1).2.c = 1#1 ↔
        2^64 ≤ (quotientLow (r (.GPR 26#5) s) (r (.GPR 25#5) s)).toNat + 1 := by
    simpa [Udivti3.radix] using Udivti3.adc_carry
      (quotientLow (r (.GPR 26#5) s) (r (.GPR 25#5) s)) 1#64 0#1
  have ppc : read_pc p = base + (if carry s then 1908#64 else 1900#64) := by
    simp [p, q, prepareResult, lowResult, NatCompare.saved, state_simp_rules, carryBit, carry]
    split <;> rfl
  have third := finish_run (carry s) p base (code.congr pprogram) perror ppc
  rw [run_plus, first, run_plus, second, third]
  simp only [result, p, q]

@[simp] theorem result_program (s : ArmState) (base : BitVec 64) :
    (result s base).program = s.program := by
  simp [result, finishResult, prepareResult, lowResult, NatCompare.saved, state_simp_rules]
@[simp] theorem result_error (s : ArmState) (base : BitVec 64) :
    read_err (result s base) = read_err s := by
  simp [result, finishResult, prepareResult, lowResult, NatCompare.saved, state_simp_rules]
@[simp] theorem result_pc (s : ArmState) (base : BitVec 64) :
    read_pc (result s base) = base + 1912#64 := by simp [result, finishResult, state_simp_rules]
@[simp] theorem result_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (result s base) = r (.SFP reg) s := by
  simp [result, finishResult, prepareResult, lowResult, NatCompare.saved, state_simp_rules]

theorem result_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (unchanged : reg ∉ [0#5, 2#5, 3#5, 4#5, 8#5, 9#5, 23#5]) :
    r (.GPR reg) (result s base) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at unchanged
  simp [result, finishResult, prepareResult, lowResult, NatCompare.saved,
    state_simp_rules, unchanged.1, unchanged.2.1, unchanged.2.2.1,
    unchanged.2.2.2.1, unchanged.2.2.2.2.1, unchanged.2.2.2.2.2.1,
    unchanged.2.2.2.2.2.2]

theorem result_arguments (s : ArmState) (base : BitVec 64) :
    r (.GPR 0#5) (result s base) = r (.GPR 31#5) s + 120#64 ∧
    r (.GPR 23#5) (result s base) = r (.GPR 31#5) s + 120#64 ∧
    r (.GPR 4#5) (result s base) = r (.GPR 20#5) s ∧
    r (.GPR 3#5) (result s base) ++ r (.GPR 2#5) (result s base) =
      encodedHigh (r (.GPR 26#5) s) (r (.GPR 25#5) s) ++
        encodedLow (r (.GPR 26#5) s) (r (.GPR 25#5) s) := by
  simp [result, finishResult, prepareResult, lowResult, NatCompare.saved,
    state_simp_rules, encodedLow, encodedHigh, carry]

theorem result_count (s : ArmState) (base : BitVec 64) (count : BitVec 128)
    (low : r (.GPR 26#5) s = count.setWidth 64)
    (high : r (.GPR 25#5) s = (count >>> (64 : Nat)).setWidth 64) :
    r (.GPR 3#5) (result s base) ++ r (.GPR 2#5) (result s base) =
      BitVec.ofNat 128 (count.toNat / 8 + 1) := by
  rw [(result_arguments s base).2.2.2, low, high]
  exact encoded_pair_eq count

theorem result_frame (s : ArmState) (base : BitVec 64)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) :
    Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s (result s base) := by
  intro address outside
  have apart := outside _ (List.mem_singleton.mpr rfl)
  simp only [result, finishResult, prepareResult, lowResult, state_simp_rules]
  apply (NatCompare.saved_frame s 9#5 stackLow).memory
  dsimp at apart
  omega

end SszArm.Measure.Bits.Width
