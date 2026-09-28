import SszX86.NatMulWordBorrow
import SszX86.NatMulWordMath

namespace SszX86.NatMulWord

theorem entry_multiply_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (nonzero : s.regs.rcx.toBitVec ≠ 0#64)
    (notone : s.regs.rcx.toBitVec ≠ 1#64) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (entryState s flags, base + 99)) :
    Eventually (step e) P (s, base) := by
  have target := hc.targets ("natMulWord_u99", 99) (by decide)
  rw [← show base + Int64.ofNat 0 = base by simp]
  natmulword_step 0:0 using hc
  natmulword_step 0:1 using hc
  natmulword_step 0:2 using hc
  simp [StatusFlags.from_result, notone, Effects.All]
  natmulword_step 0:3 using hc
  constructor <;> natmulword_step 0:4 using hc
  all_goals simpa [StatusFlags.from_result, nonzero, target, entryState, Effects.All] using next _

def productState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (s.regs.r9.toBitVec * s.regs.rcx.toBitVec)
      rdx := UInt64.ofBitVec (productHigh s.regs.r9.toBitVec s.regs.rcx.toBitVec)}
    status := flags}

/-- MUL produces both words; all four architecturally undefined flags are
universally quantified rather than fixed by the proof. -/
theorem product_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (productState s flags, base + 402)) :
    Eventually (step e) P (s, base + 396) := by
  have widthDifferent : (Width.W64 == Width.W8) = false := by decide
  natmulword_step 3:6 using hc
  natmulword_step 3:7 using hc
  simp only [widthDifferent, Bool.false_eq_true, ↓reduceIte]
  constructor <;> constructor <;> constructor <;> constructor
  all_goals simpa [productState, productHigh] using next _

theorem product_select_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rdx.toBitVec = 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 407))
    (large : s.regs.rdx.toBitVec ≠ 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 527)) :
    Eventually (step e) P (s, base + 402) := by
  have target := hc.targets ("natMulWord_u527", 527) (by decide)
  natmulword_step 3:8 using hc
  constructor <;> natmulword_step 3:9 using hc
  all_goals
    by_cases zero : s.regs.rdx.toBitVec = 0#64
    · simpa [StatusFlags.from_result, zero, Effects.All] using small zero _
    · simpa [StatusFlags.from_result, zero, target, Effects.All] using large zero _

/-- The entry registers select the scalar path without touching the arena. -/
theorem select_operand_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rsi.toBitVec = 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 396))
    (large : s.regs.rsi.toBitVec ≠ 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 122)) :
    Eventually (step e) P (s, base + 113) := by
  have target := hc.targets ("natMulWord_u396", 396) (by decide)
  natmulword_step 1:2 using hc
  constructor <;> natmulword_step 1:3 using hc
  all_goals
    by_cases zero : s.regs.rsi.toBitVec = 0#64
    · simpa [StatusFlags.from_result, zero, target, Effects.All] using small zero _
    · simpa [StatusFlags.from_result, zero, Effects.All] using large zero _

end SszX86.NatMulWord
