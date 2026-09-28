import SszX86.NatMulWordCore
import SszX86.Udivti3Math

namespace SszX86.NatMulWord

def firstFetchedState (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec limb, r8 := s.regs.rax}
    status := flags}

def secondFetchedState (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec limb}, status := flags}

/-- First half of the unroll: bounds use the original physical length R9,
not the normalized allocation count R15. Out-of-range words are zero-extended. -/
theorem first_fetch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (loaded : s.regs.rax.toNat < s.regs.r9.toNat →
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + s.regs.rax.toBitVec * 8#64) 8 =
        some (limb.toNat : Int))
    (absent : s.regs.r9.toNat ≤ s.regs.rax.toNat → limb = 0#64)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (firstFetchedState s limb flags, base + 482)) :
    Eventually (step e) P (s, base + 466) := by
  have target := hc.targets ("natMulWord_u480", 480) (by decide)
  natmulword_step 3:23 using hc
  natmulword_step 3:24 using hc
  natmulword_step 3:25 using hc
  by_cases inside : s.regs.rax.toNat < s.regs.r9.toNat
  · simp [StatusFlags.from_result, inside, Effects.All]
    natmulword_step 3:26 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    natmulword_load (loaded inside)
    natmulword_step 3:27 using hc
    simpa [firstFetchedState] using next _
  · simp [StatusFlags.from_result, inside, target, Effects.All]
    natmulword_step 3:28 using hc
    constructor <;> simpa [firstFetchedState, absent (by omega)] using next _

/-- The paired fetch uses R13=i+1 for the bounds check and the original
addressing expression RSI+8*R8+8 for its load. -/
theorem second_fetch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (loaded : s.regs.r13.toNat < s.regs.r9.toNat →
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + s.regs.r8.toBitVec * 8#64 + 8#64) 8 =
        some (limb.toNat : Int))
    (absent : s.regs.r9.toNat ≤ s.regs.r13.toNat → limb = 0#64)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (secondFetchedState s limb flags, base + 435)) :
    Eventually (step e) P (s, base + 504) := by
  have target := hc.targets ("natMulWord_u430", 430) (by decide)
  natmulword_step 4:3 using hc
  natmulword_step 4:4 using hc
  by_cases inside : s.regs.r13.toNat < s.regs.r9.toNat
  · simp [StatusFlags.from_result, inside, target, Effects.All]
    natmulword_step 3:14 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    natmulword_load (loaded inside)
    simpa [secondFetchedState] using next _
  · simp [StatusFlags.from_result, inside, Effects.All]
    natmulword_step 4:5 using hc
    constructor <;> natmulword_step 4:6 using hc
    all_goals simpa [secondFetchedState, absent (by omega)] using next _

/-- Compare the completed even index with the masked count. -/
theorem loop_advance_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (done : s.regs.r13.toBitVec = s.regs.r12.toBitVec → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 702))
    (more : s.regs.r13.toBitVec ≠ s.regs.r12.toBitVec → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 466)) :
    Eventually (step e) P (s, base + 457) := by
  have target := hc.targets ("natMulWord_u702", 702) (by decide)
  natmulword_step 3:21 using hc
  natmulword_step 3:22 using hc
  by_cases equal : s.regs.r13.toBitVec = s.regs.r12.toBitVec
  · simpa [StatusFlags.from_result, equal, target, Effects.All] using done equal _
  · simpa [StatusFlags.from_result, equal, Effects.All] using more equal _

end SszX86.NatMulWord
