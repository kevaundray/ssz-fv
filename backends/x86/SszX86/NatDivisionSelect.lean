import SszX86.NatDivisionTrim
import SszX86.NatDivisionCount

namespace SszX86.NatDivision
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The first dispatch observes the original pointer, retaining original
payload/limbs until the high-zero scan has selected the arithmetic path. -/
theorem entry_dispatch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rsi.toBitVec = 0 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 214))
    (large : s.regs.rsi.toBitVec ≠ 0 → ∀ flags, Eventually (step e) P
      (scanState s (s.regs.rdx.toBitVec + 1) s.regs.rcx.toBitVec flags, base + 48)) :
    Eventually (step e) P (s, base + 20) := by
  have target := hc.targets ("natDivision_u214", 214) (by decide)
  natdiv_step 10 using hc
  constructor <;> natdiv_step 11 using hc
  all_goals
    by_cases hz : s.regs.rsi.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using small hz _
    · simp [StatusFlags.from_result, hz, Effects.All]
      natdiv_step 12 using hc
      simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
      natdiv_step 13 using hc
      natdiv_step 14 using hc
      simpa [scanState] using large hz _

/-- A nonzero significant count of at most two selects the wide native path,
even if the physical borrowed representation contains many redundant zeros. -/
theorem count_dispatch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rcx.toBitVec.toNat < 3 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 226))
    (large : 3 ≤ s.regs.rcx.toBitVec.toNat → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 83)) :
    Eventually (step e) P (s, base + 73) := by
  have target := hc.targets ("natDivision_u226", 226) (by decide)
  natdiv_step 21 using hc
  natdiv_step 22 using hc
  by_cases hs : s.regs.rcx.toNat < 3
  · simpa [StatusFlags.from_result, Udivti3.cf_sub, hs, target, Effects.All] using small hs _
  · have largeCount : 3 ≤ s.regs.rcx.toBitVec.toNat := by
      change 3 ≤ s.regs.rcx.toNat
      omega
    simpa [StatusFlags.from_result, Udivti3.cf_sub, hs, Effects.All] using large largeCount _

/-- An all-zero scan distinguishes an empty borrowed representation from a
nonempty all-zero one before either of the actual memory loads. -/
theorem zero_dispatch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (empty : s.regs.rdx.toBitVec = 0 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 245))
    (nonempty : s.regs.rdx.toBitVec ≠ 0 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 226)) :
    Eventually (step e) P (s, base + 221) := by
  have target := hc.targets ("natDivision_u245", 245) (by decide)
  natdiv_step 54 using hc
  constructor <;> natdiv_step 55 using hc
  all_goals
    by_cases hz : s.regs.rdx.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using empty hz _
    · simpa [StatusFlags.from_result, hz, Effects.All] using nonempty hz _

def largeStart (s : MachineData) (flags : StatusFlags) : MachineData :=
  { s with
    dmem := Mem.storeInt s.dmem s.regs.rsp.toBitVec 8 s.regs.rbx.toBitVec.toInt
    regs := { s.regs with
      rbx := s.regs.r13, rax := UInt64.ofBitVec (s.regs.rdx.toBitVec + 1)
      rbp := UInt64.ofBitVec (-(s.regs.rdx.toBitVec * 8))
      r8 := UInt64.ofBitVec (-1), r15 := 0 }
    status := flags }

/-- The large path saves the explicit result pointer in the already-owned
scratch word before dedicating RBX to the divisor for every runtime call. -/
theorem large_start_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : ∃ old, Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (largeStart s flags, base + 128)) :
    Eventually (step e) P (s, base + 83) := by
  natdiv_step 23 using hc
  apply Delimited.store_cps
  · exact hm
  simp only [Effects.All]
  natdiv_step 24 using hc
  natdiv_step 25 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  natdiv_step 26 using hc
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natdiv_step 27 using hc
  natdiv_step 28 using hc
  natdiv_step 29 using hc
  constructor <;> natdiv_step 30 using hc
  all_goals natdiv_step 31 using hc
  all_goals simpa [largeStart] using hp _

end SszX86.NatDivision
