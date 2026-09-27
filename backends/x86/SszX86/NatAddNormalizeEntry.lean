import SszX86.NatAddNormalizeLeft
import SszX86.NatAddNormalizeRight

namespace SszX86.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem left_normalize_entry (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rsi.toBitVec = 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 326))
    (large : s.regs.rsi.toBitVec ≠ 0#64 → ∀ flags,
      Eventually (step e) P
        (leftNormalizeState s (s.regs.rdx.toBitVec + 1) (s.regs.rdx.toBitVec + 1) flags, base + 288)) :
    Eventually (step e) P (s, base + 271) := by
  have target := hc.targets ("natAdd_u326", 326) (by decide)
  natadd_step 75 using hc
  constructor <;> natadd_step 76 using hc
  all_goals
    by_cases hz : s.regs.rsi.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using small hz _
    · simp [StatusFlags.from_result, hz, Effects.All]
      natadd_step 77 using hc
      natadd_step 78 using hc
      natadd_step 79 using hc
      simpa [leftNormalizeState] using large hz _

theorem right_normalize_entry (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (rightNormalizeState s (s.regs.r8.toBitVec + 1) (s.regs.r8.toBitVec + 1) flags, base + 352)) :
    Eventually (step e) P (s, base + 333) := by
  natadd_step 91 using hc
  natadd_step 92 using hc
  natadd_step 93 using hc
  natadd_step 94 using hc
  simpa [rightNormalizeState] using next _

theorem left_small_normalize (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rsi := 0}, status := flags}, base + 598)) :
    Eventually (step e) P (s, base + 326) := by
  natadd_step 89 using hc
  constructor <;> natadd_step 90 using hc
  all_goals exact next _

theorem right_small_normalize (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rcx := 0}, status := flags}, base + 585)) :
    Eventually (step e) P (s, base + 390) := by
  natadd_step 104 using hc
  constructor <;> natadd_step 105 using hc
  all_goals exact next _

/-- The extra reserved word is included in the final normalization count. -/
theorem result_normalize_entry (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with
          rax := UInt64.ofBitVec (s.regs.rax.toBitVec + 2#64)
          rcx := 0}
        status := flags}, base + 1344)) :
    Eventually (step e) P (s, base + 1325) := by
  natadd_step 353 using hc
  natadd_step 354 using hc
  constructor <;> natadd_step 355 using hc
  all_goals natadd_step 356 using hc
  all_goals simpa only [UInt64.ofBitVec_add, UInt64.ofBitVec_toBitVec,
    UInt64.ofBitVec_ofNat, UInt64.add_comm] using next _

end SszX86.NatAdd
