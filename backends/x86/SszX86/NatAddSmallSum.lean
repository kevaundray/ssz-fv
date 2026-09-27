import SszX86.NatAddCore

namespace SszX86.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

private theorem decide_uint64_false {p : Prop} [Decidable p] (h : ¬ p) :
    (OfNat.ofNat (decide p).toNat : UInt64) = 0 := by
  exact congrArg (fun n : Nat => (OfNat.ofNat n : UInt64))
    (show (decide p).toNat = 0 by simp [h])

private theorem decide_uint64_true {p : Prop} [Decidable p] (h : p) :
    (OfNat.ofNat (decide p).toNat : UInt64) = 1 := by
  exact congrArg (fun n : Nat => (OfNat.ofNat n : UInt64))
    (show (decide p).toNat = 1 by simp [h])

def sumStart (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rax := 0}}

def sumState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (BitVec.ofNat 64
        (decide (2^64 ≤ s.regs.rdx.toNat + s.regs.r8.toNat)).toNat)
      rdx := UInt64.ofBitVec (s.regs.rdx.toBitVec + s.regs.r8.toBitVec)}
    status := flags}

def sumExit (s : MachineData) (base : Int64) : Int64 :=
  if s.regs.rdx.toNat + s.regs.r8.toNat < 2^64 then base + 250 else base + 676

/-- The normal one-word ADD/ADC computes the full carry, not a wrapped model. -/
theorem small_sum_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (sumState s flags, sumExit s base)) :
    Eventually (step e) P (sumStart s, base + 237) := by
  have target := hc.targets ("natAdd_u676", 676) (by decide)
  unfold sumStart
  natadd_step 67 using hc
  natadd_step 68 using hc
  natadd_step 69 using hc
  by_cases fits : s.regs.rdx.toNat + s.regs.r8.toNat < 2^64
  · have noCarry : ¬ 18446744073709551616 ≤ s.regs.r8.toNat + s.regs.rdx.toNat := by omega
    have noCarry' : ¬ 18446744073709551616 ≤ s.regs.rdx.toNat + s.regs.r8.toNat := by omega
    simpa (config := {instances := true}) [decide_uint64_false noCarry, sumState, sumExit, fits, StatusFlags.from_result, noCarry, noCarry',
      UInt64.add_comm, Udivti3.radix, Effects.All] using next _
  · have carry : 18446744073709551616 ≤ s.regs.r8.toNat + s.regs.rdx.toNat := by omega
    have carry' : 18446744073709551616 ≤ s.regs.rdx.toNat + s.regs.r8.toNat := by omega
    simpa (config := {instances := true}) [decide_uint64_true carry, sumState, sumExit, fits, StatusFlags.from_result, carry, carry', target,
      UInt64.add_comm, Udivti3.radix, Effects.All] using next _

/-- The Large-right one-word branch has its own linked ADD/ADC pair. -/
theorem loaded_sum_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (sumState s flags, sumExit s base)) :
    Eventually (step e) P (sumStart s, base + 647) := by
  have target := hc.targets ("natAdd_u676", 676) (by decide)
  unfold sumStart
  natadd_step 172 using hc
  natadd_step 173 using hc
  natadd_step 174 using hc
  by_cases fits : s.regs.rdx.toNat + s.regs.r8.toNat < 2^64
  · have noCarry : ¬ 18446744073709551616 ≤ s.regs.r8.toNat + s.regs.rdx.toNat := by omega
    have noCarry' : ¬ 18446744073709551616 ≤ s.regs.rdx.toNat + s.regs.r8.toNat := by omega
    simp (config := {instances := true}) [StatusFlags.from_result, noCarry, Effects.All]
    rw [decide_uint64_false noCarry]
    natadd_step 175 using hc
    simpa [sumState, sumExit, fits, noCarry', UInt64.add_comm, Udivti3.radix] using next _
  · have carry : 18446744073709551616 ≤ s.regs.r8.toNat + s.regs.rdx.toNat := by omega
    have carry' : 18446744073709551616 ≤ s.regs.rdx.toNat + s.regs.r8.toNat := by omega
    simpa (config := {instances := true}) [decide_uint64_true carry, sumState, sumExit, fits, StatusFlags.from_result, carry, carry', target,
      UInt64.add_comm, Udivti3.radix, Effects.All] using next _

/-- Small/Small uses the reversed branch direction but the identical wide sum. -/
theorem inline_sum_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (sumState s flags, sumExit s base)) :
    Eventually (step e) P (sumStart s, base + 663) := by
  have target := hc.targets ("natAdd_u250", 250) (by decide)
  unfold sumStart
  natadd_step 177 using hc
  natadd_step 178 using hc
  natadd_step 179 using hc
  by_cases fits : s.regs.rdx.toNat + s.regs.r8.toNat < 2^64
  · have noCarry : ¬ 18446744073709551616 ≤ s.regs.r8.toNat + s.regs.rdx.toNat := by omega
    have noCarry' : ¬ 18446744073709551616 ≤ s.regs.rdx.toNat + s.regs.r8.toNat := by omega
    simpa (config := {instances := true}) [decide_uint64_false noCarry, sumState, sumExit, fits, StatusFlags.from_result, noCarry, noCarry', target,
      UInt64.add_comm, Udivti3.radix, Effects.All] using next _
  · have carry : 18446744073709551616 ≤ s.regs.r8.toNat + s.regs.rdx.toNat := by omega
    have carry' : 18446744073709551616 ≤ s.regs.rdx.toNat + s.regs.r8.toNat := by omega
    simpa (config := {instances := true}) [decide_uint64_true carry, sumState, sumExit, fits, StatusFlags.from_result, carry, carry',
      UInt64.add_comm, Udivti3.radix, Effects.All] using next _

theorem empty_sum_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (sumState s flags, sumExit s base)) :
    Eventually (step e) P (sumStart s, base + 844) := by
  have target := hc.targets ("natAdd_u676", 676) (by decide)
  unfold sumStart
  natadd_step 215 using hc
  natadd_step 216 using hc
  natadd_step 217 using hc
  by_cases fits : s.regs.rdx.toNat + s.regs.r8.toNat < 2^64
  · have noCarry : ¬ 18446744073709551616 ≤ s.regs.r8.toNat + s.regs.rdx.toNat := by omega
    have noCarry' : ¬ 18446744073709551616 ≤ s.regs.rdx.toNat + s.regs.r8.toNat := by omega
    simp (config := {instances := true}) [StatusFlags.from_result, noCarry, Effects.All]
    rw [decide_uint64_false noCarry]
    natadd_step 218 using hc
    simpa [sumState, sumExit, fits, noCarry', UInt64.add_comm, Udivti3.radix] using next _
  · have carry : 18446744073709551616 ≤ s.regs.r8.toNat + s.regs.rdx.toNat := by omega
    have carry' : 18446744073709551616 ≤ s.regs.rdx.toNat + s.regs.r8.toNat := by omega
    simpa (config := {instances := true}) [decide_uint64_true carry, sumState, sumExit, fits, StatusFlags.from_result, carry, carry', target,
      UInt64.add_comm, Udivti3.radix, Effects.All] using next _

end SszX86.NatAdd
