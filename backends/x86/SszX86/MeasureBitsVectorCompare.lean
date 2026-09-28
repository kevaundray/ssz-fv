import SszX86.MeasureBitsVectorScan
import SszX86.MeasureBitsControl
import SszX86.MeasureBitsSmall

namespace SszX86.Measure.Bits
open UintCodec

/-- The two-word equality operation changes only its two scratch registers. -/
def pairCompared (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rdi := UInt64.ofBitVec (s.regs.rdi.toBitVec ^^^ s.regs.rax.toBitVec)
      r8 := UInt64.ofBitVec ((s.regs.r8.toBitVec ^^^ s.regs.rdx.toBitVec) |||
        (s.regs.rdi.toBitVec ^^^ s.regs.rax.toBitVec))}
    status := flags}

theorem vector_pair_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (pairCompared s flags,
        if s.regs.rdi.toBitVec = s.regs.rax.toBitVec ∧ s.regs.r8.toBitVec = s.regs.rdx.toBitVec
        then base + 2796 else base + 2805)) :
    Eventually (step e) P (s, base + 2785) := by
  have target := hc.targets ("measure_u2805", 2805) (by decide)
  measure_step 375 using hc
  constructor <;> measure_step 376 using hc
  all_goals constructor <;> measure_step 377 using hc
  all_goals constructor <;> measure_step 378 using hc
  all_goals
    by_cases same : s.regs.rdi.toBitVec = s.regs.rax.toBitVec ∧
        s.regs.r8.toBitVec = s.regs.rdx.toBitVec
    · have low : s.regs.rdi = s.regs.rax := UInt64.toBitVec_inj.mp same.1
      have high : s.regs.r8 = s.regs.rdx := UInt64.toBitVec_inj.mp same.2
      simpa [pairCompared, low, high, StatusFlags.from_result, Effects.All] using next _
    · have different : ((s.regs.r8.toBitVec ^^^ s.regs.rdx.toBitVec) |||
          (s.regs.rdi.toBitVec ^^^ s.regs.rax.toBitVec)) ≠ 0#64 := by
        simpa [and_comm] using same
      simpa [pairCompared, same, different, target, StatusFlags.from_result, Effects.All] using next _

/-- A successful equality uses the physical backing byte count, not a narrowed
logical descriptor value. -/
theorem vector_size_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (byteCount : BitVec 64) (P : MachineState → Prop)
    (stored : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 24#64) 8 = some (byteCount.toNat : Int))
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rax := UInt64.ofBitVec byteCount}}, base + 3050)) :
    Eventually (step e) P (s, base + 2796) := by
  measure_step 379 using hc
  natfrom_load stored
  measure_step 380 using hc
  simpa using next

theorem vector_pair_join_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rdi := s.regs.r9}}, base + 2785)) :
    Eventually (step e) P (s, base + 2665) := by
  measure_step 341 using hc
  measure_step 342 using hc
  simpa using next

theorem vector_one_high_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r8 := 0}, status := flags}, base + 2665)) :
    Eventually (step e) P (s, base + 2662) := by
  measure_step 340 using hc
  constructor <;> simpa using next _

theorem vector_high_word_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (high : BitVec 64) (P : MachineState → Prop)
    (stored : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 8#64) 8 = some (high.toNat : Int))
    (next : Eventually (step e) P
      ({s with regs := {s.regs with r8 := UInt64.ofBitVec high}}, base + 2665)) :
    Eventually (step e) P (s, base + 1876) := by
  measure_step 262 using hc
  natfrom_load stored
  measure_step 263 using hc
  simpa using next

/-- The stored length, not the trimmed significant length, controls the second
physical word read. This includes arbitrary high zero padding. -/
theorem vector_low_word_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (low : BitVec 64) (P : MachineState → Prop)
    (stored : Mem.loadInt s.dmem s.regs.r8.toBitVec 8 = some (low.toNat : Int))
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r9 := UInt64.ofBitVec low}, status := flags},
        if s.regs.rdi.toNat < 2 then base + 2662 else base + 1876)) :
    Eventually (step e) P (s, base + 1863) := by
  have target := hc.targets ("measure_u2662", 2662) (by decide)
  measure_step 259 using hc
  natfrom_load stored
  measure_step 260 using hc
  measure_step 261 using hc
  by_cases one : s.regs.rdi.toNat < 2
  · simpa [one, target, StatusFlags.from_result, Effects.All] using next _
  · simpa [one, target, StatusFlags.from_result, Effects.All] using next _

/-- Three or more significant words cannot fit the full128-bit count. -/
theorem vector_scan_exit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.r10.toNat < 3 then base + 1863 else base + 2805)) :
    Eventually (step e) P (s, base + 153) := by
  have target := hc.targets ("measure_u1863", 1863) (by decide)
  measure_step 35 using hc
  measure_step 36 using hc
  by_cases few : s.regs.r10.toNat < 3
  · simpa [few, target, StatusFlags.from_result, Effects.All] using next _
  · simp [few, StatusFlags.from_result, Effects.All]
    measure_step 37 using hc
    simpa [few] using next _

theorem vector_scan_begin_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with r9 := UInt64.ofBitVec (s.regs.rdi.toBitVec + 1#64)}}, base + 128)) :
    Eventually (step e) P (s, base + 115) := by
  measure_step 27 using hc
  measure_step 28 using hc
  simpa [BitVec.add_comm] using next

end SszX86.Measure.Bits
