import SszX86.MeasureBitsEntry

namespace SszX86.Measure.Bits
open UintCodec

def smallListMem (s : MachineData) : DataMem :=
  Mem.storeInt
    (Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 s.regs.rcx.toBitVec.toInt)
    (s.regs.rsp.toBitVec + 16#64) 8 s.regs.r15.toBitVec.toInt

theorem list_small_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (work : Large.Mapped s.dmem s.regs.rsp.toBitVec 24)
    (next : ∀ flags, Eventually (step e) P
      ({s with dmem := smallListMem s, regs := {s.regs with rbp := 0}, status := flags},
        base + 1341)) :
    Eventually (step e) P (s, base + 912) := by
  measure_step 108 using hc
  apply Delimited.store_cps
  · exact Large.mapped_load _ _ 24 8 8 work (by decide)
  simp only [Effects.All]
  measure_step 109 using hc
  constructor
  all_goals
    measure_step 110 using hc
    apply Delimited.store_cps
    · apply Large.mapped_load (capacity := 24) («offset» := 16) («width» := 8)
      · exact Large.mapped_store _ _ _ _ _ _ work
      · decide
    simp only [Effects.All]
    measure_step 111 using hc
    simpa [smallListMem] using next _

theorem progressive_small_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r13 := 0, rsi := s.regs.r15}, status := flags},
        base + 1520)) :
    Eventually (step e) P (s, base + 966) := by
  measure_step 121 using hc
  constructor <;> measure_step 122 using hc
  all_goals measure_step 123 using hc
  all_goals simpa using next _

theorem vector_small_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r8 := 0}, status := flags}, base + 2785)) :
    Eventually (step e) P (s, base + 1654) := by
  measure_step 217 using hc
  constructor <;> measure_step 218 using hc
  all_goals simpa using next _

theorem vector_zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r8 := 0, rdi := 0}, status := flags}, base + 2785)) :
    Eventually (step e) P (s, base + 2780) := by
  measure_step 373 using hc
  constructor <;> measure_step 374 using hc
  all_goals constructor <;> simpa using next _

theorem vector_small_error_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rcx := 0}, status := flags}, base + 2893)) :
    Eventually (step e) P (s, base + 2810) := by
  measure_step 383 using hc
  constructor <;> measure_step 384 using hc
  all_goals simpa using next _

theorem list_compare_prepare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with
        rdi := s.regs.rbp
        rsi := s.regs.r15
        rdx := s.regs.r13
        rcx := s.regs.r12}}, base + 1353)) :
    Eventually (step e) P (s, base + 1341) := by
  measure_step 148 using hc
  measure_step 149 using hc
  measure_step 150 using hc
  measure_step 151 using hc
  simpa using next

end SszX86.Measure.Bits
