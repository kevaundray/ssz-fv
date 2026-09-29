import SszX86.IndicesNatShrCounterexampleCore

namespace SszX86.IndicesNatShr.Counterexample

private theorem entry_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (hm : InitialMemory m) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (at39 m flags, base + 39)) :
    Eventually (step e) P (initial m flags, base) := by
  simp only [initial]
  rw [← Int64.add_zero base]
  shr_counter_step 0 using hc
  shr_counter_step 1 using hc
  shr_counter_step 2 using hc
  shr_counter_step 3 using hc
  shr_counter_step 4 using hc
  shr_counter_step 5 using hc
  shr_counter_step 6 using hc
  shr_counter_load hm.high
  shr_counter_step 7 using hc
  shr_counter_step 8 using hc
  shr_counter_step 9 using hc
  simpa only [at39, state] using next _

private theorem width_prefix (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (flags : StatusFlags) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (at80 m flags, base + 80)) :
    Eventually (step e) P (at39 m flags, base + 39) := by
  simp only [at39]
  shr_counter_step 10 using hc
  shr_counter_step 11 using hc
  shr_counter_step 12 using hc
  shr_counter_step 13 using hc
  shr_counter_step 14 using hc
  shr_counter_step 15 using hc
  simpa only [at80, state] using next _

private theorem spill_and_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (hm : InitialMemory m) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (at109 m flags, base + 109)) :
    Eventually (step e) P (at80 m flags, base + 80) := by
  simp only [at80]
  shr_counter_step 21 using hc
  shr_counter_step 22 using hc
  apply Delimited.store_cps
  · exact hm.scratch0
  simp only [Effects.All]
  shr_counter_step 23 using hc
  apply Delimited.store_cps
  · simpa (disch := decide) [load_store_separate] using hm.scratch1
  simp only [Effects.All]
  shr_counter_step 24 using hc
  shr_counter_step 25 using hc
  shr_counter_step 26 using hc
  shr_counter_step 27 using hc
  simpa only [at109, state, scratchMem] using next _

private theorem two_scan_iterations (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (flags : StatusFlags) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (at117 m flags, base + 117)) :
    Eventually (step e) P (at109 m flags, base + 109) := by
  have target := hc.targets ("indices_nat_shr_u109", 109) (by decide)
  simp only [at109]
  shr_counter_step 28 using hc
  shr_counter_step 29 using hc
  shr_counter_step 30 using hc
  rw [target]
  shr_counter_step 28 using hc
  shr_counter_step 29 using hc
  shr_counter_step 30 using hc
  simpa only [at117, state] using next _

/-- From original PC zero through the actual two iterations of the bit scan. -/
theorem entry_to117 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (hm : InitialMemory m) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (at117 m flags, base + 117)) :
    Eventually (step e) P (initial m flags, base) := by
  apply entry_scan e base hc m hm flags P
  intro flags
  apply width_prefix e base hc m flags P
  intro flags
  apply spill_and_scan e base hc m hm flags P
  intro flags
  exact two_scan_iterations e base hc m flags P next

end SszX86.IndicesNatShr.Counterexample
