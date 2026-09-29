import SszX86.IndicesNatShrCounterexampleEntry

namespace SszX86.IndicesNatShr.Counterexample

private theorem finish_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (flags : StatusFlags) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (at150 m flags, base + 150)) :
    Eventually (step e) P (at117 m flags, base + 117) := by
  simp only [at117]
  shr_counter_step 31 using hc
  shr_counter_step 32 using hc
  shr_counter_step 33 using hc
  shr_counter_step 34 using hc
  shr_counter_load scratch_saved0 m
  shr_counter_step 35 using hc
  shr_counter_load scratch_saved1 m
  shr_counter_step 36 using hc
  shr_counter_step 37 using hc
  shr_counter_step 38 using hc
  shr_counter_step 39 using hc
  simpa only [at150, state] using next _

private theorem shift_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (flags : StatusFlags) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (at169 m flags, base + 169)) :
    Eventually (step e) P (at150 m flags, base + 150) := by
  simp only [at150]
  shr_counter_step 40 using hc
  shr_counter_step 41 using hc
  shr_counter_step 42 using hc
  shr_counter_step 43 using hc
  shr_counter_step 44 using hc
  shr_counter_step 45 using hc
  shr_counter_step 46 using hc
  simpa only [at169, at150, state] using next _

private theorem small_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (flags : StatusFlags) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (at192 m flags, base + 192)) :
    Eventually (step e) P (at169 m flags, base + 169) := by
  simp only [at169, at150]
  shr_counter_step 47 using hc
  shr_counter_step 48 using hc
  shr_counter_step 49 using hc
  shr_counter_step 50 using hc
  shr_counter_step 51 using hc
  shr_counter_step 52 using hc
  simpa only [at192, state] using next _

/-- The actual u128 tests establish bit length 66, nonzero shift 64,
and the small-result branch; no result is assumed at this boundary. -/
theorem scan_to192 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (flags : StatusFlags) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (at192 m flags, base + 192)) :
    Eventually (step e) P (at117 m flags, base + 117) := by
  apply finish_scan e base hc m flags P
  intro flags
  apply shift_guard e base hc m flags P
  intro flags
  exact small_guard e base hc m flags P next

end SszX86.IndicesNatShr.Counterexample
