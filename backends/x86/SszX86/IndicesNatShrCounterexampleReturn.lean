import SszX86.IndicesNatShrCounterexampleBranch

namespace SszX86.IndicesNatShr.Counterexample

private theorem small_loads (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (hm : InitialMemory m) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (at665 m flags, base + 665)) :
    Eventually (step e) P (at192 m flags, base + 192) := by
  have target := hc.targets ("indices_nat_shr_u665", 665) (by decide)
  simp only [at192]
  shr_counter_step 53 using hc
  shr_counter_step 54 using hc
  shr_counter_step 55 using hc
  shr_counter_step 56 using hc
  shr_counter_step 57 using hc
  shr_counter_load (scratch_low m hm)
  shr_counter_step 58 using hc
  shr_counter_step 59 using hc
  shr_counter_step 60 using hc
  shr_counter_step 61 using hc
  simpa only [target, at665, state] using next _

/-- CL=64 is masked to zero by SHR; NEG changes CL to 192, which is
also masked to zero by SHL. Thus the real OR computes 5 OR 2 = 7. -/
private theorem combine_words (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (hm : InitialMemory m) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (at680 m flags, base + 680)) :
    Eventually (step e) P (at665 m flags, base + 665) := by
  simp only [at665]
  shr_counter_step 188 using hc
  shr_counter_load (scratch_high m hm)
  shr_counter_step 189 using hc
  shr_counter_step 190 using hc
  shr_counter_step 191 using hc
  shr_counter_step 192 using hc
  simpa only [at680, state] using next _

private theorem result_stores (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (hm : InitialMemory m) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (at696 m flags, base + 696)) :
    Eventually (step e) P (at680 m flags, base + 680) := by
  simp only [at680]
  shr_counter_step 193 using hc
  apply Delimited.store_cps
  · simpa (disch := decide) [scratchMem, load_store_separate] using hm.outputPointer
  simp only [Effects.All]
  shr_counter_step 194 using hc
  apply Delimited.store_cps
  · simpa (disch := decide) [scratchMem, load_store_separate] using hm.outputPayload
  simp only [Effects.All]
  shr_counter_step 195 using hc
  shr_counter_step 196 using hc
  apply Delimited.store_cps
  · simpa (disch := decide) [scratchMem, load_store_separate] using hm.outputTag
  simp only [Effects.All]
  simpa only [at696, state, returnedMem] using next _

private theorem actual_ret (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (hm : InitialMemory m) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (returned m flags, 32768)) :
    Eventually (step e) P (at696 m flags, base + 696) := by
  simp only [at696]
  shr_counter_step 197 using hc
  shr_counter_load (returned_address m hm)
  simpa only [returned, state] using next flags

/-- Execute the selected small branch, all three active result stores, and RET. -/
theorem small_to_return (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (hm : InitialMemory m) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (returned m flags, 32768)) :
    Eventually (step e) P (at192 m flags, base + 192) := by
  apply small_loads e base hc m hm flags P
  intro flags
  apply combine_words e base hc m hm flags P
  intro flags
  apply result_stores e base hc m hm flags P
  intro flags
  exact actual_ret e base hc m hm flags P next

end SszX86.IndicesNatShr.Counterexample
