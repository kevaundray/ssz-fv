import SszArm.MeasureScalarListWidth

namespace SszArm.Measure.Scalar.Bytes

open Result
open SszNative (NatOperand)

@[irreducible] def listWordCompared (s : ArmState) (base : BitVec 64) : ArmState :=
  let bound := read_mem_bytes 8 (r (.GPR 8#5) s) s
  w .PC (base + if r (.GPR 20#5) s = bound then 3744#64 else 2376#64)
    (write_pstate (AddWithCarry (r (.GPR 20#5) s) (~~~bound) 1#1).2
      (w (.GPR 10#5) bound s))

theorem list_flag_pc (s : ArmState) (flag : PFlag) (value : BitVec 1) (pc : BitVec 64) :
    w (.FLAG flag) value (w .PC pc s) = w .PC pc (w (.FLAG flag) value s) :=
  w_of_w_commute (by intro equal; cases equal)

private theorem list_word_effect (s : ArmState) (base : BitVec 64) (flags : PState)
    (comparison : (AddWithCarry (r (.GPR 20#5) s)
      (~~~read_mem_bytes 8 (r (.GPR 8#5) s) s) 1#1).2 = flags)
    (zero : flags.z = 1#1 ↔ r (.GPR 20#5) s = read_mem_bytes 8 (r (.GPR 8#5) s) s)
    (pc : read_pc s = base + 2356#64)
    (actual : r (.GPR 20#5) s ≠ 0#64) (count : r (.GPR 9#5) s ≠ 0#64) :
    effect [p2356, p2360, p2364, p2368, p2372] s =
      w .PC (base + if r (.GPR 20#5) s = read_mem_bytes 8 (r (.GPR 8#5) s) s
        then 3744#64 else 2376#64)
        (write_pstate flags (w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 8#5) s) s) s)) := by
  change r .PC s = _ at pc
  by_cases equal : r (.GPR 20#5) s = read_mem_bytes 8 (r (.GPR 8#5) s) s <;>
    simp_all (config := {decide := true})
      [effect, ListSteps.p2356_effect, ListSteps.p2360_effect, ListSteps.p2364_effect,
       ListSteps.p2368_effect, ListSteps.p2372_effect, state_simp_rules,
       list_flag_pc, NatExact.gpr_w_pc, w_of_w_shadow, BitVec.add_assoc]


theorem list_word_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2356#64)
    (actual : r (.GPR 20#5) s ≠ 0#64) (count : r (.GPR 9#5) s ≠ 0#64) :
    run 5 s = listWordCompared s base := by
  have equal := Udivti3.cmp_zero (r (.GPR 20#5) s) (read_mem_bytes 8 (r (.GPR 8#5) s) s)
  have follows : Follows base [p2356, p2360, p2364, p2368, p2372] s := by
    change r .PC s = _ at pc
    change r .ERR s = _ at error
    simp (config := {decide := true})
      [Follows, ListSteps.p2356_effect, ListSteps.p2360_effect, ListSteps.p2364_effect,
       ListSteps.p2368_effect,
       show p2356.offset = 2356 from rfl, show p2360.offset = 2360 from rfl,
       show p2364.offset = 2364 from rfl, show p2368.offset = 2368 from rfl,
       show p2372.offset = 2372 from rfl,
       state_simp_rules, pc, error, actual, count, BitVec.add_assoc]
  rw [show 5 = [p2356, p2360, p2364, p2368, p2372].length by rfl, runs _ s base code follows]
  simpa only [listWordCompared] using list_word_effect s base _ rfl equal pc actual count


theorem list_word_frame (s : ArmState) (base : BitVec 64) :
    NatNarrow.Frame s (listWordCompared s base) := by
  constructor
  · simp [listWordCompared, state_simp_rules]
  · simp [listWordCompared, state_simp_rules]
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [listWordCompared, state_simp_rules]
  · intro reg; simp [listWordCompared, state_simp_rules]
  · intro address outside; simp [listWordCompared, state_simp_rules]

theorem list_word (s : ArmState) (base : BitVec 64) (cap : NatOperand) (size : Nat)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2356#64) (physical : size < 2^64) (positive : 0 < size)
    (pointer : r (.GPR 8#5) s = cap.pointer) (payload : r (.GPR 9#5) s = cap.payload)
    (actual : r (.GPR 20#5) s = BitVec.ofNat 64 size)
    (count : cap.payload ≠ 0#64)
    (bound : (read_mem_bytes 8 cap.pointer s).toNat = cap.value) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready .list t base cap size := by
  let u := listWordCompared s base
  have actualNonzero : r (.GPR 20#5) s ≠ 0#64 := by rw [actual]; bv_omega
  have hu : run 5 s = u := list_word_run s base code error pc actualNonzero
    (by simpa only [payload] using count)
  have uf : NatNarrow.Frame s u := list_word_frame s base
  have keep (reg : BitVec 5) (different : reg ≠ 10#5) : r (.GPR reg) u = r (.GPR reg) s := by
    simp [u, listWordCompared, NatExact.r_gpr_w, different, state_simp_rules]
  have low : (r (.GPR 10#5) u).toNat = cap.value := by
    simpa [u, listWordCompared, state_simp_rules, pointer] using bound
  by_cases equal : r (.GPR 20#5) s = read_mem_bytes 8 (r (.GPR 8#5) s) s
  · have accepted : size ≤ cap.value := by
      have numbers := congrArg BitVec.toNat equal
      rw [actual, pointer, bound, BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical] at numbers
      omega
    refine ⟨7, successReady u base, ?_,
      (Frame.of_narrow uf).trans (success_ready_frame u base), ?_⟩
    · rw [show 7 = 5 + 2 by decide, run_plus, hu]
      exact success_ready_run u base (code.congr uf.program) (uf.error.trans error)
        (by simp [u, listWordCompared, equal, state_simp_rules])
    · simp (config := {decide := true}) [Ready, Kind.accepts, successReady,
        u, listWordCompared, state_simp_rules, accepted, actual]
  · obtain ⟨fuel, t, ht, tf, ready⟩ := list_compare u base cap size
      (code.congr uf.program) (uf.error.trans error)
      (by simp [u, listWordCompared, equal, state_simp_rules]) physical
      ((keep _ (by decide)).trans pointer) ((keep _ (by decide)).trans payload)
      ((keep _ (by decide)).trans actual) low
    exact ⟨5 + fuel, t, by rw [run_plus, hu, ht], (Frame.of_narrow uf).trans tf, ready⟩

theorem list_zero (s : ArmState) (base : BitVec 64) (cap : NatOperand)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2356#64) (actual : r (.GPR 20#5) s = 0#64) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready .list t base cap 0 := by
  let u := w .PC (base + 3744#64) s
  have hu : run 1 s = u := by
    have follows : Follows base [p2356] s := ⟨error, pc, trivial⟩
    rw [show 1 = [p2356].length by rfl, runs _ s base code follows]
    change r .PC s = _ at pc
    simp [effect, ListSteps.p2356_effect, u, pc, actual, BitVec.add_assoc]
  have uf : Frame s u := by
    constructor <;> first
      | (intro reg member; simp [u, state_simp_rules])
      | (intro reg; simp [u, state_simp_rules])
      | (simp [u, state_simp_rules])
  refine ⟨3, successReady u base, ?_, uf.trans (success_ready_frame u base), ?_⟩
  · rw [show 3 = 1 + 2 by decide, run_plus, hu]
    exact success_ready_run u base (code.congr uf.program) (uf.error.trans error)
      (by simp [u, state_simp_rules])
  · simp (config := {decide := true}) [Ready, Kind.accepts, successReady, u,
      state_simp_rules, actual]

end SszArm.Measure.Scalar.Bytes
