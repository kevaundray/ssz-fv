import SszArm.MeasureScalarListSteps

namespace SszArm.Measure.Scalar.Bytes

open Result
open SszNative (NatOperand)

def listCompareOps (actual bound : BitVec 64) : List Op :=
  [p2376, p2380] ++ if actual.toNat ≤ bound.toNat then [] else [p2384]

macro "measure_list_compare_expand" branch:term:max : tactic => `(tactic|
  (simp only [listCompareOps, ($branch), ↓reduceIte]
   all_goals simp_all (config := {decide := true, instances := true})
    [Follows, effect, ListSteps.p2376_effect, ListSteps.p2380_effect, ListSteps.p2384_effect,
     show p2376.offset = 2376 from rfl, show p2380.offset = 2380 from rfl,
     show p2384.offset = 2384 from rfl,
     state_simp_rules, NatExact.r_gpr_w, BitVec.add_assoc]
   all_goals first | omega | (split <;> simp_all [BitVec.add_assoc] <;> omega)))

theorem list_compare (s : ArmState) (base : BitVec 64) (cap : NatOperand) (size : Nat)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2376#64) (physical : size < 2^64)
    (pointer : r (.GPR 8#5) s = cap.pointer) (payload : r (.GPR 9#5) s = cap.payload)
    (actual : r (.GPR 20#5) s = BitVec.ofNat 64 size)
    (bound : (r (.GPR 10#5) s).toNat = cap.value) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready .list t base cap size := by
  have selection : (r (.GPR 20#5) s).toNat ≤ (r (.GPR 10#5) s).toNat ↔ size ≤ cap.value := by
    simp [actual, bound, BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical]
  have flags := ListSteps.unsigned_le (r (.GPR 20#5) s) (r (.GPR 10#5) s)
  let ops := listCompareOps (r (.GPR 20#5) s) (r (.GPR 10#5) s)
  let u := effect ops s
  have hpc : r .PC s = base + 2376#64 := pc
  have herr : r .ERR s = .None := error
  have follows : Follows base ops s := by
    dsimp [ops]
    by_cases branch : (r (.GPR 20#5) s).toNat ≤ (r (.GPR 10#5) s).toNat <;>
      measure_list_compare_expand branch
  have hu : run ops.length s = u := runs ops s base code follows
  have uf : NatNarrow.Frame s u := by
    constructor
    · dsimp [u, ops]; by_cases branch : (r (.GPR 20#5) s).toNat ≤ (r (.GPR 10#5) s).toNat <;> measure_list_compare_expand branch
    · dsimp [u, ops]; by_cases branch : (r (.GPR 20#5) s).toNat ≤ (r (.GPR 10#5) s).toNat <;> measure_list_compare_expand branch
    · intro reg outside; dsimp [u, ops]; by_cases branch : (r (.GPR 20#5) s).toNat ≤ (r (.GPR 10#5) s).toNat <;> measure_list_compare_expand branch
    · intro reg; dsimp [u, ops]; by_cases branch : (r (.GPR 20#5) s).toNat ≤ (r (.GPR 10#5) s).toNat <;> measure_list_compare_expand branch
    · intro address outside; dsimp [u, ops]; by_cases branch : (r (.GPR 20#5) s).toNat ≤ (r (.GPR 10#5) s).toNat <;> measure_list_compare_expand branch
  have keep (reg : BitVec 5) : r (.GPR reg) u = r (.GPR reg) s := by
    dsimp [u, ops]; by_cases branch : (r (.GPR 20#5) s).toNat ≤ (r (.GPR 10#5) s).toNat <;> measure_list_compare_expand branch
  by_cases accepted : size ≤ cap.value
  · have up : read_pc u = base + 3744#64 := by
      have branch := selection.mpr accepted
      dsimp [u, ops]; measure_list_compare_expand branch
    refine ⟨ops.length + 2, successReady u base, ?_,
      (Frame.of_narrow uf).trans (success_ready_frame u base), ?_⟩
    · rw [run_plus, hu]
      exact success_ready_run u base (code.congr uf.program) (uf.error.trans error) up
    · simp (config := {decide := true})
        [Ready, Kind.accepts, successReady, state_simp_rules, keep, actual, accepted]
  · refine ⟨ops.length, u, hu, Frame.of_narrow uf, ?_⟩
    refine ⟨(keep _).trans actual, ?_⟩
    simp only [Kind.accepts, accepted, ↓reduceIte]
    refine ⟨?_, (keep _).trans pointer, (keep _).trans payload⟩
    have branch : ¬(r (.GPR 20#5) s).toNat ≤ (r (.GPR 10#5) s).toNat :=
      fun possible => accepted (selection.mp possible)
    dsimp [u, ops, Kind.reject]; measure_list_compare_expand branch

end SszArm.Measure.Scalar.Bytes
