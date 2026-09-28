import SszArm.MeasureScalarListCompare

namespace SszArm.Measure.Scalar.Bytes

open Result
open SszNative (NatOperand)

def listWidthOps (a b : BitVec 64) : List Op :=
  [p2332, p2336] ++ (if a.toNat < b.toNat then [p2348] else [p2340, p2344]) ++ [p2352]

@[irreducible] def listWidthCompared (s : ArmState) (base : BitVec 64) : ArmState :=
  let a := r (.GPR 11#5) s
  let b := r (.GPR 10#5) s
  w .PC (base + if a = b then 2356#64 else 2388#64)
    (w (.GPR 10#5) (if a.toNat < b.toNat then 1#64 else 0#64)
      (write_pstate (AddWithCarry a (~~~b) 1#1).2 s))

private theorem flag_pc (s : ArmState) (flag : PFlag) (value : BitVec 1) (pc : BitVec 64) :
    w (.FLAG flag) value (w .PC pc s) = w .PC pc (w (.FLAG flag) value s) :=
  w_of_w_commute (by intro equal; cases equal)

private theorem reverse_width_guard (a b : BitVec 64) :
    if a.toNat < b.toNat then ¬b.toNat ≤ a.toNat else b.toNat ≤ a.toNat := by
  split <;> omega

private theorem list_width_effect (s : ArmState) (base : BitVec 64) (flags : PState)
    (comparison : (AddWithCarry (r (.GPR 11#5) s) (~~~r (.GPR 10#5) s) 1#1).2 = flags)
    (carry : flags.c = 1#1 ↔ (r (.GPR 10#5) s).toNat ≤ (r (.GPR 11#5) s).toNat)
    (zero : flags.z = 1#1 ↔ r (.GPR 11#5) s = r (.GPR 10#5) s)
    (pc : read_pc s = base + 2332#64) :
    effect (listWidthOps (r (.GPR 11#5) s) (r (.GPR 10#5) s)) s =
      w .PC (base + if r (.GPR 11#5) s = r (.GPR 10#5) s then 2356#64 else 2388#64)
        (w (.GPR 10#5) (if (r (.GPR 11#5) s).toNat < (r (.GPR 10#5) s).toNat then 1#64 else 0#64)
          (write_pstate flags s)) := by
  change r .PC s = _ at pc
  by_cases less : (r (.GPR 11#5) s).toNat < (r (.GPR 10#5) s).toNat <;>
    by_cases equal : r (.GPR 11#5) s = r (.GPR 10#5) s <;>
    simp only [listWidthOps, less, ↓reduceIte]
  all_goals have direction := reverse_width_guard (r (.GPR 11#5) s) (r (.GPR 10#5) s)
  all_goals simp only [less, ↓reduceIte] at direction
  all_goals simp_all (config := {decide := true})
    [effect, ListSteps.p2332_effect, ListSteps.p2336_effect, ListSteps.p2340_effect,
     ListSteps.p2344_effect, ListSteps.p2348_effect, ListSteps.p2352_effect,
     state_simp_rules, flag_pc, NatExact.gpr_w_pc, w_of_w_shadow, BitVec.add_assoc]
  all_goals first | omega | (split <;> simp_all [BitVec.add_assoc] <;> omega)


theorem list_width_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2332#64) :
    run (listWidthOps (r (.GPR 11#5) s) (r (.GPR 10#5) s)).length s =
      listWidthCompared s base := by
  have carry := Udivti3.cmp_carry (r (.GPR 11#5) s) (r (.GPR 10#5) s)
  have zero := Udivti3.cmp_zero (r (.GPR 11#5) s) (r (.GPR 10#5) s)
  let ops := listWidthOps (r (.GPR 11#5) s) (r (.GPR 10#5) s)
  have follows : Follows base ops s := by
    change r .PC s = _ at pc
    change r .ERR s = _ at error
    by_cases less : (r (.GPR 11#5) s).toNat < (r (.GPR 10#5) s).toNat <;>
      simp only [ops, listWidthOps, less, ↓reduceIte]
    all_goals have direction := reverse_width_guard (r (.GPR 11#5) s) (r (.GPR 10#5) s)
    all_goals simp only [less, ↓reduceIte] at direction
    all_goals simp_all (config := {decide := true})
      [Follows, ListSteps.p2332_effect, ListSteps.p2336_effect, ListSteps.p2340_effect,
       ListSteps.p2344_effect, ListSteps.p2348_effect, ListSteps.p2352_effect,
       show p2332.offset = 2332 from rfl, show p2336.offset = 2336 from rfl,
       show p2340.offset = 2340 from rfl, show p2344.offset = 2344 from rfl,
       show p2348.offset = 2348 from rfl, show p2352.offset = 2352 from rfl,
       state_simp_rules, flag_pc, NatExact.gpr_w_pc, w_of_w_shadow, BitVec.add_assoc]
    all_goals first | omega | (split <;> simp_all [BitVec.add_assoc] <;> omega)
  rw [runs ops s base code follows]
  simpa only [listWidthCompared] using list_width_effect s base _ rfl carry zero pc


theorem list_width_frame (s : ArmState) (base : BitVec 64) :
    NatNarrow.Frame s (listWidthCompared s base) := by
  constructor
  · simp [listWidthCompared, state_simp_rules]
  · simp [listWidthCompared, state_simp_rules]
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [listWidthCompared, state_simp_rules]
  · intro reg; simp [listWidthCompared, state_simp_rules]
  · intro address outside; simp [listWidthCompared, state_simp_rules]

@[irreducible] def listMarkerResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + if (r (.GPR 10#5) s).setWidth 32 = 0#32 then 3744#64 else 2392#64) s

theorem list_marker_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2388#64) : run 1 s = listMarkerResult s base := by
  have follows : Follows base [p2388] s := ⟨error, pc, trivial⟩
  rw [show 1 = [p2388].length by rfl, runs _ s base code follows]
  change r .PC s = _ at pc
  by_cases zero : (r (.GPR 10#5) s).setWidth 32 = 0#32 <;>
    simp [effect, ListSteps.p2388_effect, listMarkerResult, pc, zero, BitVec.add_assoc]


theorem list_marker (s : ArmState) (base : BitVec 64) (cap : NatOperand) (size : Nat)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2388#64)
    (pointer : r (.GPR 8#5) s = cap.pointer) (payload : r (.GPR 9#5) s = cap.payload)
    (actual : r (.GPR 20#5) s = BitVec.ofNat 64 size)
    (selection : (r (.GPR 10#5) s).setWidth 32 = 0#32 ↔ size ≤ cap.value) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready .list t base cap size := by
  let u := listMarkerResult s base
  have hu : run 1 s = u := list_marker_run s base code error pc
  have uf : Frame s u := by
    constructor
    · simp [u, listMarkerResult, state_simp_rules]
    · simp [u, listMarkerResult, state_simp_rules]
    · simp [u, listMarkerResult, state_simp_rules]
    · simp [u, listMarkerResult, state_simp_rules]
    · intro reg member; simp [u, listMarkerResult, state_simp_rules]
    · intro reg; simp [u, listMarkerResult, state_simp_rules]
    · intro address outside; simp [u, listMarkerResult, state_simp_rules]
  by_cases accepted : size ≤ cap.value
  · have zero := selection.mpr accepted
    refine ⟨3, successReady u base, ?_, uf.trans (success_ready_frame u base), ?_⟩
    · rw [show 3 = 1 + 2 by decide, run_plus, hu]
      exact success_ready_run u base (code.congr uf.program) (uf.error.trans error)
        (by simp [u, listMarkerResult, zero, state_simp_rules])
    · simp (config := {decide := true}) [Ready, Kind.accepts, successReady,
        u, listMarkerResult, state_simp_rules, actual, accepted]
  · have nonzero : (r (.GPR 10#5) s).setWidth 32 ≠ 0#32 := fun zero => accepted (selection.mp zero)
    refine ⟨1, u, hu, uf, ?_⟩
    simp [Ready, Kind.accepts, Kind.reject, u, listMarkerResult, state_simp_rules,
      actual, accepted, nonzero, pointer, payload]

end SszArm.Measure.Scalar.Bytes
