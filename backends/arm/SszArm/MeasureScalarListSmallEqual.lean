import SszArm.MeasureScalarListSmallBranch

namespace SszArm.Measure.Scalar.Bytes

open Result
open SszNative (NatOperand)

def smallEqualOps (actual cap : BitVec 64) : List Op :=
  [p2048, p2052] ++ if actual = 0#64 then [] else
    [p2056, p2060, p2064] ++ if actual = cap then [p2068] else []

@[irreducible] def smallEqualResult (s : ArmState) (base : BitVec 64) : ArmState :=
  let u := w (.GPR 21#5) 0#64 s
  if r (.GPR 20#5) s = 0#64 then w .PC (base + 4144#64) u
  else w .PC (base + if r (.GPR 20#5) s = r (.GPR 9#5) s then 4144#64 else 2376#64)
    (w (.GPR 10#5) (r (.GPR 9#5) s)
      (write_pstate (AddWithCarry (r (.GPR 20#5) s) (~~~r (.GPR 9#5) s) 1#1).2 u))

private theorem small_equal_effect (s : ArmState) (base : BitVec 64) (flags : PState)
    (comparison : (AddWithCarry (r (.GPR 20#5) s) (~~~r (.GPR 9#5) s) 1#1).2 = flags)
    (zero : flags.z = 1#1 ↔ r (.GPR 20#5) s = r (.GPR 9#5) s)
    (pc : read_pc s = base + 2048#64) :
    effect (smallEqualOps (r (.GPR 20#5) s) (r (.GPR 9#5) s)) s =
      if r (.GPR 20#5) s = 0#64 then w .PC (base + 4144#64) (w (.GPR 21#5) 0#64 s)
      else w .PC (base + if r (.GPR 20#5) s = r (.GPR 9#5) s then 4144#64 else 2376#64)
        (w (.GPR 10#5) (r (.GPR 9#5) s) (write_pstate flags (w (.GPR 21#5) 0#64 s))) := by
  change r .PC s = _ at pc
  by_cases empty : r (.GPR 20#5) s = 0#64 <;>
    by_cases equal : r (.GPR 20#5) s = r (.GPR 9#5) s <;>
    simp only [smallEqualOps, empty, equal, ↓reduceIte]
  all_goals simp_all (config := {decide := true})
    [effect, ListSteps.p2048_effect, ListSteps.p2052_effect, ListSteps.p2056_effect,
     ListSteps.p2060_effect, ListSteps.p2064_effect, ListSteps.p2068_effect,
     state_simp_rules, list_flag_pc, NatExact.gpr_w_pc, w_of_w_shadow, BitVec.add_assoc]


theorem small_equal_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2048#64) :
    run (smallEqualOps (r (.GPR 20#5) s) (r (.GPR 9#5) s)).length s = smallEqualResult s base := by
  have zero := Udivti3.cmp_zero (r (.GPR 20#5) s) (r (.GPR 9#5) s)
  let ops := smallEqualOps (r (.GPR 20#5) s) (r (.GPR 9#5) s)
  have follows : Follows base ops s := by
    change r .PC s = _ at pc
    change r .ERR s = _ at error
    by_cases empty : r (.GPR 20#5) s = 0#64 <;>
      by_cases equal : r (.GPR 20#5) s = r (.GPR 9#5) s <;>
      simp only [ops, smallEqualOps, empty, equal, ↓reduceIte]
    all_goals simp_all (config := {decide := true})
      [Follows, ListSteps.p2048_effect, ListSteps.p2052_effect, ListSteps.p2056_effect,
       ListSteps.p2060_effect, ListSteps.p2064_effect,
       show p2048.offset = 2048 from rfl, show p2052.offset = 2052 from rfl,
       show p2056.offset = 2056 from rfl, show p2060.offset = 2060 from rfl,
       show p2064.offset = 2064 from rfl, show p2068.offset = 2068 from rfl,
       state_simp_rules, BitVec.add_assoc]
  rw [runs ops s base code follows]
  simpa only [smallEqualResult] using small_equal_effect s base _ rfl zero pc


theorem small_equal_frame (s : ArmState) (base : BitVec 64) : Frame s (smallEqualResult s base) := by
  constructor
  · unfold smallEqualResult; split <;> simp [state_simp_rules]
  · unfold smallEqualResult; split <;> simp [state_simp_rules]
  · unfold smallEqualResult; split <;> simp (config := {decide := true}) [state_simp_rules]
  · unfold smallEqualResult; split <;> simp (config := {decide := true}) [state_simp_rules]
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> unfold smallEqualResult <;>
      split <;> simp (config := {decide := true}) [state_simp_rules]
  · intro reg; unfold smallEqualResult; split <;> simp [state_simp_rules]
  · intro address outside; unfold smallEqualResult; split <;> simp [state_simp_rules]

theorem small_equal (s : ArmState) (base word : BitVec 64) (size : Nat)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 2048#64) (physical : size < 2^64)
    (ptr : r (.GPR 8#5) s = 0#64) (payload : r (.GPR 9#5) s = word)
    (actual : r (.GPR 20#5) s = BitVec.ofNat 64 size) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready .list t base (.small word) size := by
  let steps := (smallEqualOps (r (.GPR 20#5) s) (r (.GPR 9#5) s)).length
  let u := smallEqualResult s base
  have hu : run steps s = u := small_equal_run s base code error pc
  have uf : Frame s u := small_equal_frame s base
  by_cases empty : r (.GPR 20#5) s = 0#64
  · have sizeZero : size = 0 := by rw [actual] at empty; bv_omega
    refine ⟨steps, u, hu, uf, ?_⟩
    simp (config := {decide := true}) [Ready, Kind.accepts, u, smallEqualResult,
      empty, sizeZero, state_simp_rules]
  · by_cases equal : r (.GPR 20#5) s = r (.GPR 9#5) s
    · have same : size = word.toNat := by rw [actual, payload] at equal; bv_omega
      have nonzeroCap : r (.GPR 9#5) s ≠ 0#64 := fun zero => empty (equal.trans zero)
      refine ⟨steps, u, hu, uf, ?_⟩
      simp (config := {decide := true}) [Ready, Kind.accepts, NatOperand.value,
        NatOperand.words, SszNative.Limbs.value, u, smallEqualResult,
        equal, nonzeroCap, state_simp_rules, same]
      exact payload
    · have keep (reg : BitVec 5) (ten : reg ≠ 10#5) (twentyOne : reg ≠ 21#5) :
          r (.GPR reg) u = r (.GPR reg) s := by
        simp [u, smallEqualResult, empty, NatExact.r_gpr_w, ten, twentyOne, state_simp_rules]
      obtain ⟨fuel, t, ht, tf, ready⟩ := list_compare u base (.small word) size
        (code.congr uf.program) (uf.error.trans error)
        (by simp [u, smallEqualResult, empty, equal, state_simp_rules]) physical
        ((keep _ (by decide) (by decide)).trans ptr)
        ((keep _ (by decide) (by decide)).trans payload)
        ((keep _ (by decide) (by decide)).trans actual)
        (by simp [u, smallEqualResult, empty, state_simp_rules, payload,
          NatOperand.value, NatOperand.words, SszNative.Limbs.value])
      exact ⟨steps + fuel, t, by rw [run_plus, hu, ht], uf.trans tf, ready⟩

end SszArm.Measure.Scalar.Bytes
