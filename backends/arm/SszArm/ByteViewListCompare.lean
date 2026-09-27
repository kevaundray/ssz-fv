import SszArm.ByteViewListBlocks

namespace SszArm.ByteView.Bounded

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def different (a b : BitVec 64) : Bool :=
  decide ((a = 0#64 ∧ b ≠ 0#64) ∨ (a ≠ 0#64 ∧ b = 0#64))

def rejectZero (a b : BitVec 64) : Bool := decide (a ≠ 0#64 ∧ b = 0#64)

def classifyOps (a b : BitVec 64) : List Op :=
  [.p2596, .p2600] ++ (if a = 0#64 then [.p2604, .p2608] else [.p2612]) ++
  [.p2616, .p2620] ++ (if b = 0#64 then [.p2624, .p2628] else [.p2632]) ++ [.p2636, .p2640]

/-- The native zero/nonzero classification ends before the lowering spill. -/
theorem classify (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (hp : read_pc s = base + 2596#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s) :
    ∃ fuel t, run fuel s = t ∧ WidthFrame s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      r (.GPR 10#5) t = (if rejectZero (r (.GPR 3#5) s) (r (.GPR 9#5) s) then 1#64 else 0#64) ∧
      r (.GPR 11#5) t = (if different (r (.GPR 3#5) s) (r (.GPR 9#5) s) then 1#64 else 0#64) ∧
      read_pc t = base + 2644#64 := by
  let ops := classifyOps (r (.GPR 3#5) s) (r (.GPR 9#5) s)
  let t := block base ops s
  have hpc : r .PC s = base + 2596#64 := hp
  have hfollow : Follows base ops s := by
    by_cases hx : r (.GPR 3#5) s = 0#64 <;> by_cases hy : r (.GPR 9#5) s = 0#64 <;>
      simp (config := {decide := true, instances := true})
        [ops, classifyOps, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
         Udivti3.next, state_simp_rules, BitVec.ofNat_eq_ofNat, hpc, hx, hy, BitVec.add_assoc]
  refine ⟨ops.length, t, block_run base ops s hc he ha hfollow,
    readonly_frame base ops s ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [ops, classifyOps]; split <;> split <;> decide
  all_goals
    by_cases hx : r (.GPR 3#5) s = 0#64 <;> by_cases hy : r (.GPR 9#5) s = 0#64 <;>
      simp (config := {decide := true, instances := true})
        [t, ops, classifyOps, different, rejectZero, block, Op.effect, put, next,
         Udivti3.compare, Udivti3.next, state_simp_rules, BitVec.ofNat_eq_ofNat,
         hpc, hx, hy, BitVec.add_assoc]

theorem ls_condition (a b : BitVec 64) :
    (¬ b.toNat ≤ a.toNat ∨ a = b) ↔ a.toNat ≤ b.toNat := by
  have h : a = b ↔ a.toNat = b.toNat := ⟨congrArg BitVec.toNat, BitVec.eq_of_toNat_eq⟩
  rw [h]
  omega

def compareOps (a b : BitVec 64) : List Op :=
  [.p3524, .p3528] ++ if a.toNat ≤ b.toNat then [] else [.p3532]

def plainOps (a b : BitVec 64) : List Op :=
  [.p2684] ++ if a = 0#64 then [] else
    [.p2688, .p2692, .p2696] ++ if a = b then [.p2700] else compareOps a b

/-- Read-only machine-word comparison after equal significant lengths. -/
theorem plain_compare (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (hp : read_pc s = base + 2684#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s) :
    ∃ fuel t, run fuel s = t ∧ WidthFrame s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      read_pc t = if (r (.GPR 3#5) s).toNat ≤ (r (.GPR 9#5) s).toNat
        then base + 4492#64 else base + 3576#64 := by
  let ops := plainOps (r (.GPR 3#5) s) (r (.GPR 9#5) s)
  let t := block base ops s
  have hpc : r .PC s = base + 2684#64 := hp
  have hfollow : Follows base ops s := by
    by_cases hz : r (.GPR 3#5) s = 0#64 <;>
      by_cases heq : r (.GPR 3#5) s = r (.GPR 9#5) s <;>
      by_cases hle : (r (.GPR 3#5) s).toNat ≤ (r (.GPR 9#5) s).toNat <;>
      (try simp only [heq] at hz hle) <;>
      (try omega) <;>
      simp (config := {decide := true, instances := true})
        [ops, plainOps, compareOps, Follows, Op.row, Op.effect, put, next,
         Udivti3.compare, Udivti3.next, state_simp_rules, BitVec.ofNat_eq_ofNat,
         Udivti3.cmp_zero, Udivti3.cmp_carry, ls_condition, hpc, hz, heq, hle, BitVec.add_assoc] <;>
      bv_omega
  refine ⟨ops.length, t, block_run base ops s hc he ha hfollow,
    readonly_frame base ops s ?_, ?_, ?_, ?_⟩
  · dsimp only [ops, plainOps, compareOps]; split <;> (try split) <;> (try split) <;> decide
  all_goals
    by_cases hz : r (.GPR 3#5) s = 0#64 <;>
      by_cases heq : r (.GPR 3#5) s = r (.GPR 9#5) s <;>
      by_cases hle : (r (.GPR 3#5) s).toNat ≤ (r (.GPR 9#5) s).toNat
    all_goals try simp only [heq] at hz hle
    all_goals try omega
    all_goals
      simp (config := {decide := true, instances := true})
        [t, ops, plainOps, compareOps, block, Op.effect, put, next,
         Udivti3.compare, Udivti3.next, state_simp_rules, BitVec.ofNat_eq_ofNat,
         Udivti3.cmp_zero, Udivti3.cmp_carry, ls_condition, hpc, hz, heq, hle, BitVec.add_assoc]
      try bv_omega

/-- Compose opaque classification, spill and comparison certificates. -/
theorem small_compare (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (hp : read_pc s = base + 2596#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    ∃ fuel t, run fuel s = t ∧ WidthFrame s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      read_pc t = if (r (.GPR 3#5) s).toNat ≤ (r (.GPR 9#5) s).toNat
        then base + 4492#64 else base + 3576#64 := by
  obtain ⟨fuel, t, ht, hf, ht8, ht9, ht10, ht11, htp⟩ := classify s base hc hp he ha
  let d := different (r (.GPR 3#5) s) (r (.GPR 9#5) s)
  let reject := rejectZero (r (.GPR 3#5) s) (r (.GPR 9#5) s)
  let u := spillResult t base true d
  have hsp : r (.GPR 31#5) t = r (.GPR 31#5) s := hf.sp
  have hts : 16 ≤ (r (.GPR 31#5) t).toNat := by simpa only [hsp] using hs
  have hu : run 7 t = u := spill_run t base true d
    (by simpa only [CodeAt, hf.program] using hc) (hf.error.trans he) (hf.aligned ha)
    htp hts ht11
  have huf : WidthFrame s u := hf.trans (spill_frame t base true d hts)
  have hu8 : r (.GPR 8#5) u = r (.GPR 8#5) s := (spill_register t base true d 8#5).trans ht8
  have hu9 : r (.GPR 9#5) u = r (.GPR 9#5) s := (spill_register t base true d 9#5).trans ht9
  have hu10 : r (.GPR 10#5) u = if reject then 1#64 else 0#64 :=
    (spill_register t base true d 10#5).trans ht10
  have hvs : run (fuel + 7) s = u := by rw [run_plus, ht, hu]
  by_cases hd : d = true
  · let v := spillResult u base false reject
    have hup : read_pc u = base + 3536#64 := by simp [u, spillTarget, hd]
    have hus : 16 ≤ (r (.GPR 31#5) u).toNat := by
      have hsp' : r (.GPR 31#5) u = r (.GPR 31#5) s := huf.sp
      simpa only [hsp'] using hs
    have hv : run 7 u = v := spill_run u base false reject
      (by simpa only [CodeAt, huf.program] using hc) (huf.error.trans he) (huf.aligned ha)
      hup hus hu10
    refine ⟨fuel + 7 + 7, v, by rw [run_plus, hvs, hv],
      huf.trans (spill_frame u base false reject hus), ?_, ?_, ?_⟩
    · exact (spill_register u base false reject 8#5).trans hu8
    · exact (spill_register u base false reject 9#5).trans hu9
    · simp only [v, spill_pc, spillTarget, Bool.false_eq_true, ↓reduceIte]
      by_cases hx : r (.GPR 3#5) s = 0#64 <;> by_cases hy : r (.GPR 9#5) s = 0#64
      all_goals simp [d, different, reject, rejectZero, hx, hy] at hd ⊢
      all_goals bv_omega
  · have hup : read_pc u = base + 2684#64 := by simp [u, spillTarget, hd]
    obtain ⟨extra, v, hv, hvf, hv8, hv9, hvp⟩ := plain_compare u base
      (by simpa only [CodeAt, huf.program] using hc) hup (huf.error.trans he) (huf.aligned ha)
    refine ⟨fuel + 7 + extra, v, by rw [run_plus, hvs, hv], huf.trans hvf,
      hv8.trans hu8, hv9.trans hu9, ?_⟩
    have hu3 : r (.GPR 3#5) u = r (.GPR 3#5) s := huf.registers 3#5 (by decide)
    simpa only [hu3, hu9] using hvp

end SszArm.ByteView.Bounded
