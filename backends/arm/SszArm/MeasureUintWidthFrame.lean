import SszArm.MeasureUintWidthOps

namespace SszArm.Measure.Uint

open UintCodec

def widthPureOps : List WidthOp :=
  [.p2740, .p2744, .p2748, .p2752, .p2788, .p2792, .p2796, .p2800,
   .p2804, .p2808, .p2812, .p2816, .p2820, .p2824, .p2876, .p2880, .p2884,
   .p2888, .p2892, .p2896, .p3012, .p3016, .p3904, .p3908, .p3912, .p3916, .p3920]

theorem width_pure_frame (base : BitVec 64) (ops : List WidthOp) (s : ArmState)
    (members : ∀ op ∈ ops, op ∈ widthPureOps) : NatNarrow.Frame s (widthBlock base ops s) := by
  induction ops generalizing s with
  | nil => exact NatNarrow.Frame.refl s
  | cons op ops ih =>
    have member := members op List.mem_cons_self
    have frame : NatNarrow.Frame s (op.effect base s) := by
      cases op <;> simp_all only [widthPureOps, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, false_or, or_self]
      all_goals
        constructor
        · exact WidthOp.program _ _ _
        · exact WidthOp.error _ _ _
        · intro reg outside
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
          simp (disch := simp_all) [WidthOp.effect, put, next, compare64,
            Emit.Dispatch.next, Emit.Dispatch.compare64, state_simp_rules]
        · intro reg; exact WidthOp.vector _ _ _ _
        · intro address outside
          simp [WidthOp.effect, put, next, compare64,
            Emit.Dispatch.next, Emit.Dispatch.compare64, state_simp_rules]
    exact frame.trans (ih _ (fun op member => members op (List.mem_cons_of_mem _ member)))

def widthLoadOps : List WidthOp :=
  [.p2756, .p2760, .p2764, .p2768, .p2772, .p2776, .p2780, .p2784]

def widthLoadResult (s : ArmState) (base limb : BitVec 64) : ArmState :=
  w .PC (base + 2788#64) (w (.GPR 12#5) limb (NatCompare.saved s 9#5))

theorem width_load_run (s : ArmState) (base limb : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2756#64)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat)
    (loaded : read_mem_bytes 8 (r (.GPR 21#5) s + (r (.GPR 11#5) s <<< 3))
      (NatCompare.saved s 9#5) = limb) :
    run 8 s = widthLoadResult s base limb := by
  have restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 9#5) = r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have pc' : r .PC s = base + 2756#64 := pc
  have follows : WidthFollows base widthLoadOps s := by
    simp [widthLoadOps, WidthFollows, WidthOp.row, WidthOp.effect, put, next,
      Emit.Dispatch.next, state_simp_rules, pc', BitVec.add_assoc]
  rw [show 8 = widthLoadOps.length by rfl, width_run base widthLoadOps s code error aligned follows]
  simp only [NatCompare.saved] at loaded restore
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases destination : reg = 12#5 <;> by_cases temporary : reg = 9#5 <;>
        by_cases stack : reg = 31#5 <;> (try subst reg) <;>
        simp_all (config := {decide := true, instances := true})
          [widthLoadResult, widthLoadOps, widthBlock, WidthOp.effect, put, next,
            Emit.Dispatch.next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w,
            BitVec.sub_add_cancel, BitVec.add_assoc]
    | PC =>
      simp_all (config := {decide := true, instances := true})
        [widthLoadResult, widthLoadOps, widthBlock, WidthOp.effect, put, next,
          Emit.Dispatch.next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w,
          BitVec.sub_add_cancel, BitVec.add_assoc]
    | SFP reg => simp [widthLoadResult, widthLoadOps, widthBlock, WidthOp.effect,
        put, next, Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
    | FLAG flag => simp [widthLoadResult, widthLoadOps, widthBlock, WidthOp.effect,
        put, next, Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
    | ERR => simp [widthLoadResult, widthLoadOps, widthBlock, WidthOp.effect,
        put, next, Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
  · simp [widthLoadResult, widthLoadOps, widthBlock, WidthOp.effect, put, next,
      Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
  · intro count address
    simp [widthLoadResult, widthLoadOps, widthBlock, WidthOp.effect, put, next,
      Emit.Dispatch.next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w]

theorem width_load_frame (s : ArmState) (base limb : BitVec 64)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat) :
    NatNarrow.Frame s (widthLoadResult s base limb) := by
  have frame := NatNarrow.saved_frame s 9#5 safe
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [widthLoadResult, state_simp_rules] using frame.program
  · simpa [widthLoadResult, state_simp_rules] using frame.error
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [widthLoadResult, NatCompare.saved, state_simp_rules]
  · intro reg; simpa [widthLoadResult, state_simp_rules] using frame.vectors reg
  · intro address outside
    simpa [widthLoadResult, state_simp_rules] using frame.memory address outside

end SszArm.Measure.Uint
