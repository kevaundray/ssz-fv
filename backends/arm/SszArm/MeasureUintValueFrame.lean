import SszArm.MeasureUintValueOps

namespace SszArm.Measure.Uint

open UintCodec

def valuePureOps : List ValueOp :=
  [.p348, .p352, .p356, .p360, .p364, .p368, .p404, .p408, .p412, .p2732]

theorem value_pure_frame (base : BitVec 64) (ops : List ValueOp) (s : ArmState)
    (members : ∀ op ∈ ops, op ∈ valuePureOps) : NatNarrow.Frame s (valueBlock base ops s) := by
  induction ops generalizing s with
  | nil => exact NatNarrow.Frame.refl s
  | cons op ops ih =>
    have member := members op List.mem_cons_self
    have frame : NatNarrow.Frame s (op.effect base s) := by
      cases op <;> simp_all only [valuePureOps, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, false_or, or_self]
      all_goals
        constructor
        · exact ValueOp.program _ _ _
        · exact ValueOp.error _ _ _
        · intro reg outside
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
          simp (disch := simp_all) [ValueOp.effect, put, next, compare32,
            Emit.Dispatch.next, Emit.Dispatch.compare32, state_simp_rules]
        · intro reg; exact ValueOp.vector _ _ _ _
        · intro address outside
          simp [ValueOp.effect, put, next, compare32,
            Emit.Dispatch.next, Emit.Dispatch.compare32, state_simp_rules]
    exact frame.trans (ih _ (fun op member => members op (List.mem_cons_of_mem _ member)))

def valueLoadOps : List ValueOp :=
  [.p372, .p376, .p380, .p384, .p388, .p392, .p396, .p400]

def valueLoadResult (s : ArmState) (base limb : BitVec 64) : ArmState :=
  w .PC (base + 404#64) (w (.GPR 11#5) limb (NatCompare.saved s 10#5))

theorem value_load_run (s : ArmState) (base limb : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 372#64)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat)
    (loaded : read_mem_bytes 8 (r (.GPR 9#5) s + (r (.GPR 8#5) s <<< 3))
      (NatCompare.saved s 10#5) = limb) :
    run 8 s = valueLoadResult s base limb := by
  have restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 10#5) = r (.GPR 10#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have pc' : r .PC s = base + 372#64 := pc
  have follows : ValueFollows base valueLoadOps s := by
    simp [valueLoadOps, ValueFollows, ValueOp.row, ValueOp.effect, put, next,
      Emit.Dispatch.next, state_simp_rules, pc', BitVec.add_assoc]
  rw [show 8 = valueLoadOps.length by rfl, value_run base valueLoadOps s code error aligned follows]
  simp only [NatCompare.saved] at loaded restore
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases destination : reg = 11#5 <;> by_cases temporary : reg = 10#5 <;>
        by_cases stack : reg = 31#5 <;> (try subst reg) <;>
        simp_all (config := {decide := true, instances := true})
          [valueLoadResult, valueLoadOps, valueBlock, ValueOp.effect, put, next,
            Emit.Dispatch.next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w,
            BitVec.sub_add_cancel, BitVec.add_assoc]
    | PC =>
      simp_all (config := {decide := true, instances := true})
        [valueLoadResult, valueLoadOps, valueBlock, ValueOp.effect, put, next,
          Emit.Dispatch.next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w,
          BitVec.sub_add_cancel, BitVec.add_assoc]
    | SFP reg => simp [valueLoadResult, valueLoadOps, valueBlock, ValueOp.effect,
        put, next, Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
    | FLAG flag => simp [valueLoadResult, valueLoadOps, valueBlock, ValueOp.effect,
        put, next, Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
    | ERR => simp [valueLoadResult, valueLoadOps, valueBlock, ValueOp.effect,
        put, next, Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
  · simp [valueLoadResult, valueLoadOps, valueBlock, ValueOp.effect, put, next,
      Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
  · intro count address
    simp [valueLoadResult, valueLoadOps, valueBlock, ValueOp.effect, put, next,
      Emit.Dispatch.next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w]

theorem value_load_frame (s : ArmState) (base limb : BitVec 64)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat) :
    NatNarrow.Frame s (valueLoadResult s base limb) := by
  have frame := NatNarrow.saved_frame s 10#5 safe
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [valueLoadResult, state_simp_rules] using frame.program
  · simpa [valueLoadResult, state_simp_rules] using frame.error
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [valueLoadResult, NatCompare.saved, state_simp_rules]
  · intro reg; simpa [valueLoadResult, state_simp_rules] using frame.vectors reg
  · intro address outside
    simpa [valueLoadResult, state_simp_rules] using frame.memory address outside

end SszArm.Measure.Uint
