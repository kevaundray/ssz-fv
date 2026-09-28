import SszX86.MeasureFinish

namespace SszX86.Measure
open SszNative SszNative.Serialize BoolCodec

def boolTested (s : MachineData) (af : Bool) : MachineData :=
  {s with status :=
    StatusFlags.from_result (s.regs.rax.toBitVec.setWidth 8) {cf := false, af, of := false}}

theorem bool_type_branch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ af, Eventually (step e) P
      (boolTested s af, if s.regs.rax.toBitVec.setWidth 8 == 0#8 then base + 54 else base + 3265)) :
    Eventually (step e) P (s, base + 46) := by
  have target := hc.targets ("measure_u3265", 3265) (by decide)
  have branch (af : Bool) : Eventually (step e) P (boolTested s af, base + 48) := by
    have hnext := next af
    measure_step 16 using hc
    simp only [target]
    split <;> rename_i condition
    all_goals simp_all (config := {instances := true})
      [boolTested, StatusFlags.from_result, Effects.All]
  measure_step 15 using hc
  exact ⟨branch false, branch true⟩

theorem bool_size_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P ({s with regs := {s.regs with rax := 1}}, base + 3050)) :
    Eventually (step e) P (s, base + 54) := by
  measure_step 17 using hc
  measure_step 18 using hc
  exact next

/-- Both Bool success values and all five wrong-type constructors execute from
the genuine table destination, through the common publication to the epilogue. -/
theorem bool_body_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : Value) (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s .bool value buffer address capacity used) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧ BodyPost s .bool value buffer address capacity used t.1)
      (s, base + 46) := by
  apply bool_type_branch e base hc s
  intro af
  have tag := owned.tag
  cases value with
  | bool boolean =>
    have zero : s.regs.rax.toBitVec.setWidth 8 = 0#8 := by
      simpa only [valueTag, Emit.valueTag] using tag
    simp only [zero, beq_self_eq_true, ↓reduceIte]
    apply bool_size_cps e base hc
    apply small_success_body_cps e base hc s _ .bool (.bool boolean)
      buffer address capacity used 1
    all_goals first | exact owned | rfl
  | uint number | bytes data | bits data | seq data | union selector data =>
    have nonzero : s.regs.rax.toBitVec.setWidth 8 ≠ 0#8 := by
      rw [tag]
      dsimp only [valueTag, Emit.valueTag]
      decide
    simp only [nonzero, beq_iff_eq, ↓reduceIte]
    apply wrong_type_body_cps e base hc s _ .bool _ buffer address capacity used
    all_goals first | exact owned | rfl

end SszX86.Measure
