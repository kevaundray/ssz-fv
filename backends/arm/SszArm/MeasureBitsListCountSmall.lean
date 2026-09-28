import SszArm.MeasureBitsListCountModel

namespace SszArm.Measure.Bits.List

open SszNative.Serialize (Packed)

theorem count_small_executes (schema : Schema) (s : ArmState) (args : Args) (bits : Packed)
    (base : BitVec 64) (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 schema.kind.smallEntry)
    (work : Work s args schema bits)
    (high : (bits.count >>> (64 : Nat)).setWidth 64 = 0#64) :
    ∃ t, run (ListEntry.smallOps schema.kind).length s = t ∧
      CountPost s t args schema bits base (.small (bits.count.setWidth 64)) := by
  let t := ListEntry.small schema.kind s base
  have state : t =
      w .PC (base + (match schema.kind with | .bounded => 1712#64 | .progressive => 716#64))
        (w (.GPR 24#5) (r (.GPR 26#5) s) (w (.GPR 21#5) 0#64 s)) := by
    cases kind : schema.kind <;> simp [t, kind, ListEntry.small]
  have model := count_call_small s args bits high
  refine ⟨t, ListEntry.small_run schema.kind s base code error pc,
    by simp only [model, SszNative.NatArithmetic.unchanged], ?_, ?_, ?_, ?_, ?_, ?_,
    trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases schema <;> simp [state, Schema.kind, Schema.countExit, state_simp_rules, high]
  · simp [state, state_simp_rules]
  · simp [state, state_simp_rules]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [state, state_simp_rules] using work.result
    · simpa [state, state_simp_rules] using work.arena
    · simpa [state, state_simp_rules] using work.stack
    · simpa [state, state_simp_rules] using work.low
    · simpa [state, state_simp_rules] using work.high
    · cases cap : schema.cap with
      | none => trivial
      | some operand => simpa [cap, state, state_simp_rules] using work.cap
    · cases schema with
      | bounded cap => trivial
      | progressive cap => simpa [state, state_simp_rules] using work.flag
  · simp [state, state_simp_rules, SszNative.NatOperand.pointer]
  · simpa [state, state_simp_rules, SszNative.NatOperand.payload] using work.low
  · simp [state, state_simp_rules, model, SszNative.NatArithmetic.unchanged, arenaOf]
  · constructor <;> simp [state, state_simp_rules]
  · simp [NatDivision.WrittenAt, model, SszNative.NatArithmetic.unchanged]
  · intro address outside
    simp [state, state_simp_rules]
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp [state, state_simp_rules]
  · intro reg
    simp [state, state_simp_rules]

end SszArm.Measure.Bits.List
