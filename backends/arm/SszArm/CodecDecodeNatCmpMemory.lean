import SszArm.CodecDecodeNatCmpOps

namespace SszArm.Codec.Decode.NatCmpUsize

theorem frame_code {s t : ArmState} (frame : NatNarrow.Frame s t) {base : BitVec 64}
    (code : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, Linked.NatCmpUsize.CodeAt, Linked.WordsAt, frame.program] using code

/-- Only register/flag instructions belong to this scan phase. The limb load's
real spill is accounted for separately by `NatNarrow.saved_frame`. -/
def scanPureOps : List Op := [.p0, .p4, .p8, .p12, .p48, .p52, .p56, .p60, .p64, .p68,
  .p80, .p104, .p108, .p112]

theorem scan_pure_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (members : ∀ op ∈ ops, op ∈ scanPureOps) : NatNarrow.Frame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact NatNarrow.Frame.refl s
  | cons op ops ih =>
    have member := members op List.mem_cons_self
    have frame : NatNarrow.Frame s (op.effect base s) := by
      cases op <;> simp_all only [scanPureOps, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, false_or, or_self]
      all_goals
        constructor
        · exact Op.program _ _ _
        · exact Op.error _ _ _
        · intro reg outside
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
          simp (disch := simp_all) [Op.effect, put, next, Udivti3.compare,
            Udivti3.next, state_simp_rules]
        · intro reg; exact Op.sfp _ _ _ _
        · intro address outside
          simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
    exact frame.trans (ih _ (fun op member => members op (List.mem_cons_of_mem _ member)))

end SszArm.Codec.Decode.NatCmpUsize
