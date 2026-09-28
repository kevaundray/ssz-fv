import SszArm.SerializeContract

namespace SszArm.Serialize

open Delimited (Span Protected MemoryFrame)

/-- Byte containment is enough when a callee's precise store span is smaller
than an original caller-owned region. -/
def Covers (small large : List Span) : Prop :=
  ∀ span ∈ small, ∃ outer ∈ large,
    outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2

theorem Covers.refl (spans : List Span) : Covers spans spans := by
  intro span member
  exact ⟨span, member, Nat.le_refl _, Nat.le_refl _⟩

theorem Covers.trans {first second third : List Span}
    (left : Covers first second) (right : Covers second third) : Covers first third := by
  intro span member
  obtain ⟨middle, middleMember, lower, upper⟩ := left span member
  obtain ⟨outer, outerMember, outerLower, outerUpper⟩ := right middle middleMember
  exact ⟨outer, outerMember, Nat.le_trans outerLower lower, Nat.le_trans upper outerUpper⟩

theorem protected_of_covers {small large : List Span} {address bytes : Nat}
    (owned : Protected large address bytes) (covered : Covers small large) :
    Protected small address bytes := by
  rcases owned with empty | separate
  · exact Or.inl empty
  · right
    intro span member
    obtain ⟨outer, outerMember, lower, upper⟩ := covered span member
    rcases separate outer outerMember with before | after
    · left; omega
    · right; omega

theorem frame_of_covers {small large : List Span} {s t : ArmState}
    (frame : MemoryFrame small s t) (covered : Covers small large) :
    MemoryFrame large s t := by
  intro address outside
  apply frame address
  intro span member
  obtain ⟨outer, outerMember, lower, upper⟩ := covered span member
  rcases outside outer outerMember with before | after
  · left; omega
  · right; omega

theorem operand_owned_of_covers {small large : List Span}
    (covered : Covers small large) (operand : SszNative.NatOperand)
    (owned : NatDivision.OperandOwned large operand) : NatDivision.OperandOwned small operand := by
  cases operand with
  | small scalar => trivial
  | large pointer limbs => exact protected_of_covers owned covered

theorem bodySP_toNat (args : Args) (low : 144 ≤ args.stack.toNat) :
    args.bodySP.toNat = args.stack.toNat - 144 := by
  unfold Args.bodySP
  bv_omega

theorem plan_toNat (args : Args) (low : 144 ≤ args.stack.toNat) :
    args.plan.toNat = args.stack.toNat - 120 := by
  have bound := args.stack.isLt
  unfold Args.plan Args.bodySP
  bv_omega

theorem save_covered (args : Args) : Covers (saveWrites args) (stackSpans args) := by
  intro span member
  simp only [saveWrites, List.mem_singleton] at member
  subst span
  exact ⟨_, by simp [stackSpans], Nat.le_refl _, Nat.le_refl _⟩

theorem resultExtent_le (first : SszNative.Serialize.Outcome SszNative.NatOperand) :
    Measure.resultExtent first ≤ 72 := by
  unfold Measure.resultExtent
  split <;> decide

end SszArm.Serialize
