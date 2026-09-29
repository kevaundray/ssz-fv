import SszArm.CodecStorageModels

namespace SszArm.Codec.Storage

open SszNative.CodecMeasure (Plan)
open Delimited (Span Protected)

/- Protection of modeled backings only. It is separate from observations and
can be derived from allocation provenance without constraining any future run. -/
mutual
  def PlanBackingsProtected (writes : List Span) : Plan → Prop
    | .mk size _ children allocation =>
        NatDivision.OperandOwned writes size ∧
          PlansProtected writes (match allocation with | none => 8 | some r => r.pointer) children

  def PlansProtected (writes : List Span) (address : Nat) : List Plan → Prop
    | [] => True
    | child :: rest => Protected writes address 40 ∧ PlanBackingsProtected writes child ∧
        PlansProtected writes (address + 40) rest
end

 theorem word_owned {writes s address size number}
    (input : (Image.word address size number).At s)
    (separated : Protected writes address size) :
    (Image.word address size number).Owned writes s :=
  ⟨input.1, separated, input.2.2⟩

 theorem nat_owned {writes s address number}
    (input : (Image.operand address number).At s)
    (header : Protected writes address 16) (backing : NatDivision.OperandOwned writes number) :
    (Image.operand address number).Owned writes s := by
  refine ⟨input.1, header, ?_, input.2.2.2⟩
  cases number with
  | small word => trivial
  | large pointer words => exact ⟨input.2.2.1.1, backing⟩

mutual
  theorem plan_owned {writes s address} (logical : Plan)
      (input : PlanAt s address logical) (root : Protected writes address 40)
      (backings : PlanBackingsProtected writes logical) : PlanOwned writes s address logical := by
    cases logical with
    | mk size leading children allocation =>
        refine ⟨⟨input.1.1, root⟩,
          word_owned input.2.1 ?_, word_owned input.2.2.1 ?_,
          nat_owned input.2.2.2.1 ?_ backings.1,
          word_owned input.2.2.2.2.1 ?_, input.2.2.2.2.2.1,
          input.2.2.2.2.2.2.1, ?_⟩
        · simpa only [Nat.add_zero] using root.subspan 0 8 (by decide)
        · exact root.subspan 8 8 (by decide)
        · exact root.subspan 16 16 (by decide)
        · exact root.subspan 32 8 (by decide)
        · exact plans_owned children input.2.2.2.2.2.2.2 backings.2

  theorem plans_owned {writes s address} (children : List Plan)
      (input : (planEntries address children).At s)
      (backings : PlansProtected writes address children) :
      (planEntries address children).Owned writes s := by
    cases children with
    | nil => trivial
    | cons child rest =>
        exact ⟨plan_owned child input.1 backings.1 backings.2.1,
          plans_owned rest input.2 backings.2.2⟩
end

end SszArm.Codec.Storage
