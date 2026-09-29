import SszCodecMeasureLogic
import SszCodecMeasureExpected

set_option autoImplicit false

namespace SszNative.CodecMeasure

open Codec (Desc Value Error)

def partialSize (totals : Partial) : Nat × Nat :=
  (totals.leading.value, totals.bodies.value)

theorem accumulate_refines (inline : Bool) (child : Plan) (totals : Partial)
    (arena : Delimited.ArenaState) :
    Refines partialSize (accumulate inline child totals arena).result
      (.ok (totals.leading.value + (if inline then child.size.value else 4),
        if inline then totals.bodies.value else totals.bodies.value + child.size.value)) := by
  cases inline with
  | false =>
    unfold accumulate
    simp only [Bool.false_eq_true, ↓reduceIte]
    have first := add_refines totals.leading (.small 4) arena
    change Refines NatOperand.value _ (.ok (totals.leading.value + 4)) at first
    apply refines_bind NatOperand.value partialSize _ _ _
      (fun leading => .ok (leading, totals.bodies.value + child.size.value)) first
    intro leading used
    apply refines_bind NatOperand.value partialSize _ _ _
      (fun bodies => .ok (leading.value, bodies))
      (add_refines totals.bodies child.size { arena with used := used })
    intro bodies used
    exact Or.inl rfl
  | true =>
    unfold accumulate
    simp only [↓reduceIte]
    apply refines_bind NatOperand.value partialSize _ _ _
      (fun leading => .ok (leading, totals.bodies.value))
      (add_refines totals.leading child.size arena)
    intro leading used
    exact Or.inl rfl

/-- Union arithmetic precedes retention, and the retention decision depends on
actual retained descendants rather than merely on the child's variable type. -/
theorem unionPlan_refines (child : Plan) (arena : Delimited.ArenaState) (retain : Bool) :
    Refines (fun plan => plan.size.value) (unionPlan child arena retain).result
      (.ok (child.size.value + 1)) := by
  unfold unionPlan
  have first := add_refines child.size (.small 1) arena
  change Refines NatOperand.value _ (.ok (child.size.value + 1)) at first
  apply refines_bind NatOperand.value (fun (plan : Plan) => plan.size.value) _ _ _
    (fun size => .ok size) first
  intro size used
  split
  · apply refines_bind (fun _ => ()) (fun (plan : Plan) => plan.size.value) _ _ _
      (fun _ => .ok size.value) (reservePlans_refines 1 { arena with used := used })
    intro allocation used
    apply refines_bind (fun _ => ()) (fun (plan : Plan) => plan.size.value) _ _ _
      (fun _ => .ok size.value) (writePlan_refines (some allocation) 0 child used)
    intro _ used
    exact Or.inl rfl
  · exact Or.inl rfl

end SszNative.CodecMeasure
