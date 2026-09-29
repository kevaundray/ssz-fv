import SszArm.CodecMeasureProvenanceResult

namespace SszArm.Codec.Measure.Provenance

open SszNative (NatOperand)
open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure
open Delimited (Span Protected)

 structure PartialOwned (writes : List Span) (totals : Partial) : Prop where
  leading : NatDivision.OperandOwned writes totals.leading
  bodies : NatDivision.OperandOwned writes totals.bodies
  children : ∀ child ∈ totals.children, Storage.PlanBackingsProtected writes child

 theorem initial_owned (writes : List Span) : PartialOwned writes initial :=
  ⟨True.intro, True.intro, by simp [initial]⟩

 theorem plan_size_owned {writes logical} (input : Storage.PlanBackingsProtected writes logical) :
    NatDivision.OperandOwned writes logical.size := by
  cases logical
  exact input.1

 theorem partial_retain {writes totals child} (keep : Bool)
    (input : PartialOwned writes totals) (stored : Storage.PlanBackingsProtected writes child) :
    PartialOwned writes { totals with children := if keep then totals.children ++ [child] else totals.children } := by
  refine ⟨input.leading, input.bodies, ?_⟩
  cases keep with
  | false => exact input.children
  | true =>
      intro entry member
      rcases List.mem_append.mp member with old | new
      · exact input.children entry old
      · simp only [List.mem_singleton] at new
        subst entry
        exact stored

 theorem plans_protected {writes : List Span} (children : List Plan) (address : Nat)
    (records : Protected writes address (40 * children.length))
    (backings : ∀ child ∈ children, Storage.PlanBackingsProtected writes child) :
    Storage.PlansProtected writes address children := by
  induction children generalizing address with
  | nil => trivial
  | cons child rest ih =>
      refine ⟨?_, backings child (by simp), ?_⟩
      · simpa only [Nat.add_zero] using records.subspan 0 40 (by simp only [List.length_cons]; omega)
      · apply ih
        · exact records.subspan 40 (40 * rest.length) (by simp only [List.length_cons]; omega)
        · intro other member
          exact backings other (List.mem_cons_of_mem _ member)

 theorem accumulate_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (inline : Bool) (child : Plan) (totals : Partial)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (stored : Storage.PlanBackingsProtected writes child) (input : PartialOwned writes totals) :
    ResultOwned writes (PartialOwned writes) (accumulate inline child totals arena).result := by
  unfold accumulate
  apply bind_owned (NatDivision.OperandOwned writes)
  · apply add_owned writes arena _ _ storage free input.leading
    cases inline with
    | false => trivial
    | true => exact plan_size_owned stored
  · intro leading leadingOwned
    have nextFree := Serialize.free_protected_after arena free _
      (add_cursorSafe totals.leading (if inline then child.size else .small 4) arena).1
    cases inline with
    | true => exact ⟨leadingOwned, input.bodies, input.children⟩
    | false =>
        apply bind_owned (NatDivision.OperandOwned writes)
        · exact add_owned writes _ totals.bodies child.size storage nextFree input.bodies (plan_size_owned stored)
        · intro bodies bodiesOwned
          exact ⟨leadingOwned, bodiesOwned, input.children⟩

 theorem finishParts_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (parts : Parts) (values : List Value) (totals : Partial)
    (allocation : Option SszNative.Arena.Reservation)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (input : PartialOwned writes totals)
    (records : Protected writes (match allocation with | none => 8 | some r => r.pointer)
      (40 * totals.children.length)) :
    ResultOwned writes (Storage.PlanBackingsProtected writes)
      (finishParts parts values totals allocation arena).result := by
  unfold finishParts
  split
  · apply bind_owned (NatDivision.OperandOwned writes)
    · exact add_owned writes arena totals.leading totals.bodies storage free input.leading input.bodies
    · intro size sizeOwned
      apply bind_owned (fun _ => True)
      · exact compositeSize_owned writes size _ sizeOwned
      · intro _ _
        apply bind_owned (fun _ => True)
        · exact hostSize_owned writes totals.leading _
        · intro leading _
          exact ⟨sizeOwned, plans_protected totals.children _ records input.children⟩
  · exact ⟨True.intro, True.intro⟩

 theorem unionPlan_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (child : Plan) (retain : Bool) (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (stored : Storage.PlanBackingsProtected writes child) :
    ResultOwned writes (Storage.PlanBackingsProtected writes) (unionPlan child arena retain).result := by
  unfold unionPlan
  apply bind_owned (NatDivision.OperandOwned writes)
  · exact add_owned writes arena child.size (.small 1) storage free (plan_size_owned stored) True.intro
  · intro size sizeOwned
    have nextFree := Serialize.free_protected_after arena free _ (add_cursorSafe child.size (.small 1) arena).1
    split
    · apply bind_owned (fun r => Protected writes r.pointer (40 * 1))
      · exact reservePlans_owned writes _ 1 nextFree
      · intro allocation allocated
        simp only [writePlan, bind, unchanged]
        exact ⟨sizeOwned, allocated, stored, True.intro⟩
    · exact ⟨sizeOwned, True.intro⟩

end SszArm.Codec.Measure.Provenance
