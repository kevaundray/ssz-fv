import SszX86.CodecStorage

set_option autoImplicit false

namespace SszX86.Codec
open SszNative UintCodec

mutual
  /-- The concrete recursive Plan read footprint, independent of any larger
  ambient readonly region used to construct its storage proof. -/
  def planFootprint (p : BitVec 64) : CodecMeasure.Plan → Footprint
    | .mk size _ children allocation => fun a =>
        InSpan a p 40 ∨ Emit.NatBorrowed size a ∨
          plansFootprint (BitVec.ofNat 64 (match allocation with
            | none => 8
            | some reservation => reservation.pointer)) children a

  def plansFootprint (p : BitVec 64) : List CodecMeasure.Plan → Footprint
    | [] => fun _ => False
    | plan :: plans => fun a => planFootprint p plan a ∨ plansFootprint (p + 40) plans a
end

/-- Excludes only the outer Plan header. Nested headers and all borrowed Nat
limbs remain protected, even when they alias one another. -/
def planBorrowed (plan : CodecMeasure.Plan) : Footprint := fun a =>
  Emit.NatBorrowed plan.size a ∨
    plansFootprint (BitVec.ofNat 64 plan.childrenPointer) plan.children a

/-- Exactly the five active Plan fields. This is a post-write memory equality,
not a promised helper execution or a successful measurement premise. -/
structure PlanRootSame (before after : DataMem) (p : BitVec 64) : Prop where
  pointer : Mem.loadInt after p 8 = Mem.loadInt before p 8
  length : Mem.loadInt after (p + 8) 8 = Mem.loadInt before (p + 8) 8
  sizePointer : widthLoad after (p + 16).toNat 8 = widthLoad before (p + 16).toNat 8
  sizePayload : widthLoad after ((p + 16).toNat + 8) 8 =
    widthLoad before ((p + 16).toNat + 8) 8
  leading : Mem.loadInt after (p + 32) 8 = Mem.loadInt before (p + 32) 8

private theorem plan_window_same {m n : DataMem} {w : Footprint} {p : BitVec 64}
    (frame : MemoryFrame m n w) (safe : ∀ a, InSpan a p 40 → ¬ w a)
    (off bytes : Nat) (bound : off + bytes ≤ 40) :
    Mem.loadInt n (p + BitVec.ofNat 64 off) bytes =
      Mem.loadInt m (p + BitVec.ofNat 64 off) bytes := by
  apply Emit.frame_load m n w frame
  intro i hi
  exact safe _ (Emit.span_shift p off bytes 40 bound ⟨i, hi, rfl⟩)

theorem PlanRootSame.of_frame {m n : DataMem} {w : Footprint} {p : BitVec 64}
    (frame : MemoryFrame m n w) (safe : ∀ a, InSpan a p 40 → ¬ w a) :
    PlanRootSame m n p := by
  refine ⟨?_, plan_window_same frame safe 8 8 (by decide), ?_, ?_,
    plan_window_same frame safe 32 8 (by decide)⟩
  · simpa only [BitVec.add_zero] using plan_window_same frame safe 0 8 (by decide)
  · unfold widthLoad
    simp only [BitVec.ofNat_toNat]
    rw [plan_window_same frame safe 16 8 (by decide)]
  · unfold widthLoad
    rw [width_address]
    have pointer : p + 16 + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 24 := by bv_omega
    rw [pointer, plan_window_same frame safe 24 8 (by decide)]

/-- Operand limbs can be transported independently of the two-word Nat header. -/
theorem operand_frame {m n : DataMem} {w : Footprint} (operand : NatOperand)
    (stored : operand.At (widthLoad m)) (frame : MemoryFrame m n w)
    (safe : ∀ a, Emit.NatBorrowed operand a → ¬ w a) : operand.At (widthLoad n) := by
  cases operand with
  | small word => trivial
  | large pointer words =>
    obtain ⟨positive, aligned, bound, observations⟩ := stored
    refine ⟨positive, aligned, bound, ?_⟩
    intro i
    have same : widthLoad n (pointer.toNat + 8 * i.val) 8 =
        widthLoad m (pointer.toNat + 8 * i.val) 8 := by
      unfold widthLoad
      rw [width_address]
      congr 1
      apply Emit.frame_load m n w frame
      intro j hj
      exact safe _ (Emit.span_shift pointer (8 * i.val) 8 (8 * words.length)
        (by have := i.isLt; omega) ⟨j, hj, rfl⟩)
    rw [same]
    exact observations i

private theorem plan_fields_transport {m n : DataMem} {r w : Footprint} {p : BitVec 64}
    {plan : CodecMeasure.Plan} (h : PlanAt m r p plan) (root : PlanRootSame m n p)
    (frame : MemoryFrame m n w)
    (limbs : ∀ a, Emit.NatBorrowed plan.size a → ¬ w a)
    (children : PlansAt n r (BitVec.ofNat 64 plan.childrenPointer) plan.children) :
    PlanAt n r p plan := by
  cases h with
  | plan span pointerBound slice size leading oldChildren =>
    apply Stored.plan span pointerBound
    · exact ⟨⟨root.pointer.trans slice.pointer.load, slice.pointer.covered⟩,
        ⟨root.length.trans slice.length.load, slice.length.covered⟩,
        slice.countBound, slice.byteBound, slice.span⟩
    · exact ⟨⟨root.sizePointer.trans size.stored.1,
        root.sizePayload.trans size.stored.2.1,
        operand_frame plan.size size.stored.2.2 frame limbs⟩, size.span, size.borrowed⟩
    · exact ⟨root.leading.trans leading.load, leading.covered⟩
    · exact children

mutual
  /-- Unlike `Stored.frame`, this rule does not require unrelated bytes of the
  ambient footprint to stay readonly. It follows exactly the retained Plan tree. -/
  theorem PlanAt.frame_footprint {m n : DataMem} {r w : Footprint} {p : BitVec 64}
      {plan : CodecMeasure.Plan} (h : PlanAt m r p plan) (frame : MemoryFrame m n w)
      (safe : ∀ a, planFootprint p plan a → ¬ w a) : PlanAt n r p plan := by
    cases plan with
    | mk size leading plans allocation =>
      have root : PlanRootSame m n p := PlanRootSame.of_frame frame
        (fun a ha => safe a (Or.inl ha))
      apply plan_fields_transport h root frame
      · intro a ha
        exact safe a (Or.inr (Or.inl ha))
      · cases h with
        | plan span bound slice size leading children =>
          exact PlansAt.frame_footprint children frame
            (fun a ha => safe a (Or.inr (Or.inr ha)))
  termination_by sizeOf plan
  decreasing_by all_goals simp_wf <;> omega

  theorem PlansAt.frame_footprint {m n : DataMem} {r w : Footprint} {p : BitVec 64}
      {plans : List CodecMeasure.Plan} (h : PlansAt m r p plans) (frame : MemoryFrame m n w)
      (safe : ∀ a, plansFootprint p plans a → ¬ w a) : PlansAt n r p plans := by
    cases plans with
    | nil => exact .plansNil
    | cons plan plans =>
      cases h with
      | plansCons head tail =>
        exact .plansCons
          (PlanAt.frame_footprint head frame (fun a ha => safe a (Or.inl ha)))
          (PlansAt.frame_footprint tail frame (fun a ha => safe a (Or.inr ha)))
  termination_by sizeOf plans
  decreasing_by all_goals simp_wf <;> omega
end

/-- Replacing an outer Plan with the same active fields preserves its recursive
storage provided the actual out-of-line children and size limbs are framed. In
particular the original ambient footprint may include the overwritten header. -/
theorem PlanAt.replaceRoot {m n : DataMem} {r w : Footprint} {p : BitVec 64}
    {plan : CodecMeasure.Plan} (h : PlanAt m r p plan) (root : PlanRootSame m n p)
    (frame : MemoryFrame m n w) (safe : ∀ a, planBorrowed plan a → ¬ w a) :
    PlanAt n r p plan := by
  apply plan_fields_transport h root frame
  · intro a ha
    exact safe a (Or.inl ha)
  · cases h with
    | plan span bound slice size leading children =>
      exact PlansAt.frame_footprint children frame (fun a ha => safe a (Or.inr ha))

mutual
  /-- Concrete retained footprints really are contained in the ambient region;
  there is no freshness or pairwise-disjointness assumption in this fact. -/
  theorem PlanAt.footprint_subset {m : DataMem} {r : Footprint} {p : BitVec 64}
      {plan : CodecMeasure.Plan} (h : PlanAt m r p plan) :
      ∀ a, planFootprint p plan a → r a := by
    cases plan with
    | mk number leading plans allocation =>
      cases h with
      | plan span bound slice size leading children =>
        intro a ha
        rcases ha with root | limbs | child
        · exact span.covered a root
        · exact size.borrowed a limbs
        · exact PlansAt.footprint_subset children a child
  termination_by sizeOf plan
  decreasing_by all_goals simp_wf <;> omega

  theorem PlansAt.footprint_subset {m : DataMem} {r : Footprint} {p : BitVec 64}
      {plans : List CodecMeasure.Plan} (h : PlansAt m r p plans) :
      ∀ a, plansFootprint p plans a → r a := by
    cases plans with
    | nil => intro a ha; exact False.elim ha
    | cons plan plans =>
      cases h with
      | plansCons head tail =>
        intro a ha
        rcases ha with first | rest
        · exact PlanAt.footprint_subset head a first
        · exact PlansAt.footprint_subset tail a rest
  termination_by sizeOf plans
  decreasing_by all_goals simp_wf <;> omega
end

end SszX86.Codec
