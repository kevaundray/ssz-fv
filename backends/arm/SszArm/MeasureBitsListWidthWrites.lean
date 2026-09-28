import SszArm.MeasureBitsListWidthModel
import SszArm.MeasureAllocationFrame
import SszArm.BitVectorMemory

namespace SszArm.Measure.Bits.List

open Delimited (Span)
open SszArm.BitVector (Covers)

 theorem width_positions {schema : Schema} {s u : ArmState} {args : Args} {bits : SszNative.Serialize.Packed}
    {actual : SszNative.NatOperand} (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual) (base : BitVec 64) :
    (r (.GPR 0#5) (Width.result u base)).toNat = args.stack.toNat - 152 ∧
    (r (.GPR 31#5) (Width.result u base)).toNat - 16 = args.stack.toNat - 288 ∧
    r (.GPR 19#5) (Width.result u base) = args.result ∧
    r (.GPR 4#5) (Width.result u base) = args.arena := by
  have low := owned.stackLow
  have sp := (Width.result_register u base 31#5 (by decide)).trans pre.core.stack
  refine ⟨?_, ?_, (Width.result_register u base 19#5 (by decide)).trans pre.core.result,
    (Width.result_arguments u base).2.2.1.trans pre.core.arena⟩
  · rw [(Width.result_arguments u base).1, pre.core.stack, Args.bodySP]
    bv_omega
  · rw [sp, Args.bodySP]
    bv_omega

theorem width_native_local_cover {schema : Schema} {s u : ArmState} {args : Args} {bits : SszNative.Serialize.Packed}
    {actual : SszNative.NatOperand} (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual)
    (checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok ())
    (base : BitVec 64) :
    Covers (bodyStackWrites args (outcome s args schema.descriptor (.bits bits)))
      (match (NatFromU128.outcome (Width.result u base)).result with
      | .ok _ => NatFromU128.successWrites (Width.result u base)
      | .error _ => NatFromU128.localWrites (Width.result u base)) := by
  have pos := width_positions owned pre base
  have scratch : (args.stack.toNat - 152, 68) ∈ bodyStackWrites args (outcome s args schema.descriptor (.bits bits)) := by
    simp [bodyStackWrites, width_two_calls pre checked]
  have lower : (args.stack.toNat - 288, 16) ∈ bodyStackWrites args (outcome s args schema.descriptor (.bits bits)) := by
    simp [bodyStackWrites]
  intro span member
  cases native : (NatFromU128.outcome (Width.result u base)).result with
  | ok operand =>
    simp only [native, NatFromU128.successWrites, pos.1, pos.2.1,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨_, scratch, by omega, by dsimp; omega⟩
    · exact ⟨_, scratch, by dsimp; omega, by dsimp; omega⟩
    · exact ⟨_, lower, Nat.le_refl _, Nat.le_refl _⟩
  | error reason =>
    simp only [native, NatFromU128.localWrites, pos.1, pos.2.1,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨_, scratch, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, lower, Nat.le_refl _, Nat.le_refl _⟩

theorem width_tail_cover {schema : Schema} {s u : ArmState} {args : Args} {bits : SszNative.Serialize.Packed}
    {actual : SszNative.NatOperand} (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual)
    (checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok ())
    (base : BitVec 64) :
    Covers (bodyStackWrites args (outcome s args schema.descriptor (.bits bits)) ++
      resultWrites args (outcome s args schema.descriptor (.bits bits)))
      (Constructor.tailWrites (Width.result u base)) := by
  have pos := width_positions owned pre base
  have model := width_model pre checked
  intro span member
  cases second : (widthCall s args bits).result with
  | ok operand =>
    have result : resultWrites args (outcome s args schema.descriptor (.bits bits)) =
        [(args.result.toNat, 40), (args.result.toNat + 64, 4)] := by
      simp only [resultWrites, model, second, Except.mapError]
    simp only [Constructor.tailWrites, width_outcome owned pre base, second, Result.successWrites,
      pos.2.1, pos.2.2.1, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨_, List.mem_append.mpr (Or.inl (by simp [bodyStackWrites])), Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, List.mem_append.mpr (Or.inr (by simp only [result, List.mem_cons]; exact Or.inl trivial)),
        Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, List.mem_append.mpr (Or.inr (by simp [result])), Nat.le_refl _, Nat.le_refl _⟩
  | error reason =>
    have result : resultWrites args (outcome s args schema.descriptor (.bits bits)) = [(args.result.toNat, 72)] := by
      simp [resultWrites, model, second, Except.mapError, resultExtent, propagated]
    simp only [Constructor.tailWrites, width_outcome owned pre base, second, pos.2.2.1, List.mem_singleton] at member
    subst span
    exact ⟨_, List.mem_append.mpr (Or.inr (by simp [result])), Nat.le_refl _, Nat.le_refl _⟩

theorem width_constructor_cover {schema : Schema} {s u : ArmState} {args : Args} {bits : SszNative.Serialize.Packed}
    {actual : SszNative.NatOperand} (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual)
    (checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok ())
    (base : BitVec 64) :
    Covers (bodyWrites args (outcome s args schema.descriptor (.bits bits)))
      (Constructor.writesFor (Width.result u base)) := by
  intro span member
  simp only [Constructor.writesFor, NatFromU128.writesFor, List.mem_append] at member
  rcases member with (localSpan | allocated) | tail
  · obtain ⟨outer, allowed, low, high⟩ := width_native_local_cover owned pre checked base span localSpan
    exact ⟨outer, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl allowed))), low, high⟩
  · rw [width_outcome owned pre base] at allocated
    cases allocation : (widthCall s args bits).allocation with
    | none => simp only [allocation, List.not_mem_nil] at allocated
    | some reservation =>
      have second : widthCall s args bits ∈ (outcome s args schema.descriptor (.bits bits)).calls := by
        rw [width_model pre checked]
        simp
      have count := callsTwo_measure (arenaOf s args) schema.descriptor (.bits bits)
        (widthCall s args bits) second reservation allocation
      have output : span ∈ allocationWrites args (outcome s args schema.descriptor (.bits bits)) := by
        apply List.mem_flatMap.mpr
        refine ⟨widthCall s args bits, second, ?_⟩
        simpa only [allocation, (width_positions owned pre base).2.2.2, count, Nat.reduceMul] using allocated
      exact ⟨span, List.mem_append.mpr (Or.inr output), Nat.le_refl _, Nat.le_refl _⟩
  · obtain ⟨outer, allowed, low, high⟩ := width_tail_cover owned pre checked base span tail
    exact ⟨outer, List.mem_append.mpr (Or.inl allowed), low, high⟩

end SszArm.Measure.Bits.List
