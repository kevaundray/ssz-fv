import SszArm.MeasureBitsListWidthModel
import SszArm.MeasureArenaFrame
import SszArm.MeasureHelpersResultSpace
import SszArm.MeasureHelpersCopySpace

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)
open Delimited (Span Protected)

theorem width_registers {schema : Schema} {s u : ArmState} {args : Args} {bits : Packed}
    {actual : NatOperand} (pre : Prefix s u args schema bits actual) (base : BitVec 64) :
    r (.GPR 31#5) (Width.result u base) = args.bodySP ∧
    r (.GPR 19#5) (Width.result u base) = args.result ∧
    r (.GPR 4#5) (Width.result u base) = args.arena ∧
    r (.GPR 0#5) (Width.result u base) = args.bodySP + 120#64 ∧
    r (.GPR 23#5) (Width.result u base) = args.bodySP + 120#64 := by
  refine ⟨(Width.result_register u base 31#5 (by decide)).trans pre.core.stack,
    (Width.result_register u base 19#5 (by decide)).trans pre.core.result,
    (Width.result_arguments u base).2.2.1.trans pre.core.arena, ?_, ?_⟩
  · rw [(Width.result_arguments u base).1, pre.core.stack]
  · rw [(Width.result_arguments u base).2.1, pre.core.stack]

theorem width_local_subset {schema : Schema} {s u : ArmState} {args : Args} {bits : Packed}
    {actual : NatOperand} (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual)
    (checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok ())
    (base : BitVec 64) (span : Span) (member : span ∈ NatFromU128.localWrites (Width.result u base)) :
    span ∈ bodyStackWrites args (outcome s args schema.descriptor (.bits bits)) := by
  have regs := width_registers pre base
  have low := owned.stackLow
  have scratch : (r (.GPR 0#5) (Width.result u base)).toNat = args.stack.toNat - 152 := by
    rw [regs.2.2.2.1, Args.bodySP]
    bv_omega
  have stack : (r (.GPR 31#5) (Width.result u base)).toNat - 16 = args.stack.toNat - 288 := by
    rw [regs.1, Args.bodySP]
    bv_omega
  simp only [NatFromU128.localWrites, scratch, stack, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl <;>
    simp [bodyStackWrites, width_two_calls pre checked]

theorem width_tail_subset {schema : Schema} {s u : ArmState} {args : Args} {bits : Packed}
    {actual : NatOperand} (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual)
    (checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok ())
    (base : BitVec 64) (span : Span) (member : span ∈ Constructor.tailWrites (Width.result u base)) :
    span ∈ bodyStackWrites args (outcome s args schema.descriptor (.bits bits)) ++
      resultWrites args (outcome s args schema.descriptor (.bits bits)) := by
  have regs := width_registers pre base
  have low := owned.stackLow
  have stack : (r (.GPR 31#5) (Width.result u base)).toNat - 16 = args.stack.toNat - 288 := by
    rw [regs.1, Args.bodySP]
    bv_omega
  cases second : (widthCall s args bits).result with
  | ok operand =>
    simp only [Constructor.tailWrites, width_outcome owned pre base, second,
      Result.successWrites, stack, regs.2.1, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact List.mem_append.mpr (Or.inl (by simp [bodyStackWrites]))
    · exact List.mem_append.mpr (Or.inr (by
        simp [resultWrites, width_model pre checked, second, Except.mapError]))
    · exact List.mem_append.mpr (Or.inr (by
        simp [resultWrites, width_model pre checked, second, Except.mapError]))
  | error reason =>
    simp only [Constructor.tailWrites, width_outcome owned pre base, second,
      regs.2.1, List.mem_singleton] at member
    subst span
    exact List.mem_append.mpr (Or.inr (by
      simp [resultWrites, resultExtent, propagated, width_model pre checked, second, Except.mapError]))

theorem width_tail_local_subset {schema : Schema} {s u : ArmState} {args : Args} {bits : Packed}
    {actual : NatOperand} (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual)
    (checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok ())
    (base : BitVec 64) (span : Span) (member : span ∈ Constructor.tailWrites (Width.result u base)) :
    span ∈ localWrites args (outcome s args schema.descriptor (.bits bits)) := by
  have selected := width_tail_subset owned pre checked base span member
  rcases List.mem_append.mp selected with stack | result
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr stack)))
  · exact List.mem_append.mpr (Or.inr result)

theorem count_used_monotone (s : ArmState) (args : Args) (bits : Packed) :
    (arenaOf s args).used ≤ (countCall s args bits).used := by
  exact (resource_fromWide (arenaOf s args) bits.count).monotone

end SszArm.Measure.Bits.List
