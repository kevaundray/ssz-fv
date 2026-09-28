import SszArm.MeasureBitsListCountModel
import SszArm.MeasureHelpersAllocation
import SszArm.MeasureHelpersCompareOwned

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)
open Delimited (Span Protected MemoryFrame)

theorem first_call_member (schema : Schema) (s : ArmState) (args : Args) (bits : Packed) :
    countCall s args bits ∈ (outcome s args schema.descriptor (.bits bits)).calls := by
  have firstMember : countCall s args bits ∈
      (SszNative.Serialize.fromWide (arenaOf s args) bits.count).calls := by
    change countCall s args bits ∈ [countCall s args bits]
    exact List.mem_singleton.mpr rfl
  rw [list_outcome, SszNative.Serialize.measureList]
  cases first : (SszNative.Serialize.fromWide (arenaOf s args) bits.count).result with
  | error reason =>
    rw [SszNative.Serialize.bind, first]
    exact firstMember
  | ok actual =>
    rw [SszNative.Serialize.bind, first]
    exact List.mem_append.mpr (Or.inl firstMember)

theorem count_writes_subset (schema : Schema) (s : ArmState) (args : Args) (bits : Packed)
    (span : Span) (member : span ∈ countWrites s args bits) :
    span ∈ allocationWrites args (outcome s args schema.descriptor (.bits bits)) := by
  simp only [countWrites] at member
  cases allocated : (countCall s args bits).allocation with
  | none => simp only [allocated, List.not_mem_nil] at member
  | some reservation =>
    have count : (countCall s args bits).written.length = 2 :=
      fromWide_written_length (arenaOf s args) bits.count reservation allocated
    apply List.mem_flatMap.mpr
    refine ⟨countCall s args bits, first_call_member schema s args bits, ?_⟩
    simpa only [allocated, count, Nat.reduceMul] using member

theorem CountPost.full_frame {schema : Schema} {s t : ArmState} {args : Args} {bits : Packed}
    {base : BitVec 64} {actual : NatOperand} (post : CountPost s t args schema bits base actual) :
    MemoryFrame (writesFor args (outcome s args schema.descriptor (.bits bits))) s t := by
  apply post.frame.weaken
  intro span member
  exact List.mem_append.mpr (Or.inr (count_writes_subset schema s args bits span member))

theorem lowering_subset_local (args : Args) (measured : SszNative.Serialize.Outcome NatOperand)
    (u : ArmState) (low : 288 ≤ args.stack.toNat) (stack : r (.GPR 31#5) u = args.bodySP)
    (span : Span) (member : span ∈ Helpers.loweringWrites u) : span ∈ localWrites args measured := by
  have position : (r (.GPR 31#5) u).toNat - 16 = args.stack.toNat - 288 := by
    rw [stack, Args.bodySP]
    bv_omega
  simp only [Helpers.loweringWrites, position, List.mem_singleton] at member
  subst span
  simp [localWrites, stackWrites, bodyStackWrites]

theorem lowering_subset_body (args : Args) (measured : SszNative.Serialize.Outcome NatOperand)
    (u : ArmState) (low : 288 ≤ args.stack.toNat) (stack : r (.GPR 31#5) u = args.bodySP)
    (span : Span) (member : span ∈ Helpers.loweringWrites u) : span ∈ bodyStackWrites args measured := by
  have position : (r (.GPR 31#5) u).toNat - 16 = args.stack.toNat - 288 := by
    rw [stack, Args.bodySP]
    bv_omega
  simp only [Helpers.loweringWrites, position, List.mem_singleton] at member
  subst span
  simp [bodyStackWrites]

theorem operand_owned_restrict {small large : List Span} (operand : NatOperand)
    (owned : NatDivision.OperandOwned large operand)
    (subset : ∀ span ∈ small, span ∈ large) : NatDivision.OperandOwned small operand := by
  cases operand with
  | small word => trivial
  | large pointer words =>
    rcases owned with empty | separate
    · exact Or.inl empty
    · exact Or.inr (fun span member => separate span (subset span member))

theorem CountPost.actual_lower_owned {schema : Schema} {s t : ArmState} {args : Args} {bits : Packed}
    {base : BitVec 64} {actual : NatOperand}
    (owned : Owned s args schema.descriptor (.bits bits))
    (post : CountPost s t args schema bits base actual) :
    NatDivision.OperandOwned (Helpers.loweringWrites t) actual := by
  apply Helpers.fromWide_result_owned (Helpers.loweringWrites t) (arenaOf s args) bits.count
    owned.storageBound _ actual post.counted
  rcases owned.freeLocal with empty | separate
  · exact Or.inl empty
  · right
    intro span member
    apply separate span
    exact List.mem_append.mpr (Or.inl (lowering_subset_local args _ t owned.stackLow post.work.stack span member))

theorem cap_member (schema : Schema) (cap : NatOperand) (present : schema.cap = some cap) :
    cap ∈ Emit.descriptorOperands schema.descriptor := by
  cases schema with
  | bounded value =>
    simp only [Schema.cap, Option.some.injEq] at present
    subst value
    simp [Schema.descriptor, Emit.descriptorOperands]
  | progressive option =>
    simp only [Schema.cap] at present
    subst option
    simp [Schema.descriptor, Emit.descriptorOperands]

theorem CountPost.cap_at {schema : Schema} {s t : ArmState} {args : Args} {bits : Packed}
    {base : BitVec 64} {actual : NatOperand}
    (owned : Owned s args schema.descriptor (.bits bits))
    (post : CountPost s t args schema bits base actual)
    (cap : NatOperand) (present : schema.cap = some cap) : cap.At (UintCodec.widthLoad t) := by
  have member : cap ∈ Emit.descriptorOperands schema.descriptor ++ Emit.valueOperands (.bits bits) :=
    List.mem_append.mpr (Or.inl (cap_member schema cap present))
  exact NatDivision.operand_at_preserved post.full_frame cap (owned.operand_at cap member)
    (owned.operandOwned cap member)

theorem CountPost.cap_lower_owned {schema : Schema} {s t : ArmState} {args : Args} {bits : Packed}
    {base : BitVec 64} {actual : NatOperand}
    (owned : Owned s args schema.descriptor (.bits bits))
    (post : CountPost s t args schema bits base actual)
    (cap : NatOperand) (present : schema.cap = some cap) :
    NatDivision.OperandOwned (Helpers.loweringWrites t) cap := by
  apply operand_owned_restrict cap (owned.operandOwned cap
    (List.mem_append.mpr (Or.inl (cap_member schema cap present))))
  intro span member
  exact List.mem_append.mpr (Or.inl (lowering_subset_local args _ t owned.stackLow post.work.stack span member))

end SszArm.Measure.Bits.List
