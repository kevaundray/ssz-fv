import SszArm.MeasureBitListSpaceGeometry

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)
open Delimited (Span Protected)

theorem width_native_owned {schema : Schema} {s u : ArmState} {args : Args} {bits : Packed}
    {actual : NatOperand} (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual)
    (checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok ())
    (base : BitVec 64) : NatFromU128.Owned (Width.result u base) := by
  have regs := width_registers pre base
  have low := owned.stackLow
  have arena := width_arena owned pre base
  have address : (NatFromU128.addressWord (Width.result u base)).toNat = (arenaOf s args).base :=
    congrArg SszNative.Delimited.ArenaState.base arena
  have capacity : (NatFromU128.capacityWord (Width.result u base)).toNat = (arenaOf s args).capacity :=
    congrArg SszNative.Delimited.ArenaState.capacity arena
  have used : (NatFromU128.usedWord (Width.result u base)).toNat = (countCall s args bits).used :=
    congrArg SszNative.Delimited.ArenaState.used arena
  have localSubset : ∀ span ∈ NatFromU128.localWrites (Width.result u base),
      span ∈ localWrites args (outcome s args schema.descriptor (.bits bits)) := by
    intro span member
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
      (width_local_subset owned pre checked base span member))))
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [regs.1, Args.bodySP]
    bv_omega
  · rw [regs.2.2.2.1, Args.bodySP]
    bv_omega
  · right
    rw [regs.2.2.2.1, regs.1, Args.bodySP]
    bv_omega
  · rw [regs.2.2.1]
    exact owned.arenaBound
  · rw [address, capacity]
    exact owned.storageBound
  · rw [address, capacity]
    exact owned.nonnull
  · rw [regs.2.2.1]
    rcases owned.headerLocal with empty | separate
    · exact Or.inl empty
    · exact Or.inr (fun span member => separate span (localSubset span member))
  · rw [regs.2.2.1, address, capacity, used]
    have free := owned.free_after (countCall s args bits).used (count_used_monotone s args bits)
    rcases free with empty | separate
    · exact Or.inl empty
    · right
      intro span member
      rcases List.mem_append.mp member with localMember | headerMember
      · exact separate span (List.mem_append.mpr (Or.inl (localSubset span localMember)))
      · exact separate span (List.mem_append.mpr (Or.inr headerMember))

end SszArm.Measure.Bits.List
