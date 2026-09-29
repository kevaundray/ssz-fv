import SszX86.CodecMeasureFixedMemory
import SszX86.CodecMeasureFixedProvenance
import SszX86.CodecMeasureFixedArithmeticTraceGeometry
import SszX86.CodecMeasureFixedArithmeticOwnershipOperands
import SszX86.MeasureBitsCountPrefix

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

theorem calls_append (observe : Nat → Nat → Option Nat)
    (left right : List (NatArithmetic.Outcome NatOperand))
    (first : CallsAt observe left) (second : CallsAt observe right) :
    CallsAt observe (left ++ right) := by
  intro call member reservation allocated
  rcases List.mem_append.mp member with before | after
  · exact first call before reservation allocated
  · exact second call after reservation allocated

theorem allocated_append (left right : List (NatArithmetic.Outcome NatOperand)) :
    Allocated (left ++ right) ↔ Allocated left ∨ Allocated right := by
  constructor
  · rintro ⟨call, member, reservation, allocated⟩
    rcases List.mem_append.mp member with before | after
    · exact Or.inl ⟨call, before, reservation, allocated⟩
    · exact Or.inr ⟨call, after, reservation, allocated⟩
  · rintro (⟨call, member, reservation, allocated⟩ | ⟨call, member, reservation, allocated⟩)
    · exact ⟨call, List.mem_append.mpr (Or.inl member), reservation, allocated⟩
    · exact ⟨call, List.mem_append.mpr (Or.inr member), reservation, allocated⟩

/-- Exact prefix-frame composition: successful reservations retain their full
written limb buffers after later recursive errors. -/
theorem trace_frame_append (original : MachineData) (middle after : DataMem) (bytes : Nat)
    (left right : List (NatArithmetic.Outcome NatOperand))
    (first : Codec.MemoryFrame original.dmem middle (fun a =>
      Codec.StackWrites original.regs.rsp.toBitVec bytes a ∨ AllocationWrites left a ∨
      (Allocated left ∧ Codec.InSpan a (original.regs.rdx.toBitVec + 16) 8)))
    (second : Codec.MemoryFrame middle after (fun a =>
      Codec.StackWrites original.regs.rsp.toBitVec bytes a ∨ AllocationWrites right a ∨
      (Allocated right ∧ Codec.InSpan a (original.regs.rdx.toBitVec + 16) 8))) :
    Codec.MemoryFrame original.dmem after (fun a =>
      Codec.StackWrites original.regs.rsp.toBitVec bytes a ∨ AllocationWrites (left ++ right) a ∨
      (Allocated (left ++ right) ∧ Codec.InSpan a (original.regs.rdx.toBitVec + 16) 8)) := by
  intro a outside
  have beforeSafe : ¬ (Codec.StackWrites original.regs.rsp.toBitVec bytes a ∨
      AllocationWrites left a ∨ (Allocated left ∧ Codec.InSpan a (original.regs.rdx.toBitVec + 16) 8)) := by
    rintro (stack | writes | ⟨allocated, cursor⟩)
    · exact outside (Or.inl stack)
    · exact outside (Or.inr (Or.inl ((allocationWrites_append _ _ _).mpr (Or.inl writes))))
    · exact outside (Or.inr (Or.inr ⟨(allocated_append _ _).mpr (Or.inl allocated), cursor⟩))
  have afterSafe : ¬ (Codec.StackWrites original.regs.rsp.toBitVec bytes a ∨
      AllocationWrites right a ∨ (Allocated right ∧ Codec.InSpan a (original.regs.rdx.toBitVec + 16) 8)) := by
    rintro (stack | writes | ⟨allocated, cursor⟩)
    · exact outside (Or.inl stack)
    · exact outside (Or.inr (Or.inl ((allocationWrites_append _ _ _).mpr (Or.inr writes))))
    · exact outside (Or.inr (Or.inr ⟨(allocated_append _ _).mpr (Or.inr allocated), cursor⟩))
  exact (second a afterSafe).trans (first a beforeSafe)

/-- All prior allocation bytes lie apart from the activation and arena header. -/
theorem committed_safe {original : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (owned : Owned original base r desc address capacity used ra bytes)
    (a : BitVec 64) (location : address.toNat + used.toNat ≤ a.toNat ∧
      a.toNat < address.toNat + capacity.toNat) :
    ¬ Codec.StackWrites original.regs.rsp.toBitVec bytes a ∧
      ¬ Codec.InSpan a (original.regs.rdx.toBitVec + 16) 8 := by
  have nonempty : 0 < capacity.toNat - used.toNat := by omega
  constructor
  · intro stack
    have atStack := stack_bounds owned.stack.lowEnough stack
    have apart := owned.arena_stack.nonempty nonempty (by omega)
    omega
  · intro cursor
    have hb := owned.header_bound
    have atCursor : original.regs.rdx.toNat + 16 ≤ a.toNat ∧
        a.toNat < original.regs.rdx.toNat + 24 := by
      rcases cursor with ⟨i, hi, same⟩
      bv_omega
    have apart := owned.arena_header.nonempty nonempty (by decide)
    omega

/-- A returned width may borrow the original readonly graph or an earlier
allocation; neither needs fresh, disjoint readonly storage. -/
theorem operand_safe_after_trace {original : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra current : BitVec 64} {bytes : Nat}
    (owned : Owned original base r desc address capacity used ra bytes)
    {α : Type} (outcome : Serialize.Outcome α)
    (geometry : TraceGeometry (arenaState address capacity used) outcome)
    (cursor : current.toNat = outcome.used) (operand : NatOperand)
    (provenance : ∀ a, Emit.NatBorrowed operand a → r a ∨ AllocationWrites outcome.calls a) :
    ArithmeticOperandSafe original bytes address capacity current operand := by
  intro a borrowed writes
  have lower : used.toNat ≤ current.toNat := by simpa only [cursor] using geometry.lower
  have upper : current.toNat ≤ capacity.toNat := by simpa only [cursor] using geometry.upper
  rcases provenance a borrowed with readonly | allocated
  · apply owned.readonly a readonly
    rcases writes with stack | header | free
    · exact Or.inr (Or.inl stack)
    · exact Or.inr (Or.inr (Or.inl header))
    · exact Or.inr (Or.inr (Or.inr (free_shrinks lower upper free)))
  · have location := geometry.writes a allocated
    change address.toNat + used.toNat ≤ a.toNat ∧ a.toNat < address.toNat + outcome.used at location
    have bound : a.toNat < address.toNat + capacity.toNat := by omega
    have safe := committed_safe owned a ⟨location.1, bound⟩
    rcases writes with stack | header | free
    · exact safe.1 stack
    · exact safe.2 header
    · have future := free_bounds owned.arena_bound upper free
      omega

/-- Completed earlier payloads survive an actual later call's exact write frame;
this is a resource proof, not a future execution assumption. -/
theorem calls_survive_next {original : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (owned : Owned original base r desc address capacity used ra bytes)
    {α β : Type} (first : Serialize.Outcome α) (second : Serialize.Outcome β)
    (geometry : TraceGeometry (arenaState address capacity used) first)
    (following : TraceGeometry {arenaState address capacity used with used := first.used} second)
    (before after : DataMem)
    (frame : Codec.MemoryFrame before after (fun a =>
      Codec.StackWrites original.regs.rsp.toBitVec bytes a ∨ AllocationWrites second.calls a ∨
      (Allocated second.calls ∧ Codec.InSpan a (original.regs.rdx.toBitVec + 16) 8)))
    (stored : CallsAt (widthLoad before) first.calls) : CallsAt (widthLoad after) first.calls := by
  apply Measure.Bits.calls_frame before after first.calls _ frame ?_ stored
  intro a written writes
  have location := geometry.writes a written
  change address.toNat + used.toNat ≤ a.toNat ∧ a.toNat < address.toNat + first.used at location
  have upper := geometry.upper
  change first.used ≤ capacity.toNat at upper
  have safe := committed_safe owned a ⟨location.1, by omega⟩
  rcases writes with stack | allocated | cursor
  · exact safe.1 stack
  · have nextLocation := following.writes a allocated
    change address.toNat + first.used ≤ a.toNat ∧ a.toNat < address.toNat + second.used at nextLocation
    omega
  · exact safe.2 cursor.2

end SszX86.CodecMeasureFixed
