import SszArm.MeasureBitsListWidthWrites
import SszArm.MeasureAllocationOrder

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

theorem width_first_protected {schema : Schema} {s u : ArmState} {args : Args} {bits : Packed}
    {actual : NatOperand} (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual)
    (checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok ())
    (base : BitVec 64) (reservation : SszNative.Arena.Reservation)
    (allocated : (countCall s args bits).allocation = some reservation) :
    Protected (Constructor.writesFor (Width.result u base)) reservation.pointer
      (8 * (countCall s args bits).written.length) := by
  have first := first_call_member schema s args bits
  have count := callsTwo_measure (arenaOf s args) schema.descriptor (.bits bits) (countCall s args bits)
    first reservation allocated
  have original := owned.allocation_protected (countCall s args bits) first reservation allocated
  rcases original with empty | separate
  · omega
  right
  intro span member
  simp only [Constructor.writesFor, NatFromU128.writesFor, List.mem_append] at member
  rcases member with (localSpan | allocation) | tail
  · obtain ⟨outer, allowed, low, high⟩ := width_native_local_cover owned pre checked base span localSpan
    have apart := separate outer (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr allowed))))))
    omega
  · rw [width_outcome owned pre base] at allocation
    cases second : (widthCall s args bits).allocation with
    | none => simp only [second, List.not_mem_nil] at allocation
    | some later =>
      simp only [second, (width_positions owned pre base).2.2.2,
        List.mem_cons, List.not_mem_nil, or_false] at allocation
      rcases allocation with rfl | rfl
      · have apart := separate (args.arena.toNat, 24) (List.mem_append.mpr (Or.inr (by simp)))
        dsimp at apart ⊢
        omega
      · have order := fromWide_allocations_ordered (arenaOf s args) bits.count
          (BitVec.ofNat 128 (bits.count.toNat / 8 + 1)) reservation later allocated second
        left
        dsimp
        omega
  · obtain ⟨outer, allowed, low, high⟩ := width_tail_cover owned pre checked base span tail
    have localSpan : outer ∈ localWrites args (outcome s args schema.descriptor (.bits bits)) := by
      rcases List.mem_append.mp allowed with stack | result
      · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr stack)))
      · exact List.mem_append.mpr (Or.inr result)
    have apart := separate outer (List.mem_append.mpr (Or.inl localSpan))
    omega

theorem width_first_written {schema : Schema} {s u t : ArmState} {args : Args} {bits : Packed}
    {actual : NatOperand} (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual)
    (checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok ())
    (base : BitVec 64)
    (frame : MemoryFrame (Constructor.writesFor (Width.result u base)) (Width.result u base) t)
    (input : NatDivision.WrittenAt (widthLoad (Width.result u base)) (countCall s args bits)) :
    NatDivision.WrittenAt (widthLoad t) (countCall s args bits) := by
  intro reservation allocated index
  have bound := (resource_measure (arenaOf s args) schema.descriptor (.bits bits)).allocations
    (countCall s args bits) (first_call_member schema s args bits) reservation allocated
  have storage := owned.storageBound
  have buffer := width_first_protected owned pre checked base reservation allocated
  have within := index.isLt
  have wordOwned := buffer.subspan (8 * index.val) 8 (by omega)
  rw [frame.load (reservation.pointer + 8 * index.val) 8 (by omega) wordOwned]
  exact input reservation allocated index

theorem prefix_width_written {schema : Schema} {s u : ArmState} {args : Args} {bits : Packed}
    {actual : NatOperand} (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual) (base : BitVec 64) :
    NatDivision.WrittenAt (widthLoad (Width.result u base)) (countCall s args bits) := by
  have stackLow : 16 ≤ (r (.GPR 31#5) u).toNat := by
    have low := owned.stackLow
    rw [pre.core.stack, Args.bodySP]
    bv_omega
  apply Helpers.fromWide_written_preserved (arenaOf s args) bits.count owned.storageBound _
    (Width.result_frame u base stackLow) pre.written
  rcases owned.freeLocal with empty | separate
  · exact Or.inl empty
  · right
    intro span member
    exact separate span (List.mem_append.mpr (Or.inl
      (lowering_subset_local args _ u owned.stackLow pre.core.stack span member)))

end SszArm.Measure.Bits.List
