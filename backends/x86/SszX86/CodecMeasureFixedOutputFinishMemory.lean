import SszX86.CodecMeasureFixedOutputFinishCore

namespace SszX86.CodecMeasureFixed.Output
open SszNative UintCodec

/-- A byte-exact output frame preserves any physically disjoint observation. -/
theorem output_load (before after : DataMem) (out : BitVec 64)
    (result : Except Serialize.Error (Option NatOperand))
    (frame : Codec.MemoryFrame before after (ResultWrites out result))
    (p n : Nat) (safe : ∀ i < n,
      ¬ Codec.InSpan (BitVec.ofNat 64 p + BitVec.ofNat 64 i) out 72) :
    widthLoad after p n = widthLoad before p n := by
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  apply frame
  intro writes
  exact safe i hi (result_writes_span out result _ writes)

theorem publication_calls {original : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (owned : Owned original base r desc address capacity used ra bytes)
    (before after : DataMem)
    (frame : Codec.MemoryFrame before after
      (ResultWrites original.regs.rdi.toBitVec
        (FixedSize.measureFixed desc (arenaState address capacity used)).result))
    (calls : CallsAt (widthLoad before)
      (FixedSize.measureFixed desc (arenaState address capacity used)).calls) :
    CallsAt (widthLoad after)
      (FixedSize.measureFixed desc (arenaState address capacity used)).calls := by
  intro call member reservation allocated i
  rw [output_load before after _ _ frame]
  · exact calls call member reservation allocated i
  · intro j hj output
    have write : AllocationWrites
        (FixedSize.measureFixed desc (arenaState address capacity used)).calls
        (BitVec.ofNat 64 (reservation.pointer + 8*i.val) + BitVec.ofNat 64 j) := by
      refine ⟨call, member, reservation, allocated, 8*i.val+j, by have := i.isLt; omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.add_assoc]
    have geometry := measureFixed_trace_geometry desc (arenaState address capacity used)
      owned.arena_bound owned.used_bound
    have location := geometry.writes _ write
    have upper := geometry.upper
    change address.toNat + used.toNat ≤ _ ∧ _ < address.toNat + _ at location
    change _ ≤ capacity.toNat at upper
    have outputPosition := span_bounds owned.output_bound output
    have apart := owned.arena_output.nonempty (by omega) (by decide)
    omega

theorem publication_cursor {original : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (owned : Owned original base r desc address capacity used ra bytes)
    (before after : DataMem) (result : Except Serialize.Error (Option NatOperand))
    (frame : Codec.MemoryFrame before after (ResultWrites original.regs.rdi.toBitVec result)) :
    widthLoad after (original.regs.rdx.toNat + 16) 8 =
      widthLoad before (original.regs.rdx.toNat + 16) 8 := by
  apply output_load before after _ _ frame
  intro i hi inside
  have atOutput := span_bounds owned.output_bound inside
  have bound := owned.header_bound
  have atHeader : original.regs.rdx.toNat ≤
      (BitVec.ofNat 64 (original.regs.rdx.toNat + 16) + BitVec.ofNat 64 i).toNat ∧
      (BitVec.ofNat 64 (original.regs.rdx.toNat + 16) + BitVec.ofNat 64 i).toNat <
        original.regs.rdx.toNat + 24 := by bv_omega
  have apart := owned.header_output.nonempty (by decide) (by decide)
  omega

/-- Compose the completed prefix with the concrete publication frame. -/
theorem Pending.published_frame {original body : MachineData} {desc : SszNative.Codec.Desc}
    {address capacity used ra : BitVec 64} {bytes : Nat}
    (pending : Pending original desc address capacity used ra bytes body) (m : DataMem)
    (publication : Codec.MemoryFrame body.dmem m
      (ResultWrites original.regs.rdi.toBitVec
        (FixedSize.measureFixed desc (arenaState address capacity used)).result)) :
    Codec.MemoryFrame original.dmem m
      (Writable original bytes (FixedSize.measureFixed desc (arenaState address capacity used))) := by
  intro a outside
  rw [publication a (fun written => outside (Or.inl written))]
  apply pending.frame a
  intro written
  exact outside (Or.inr written)

end SszX86.CodecMeasureFixed.Output
