import SszX86.BitVectorStable

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem Protected.with_memory {s : MachineData} {address capacity used : BitVec 64}
    {p n : Nat} (owned : Protected s address capacity used p n) (m : DataMem) :
    Protected {s with dmem := m} address capacity used p n :=
  ⟨owned.bound, owned.output, owned.work, owned.cursor, owned.arena⟩

theorem free_suffix_advance (address capacity used next p n : Nat)
    (progress : used ≤ next) (bound : next ≤ capacity)
    (apart : Body.Apart (address + used) (capacity - used) p n) :
    Body.Apart (address + next) (capacity - next) p n := by
  unfold Body.Apart at *
  omega

theorem StableFrame.saved_at (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (owned : Owned s saved length data address capacity used) (m : DataMem)
    (frame : StableFrame s address capacity used m) : SavedAt m s.regs.rsp.toBitVec saved := by
  have region := StableFrame.saved_region s saved length data address capacity used owned
  have preserves (off : Nat) (lower : 312 ≤ off) (upper : off + 8 ≤ 368) :
      Mem.loadInt m (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 =
        Mem.loadInt s.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 := by
    have kept := frame.load (region.subrange (off - 312) 8 (by omega))
    have position : s.regs.rsp.toNat + 312 + (off - 312) = s.regs.rsp.toNat + off := by omega
    rw [position] at kept
    change Mem.loadInt m (BitVec.ofNat 64 (s.regs.rsp.toBitVec.toNat + off)) 8 =
      Mem.loadInt s.dmem (BitVec.ofNat 64 (s.regs.rsp.toBitVec.toNat + off)) 8 at kept
    simpa only [width_address] using kept
  simpa (disch := omega) only [SavedAt, preserves] using owned.saved_at

/-- Restores the physical entry-shaped ownership record over a later memory.
This does not assert the current execution registers equal the entry registers;
call-specific ABI adapters separately establish that fact for every helper. -/
theorem Owned.rebase (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used next : BitVec 64)
    (owned : Owned s saved length data address capacity used) (m : DataMem)
    (frame : StableFrame s address capacity used m) (mapping : Mapping.Extends s.dmem m)
    (progress : used.toNat ≤ next.toNat) (nextBound : next.toNat ≤ capacity.toNat)
    (cursor : Mem.loadInt m (s.regs.rbx.toBitVec + 16) 8 = some (next.toNat : Int)) :
    Owned {s with dmem := m} saved length data address capacity next := by
  have header := StableFrame.header_region s saved length data address capacity used owned
  have headerRead (off : Nat) (inside : off + 8 ≤ 16) :
      Mem.loadInt m (s.regs.rbx.toBitVec + BitVec.ofNat 64 off) 8 =
        Mem.loadInt s.dmem (s.regs.rbx.toBitVec + BitVec.ofNat 64 off) 8 := by
    have kept := frame.load (header.subrange off 8 inside)
    change Mem.loadInt m (BitVec.ofNat 64 (s.regs.rbx.toBitVec.toNat + off)) 8 =
      Mem.loadInt s.dmem (BitVec.ofNat 64 (s.regs.rbx.toBitVec.toNat + off)) 8 at kept
    simpa only [width_address] using kept
  refine {
    output_bound := owned.output_bound
    output_mapped := mapping _ _ owned.output_mapped
    stack_low := owned.stack_low
    stack_bound := owned.stack_bound
    work_mapped := mapping _ _ owned.work_mapped
    saved_at := frame.saved_at s saved length data address capacity used owned m
    output_work := owned.output_work
    output_saved := owned.output_saved
    descriptor := ?_
    descriptor_owned := (owned.descriptor_owned.advance progress nextBound).with_memory m
    operand_owned := ?_
    data_length := owned.data_length
    source := ?_
    source_owned := (owned.source_owned.advance progress nextBound).with_memory m
    header_bound := owned.header_bound
    address_load := ?_
    capacity_load := ?_
    used_load := cursor
    arena_bound := owned.arena_bound
    used_bound := nextBound
    arena_nonzero := owned.arena_nonzero
    arena_mapped := mapping _ _ owned.arena_mapped
    arena_output := free_suffix_advance _ _ _ _ _ _ progress nextBound owned.arena_output
    arena_work := free_suffix_advance _ _ _ _ _ _ progress nextBound owned.arena_work
    arena_saved := free_suffix_advance _ _ _ _ _ _ progress nextBound owned.arena_saved
    arena_header := free_suffix_advance _ _ _ _ _ _ progress nextBound owned.arena_header
    header_output := owned.header_output
    header_work := owned.header_work
    cursor_saved := owned.cursor_saved }
  · refine ⟨?_, ?_, frame.operand length owned.descriptor.2.2 owned.operand_owned⟩
    · rw [frame.width (owned.descriptor_owned.subrange 8 8 (by decide))]
      exact owned.descriptor.1
    · have preserved := frame.width (owned.descriptor_owned.subrange 16 8 (by decide))
      simpa only [Nat.add_assoc, Nat.reduceAdd, preserved] using owned.descriptor.2.1
  · cases length with
    | small limb => trivial
    | large pointer words => exact (owned.operand_owned.advance progress nextBound).with_memory m
  · intro i hi
    rw [frame.width (owned.source_owned.subrange i 1 (by omega))]
    exact owned.source i hi
  · have kept := headerRead 0 (by decide)
    simp only [BitVec.add_zero] at kept
    exact kept.trans owned.address_load
  · change Mem.loadInt m (s.regs.rbx.toBitVec + 8#64) 8 = some (capacity.toNat : Int)
    exact (headerRead 8 (by decide)).trans owned.capacity_load

end SszX86.BitVector
