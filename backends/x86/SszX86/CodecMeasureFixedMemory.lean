import SszX86.CodecMeasureFixedCore
import SszX86.BitVectorMappingClosure

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

/-- The broad original mutable region used only for preserving entry resources.
The public postcondition retains the smaller exact ResultWrites/call footprint. -/
def Mutable (s : MachineData) (address used capacity : BitVec 64) (bytes : Nat)
    (a : BitVec 64) : Prop :=
  Codec.InSpan a s.regs.rdi.toBitVec 72 ∨
  Codec.StackWrites s.regs.rsp.toBitVec bytes a ∨
  Codec.InSpan a (s.regs.rdx.toBitVec + 16) 8 ∨
  Codec.InSpan a (address + used) (capacity.toNat - used.toNat)

theorem span_bounds {a p : BitVec 64} {n : Nat}
    (bound : p.toNat + n ≤ 2 ^ 64) (inside : Codec.InSpan a p n) :
    p.toNat ≤ a.toNat ∧ a.toNat < p.toNat + n := by
  rcases inside with ⟨i, hi, same⟩
  bv_omega

theorem stack_bounds {a sp : BitVec 64} {bytes : Nat}
    (low : bytes ≤ sp.toNat) (inside : Codec.StackWrites sp bytes a) :
    sp.toNat - bytes ≤ a.toNat ∧ a.toNat < sp.toNat := by
  rcases inside with ⟨i, hi, same⟩
  bv_omega

theorem free_bounds {a address used capacity : BitVec 64}
    (bound : address.toNat + capacity.toNat ≤ 2 ^ 64)
    (usedBound : used.toNat ≤ capacity.toNat)
    (inside : Codec.InSpan a (address + used) (capacity.toNat - used.toNat)) :
    address.toNat + used.toNat ≤ a.toNat ∧ a.toNat < address.toNat + capacity.toNat := by
  rcases inside with ⟨i, hi, same⟩
  bv_omega

theorem free_shrinks {a address used current capacity : BitVec 64}
    (lower : used.toNat ≤ current.toNat) (upper : current.toNat ≤ capacity.toNat)
    (inside : Codec.InSpan a (address + current) (capacity.toNat - current.toNat)) :
    Codec.InSpan a (address + used) (capacity.toNat - used.toNat) := by
  rcases inside with ⟨i, hi, same⟩
  refine ⟨current.toNat - used.toNat + i, by omega, ?_⟩
  bv_omega

theorem Owned.return_safe {s : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (owned : Owned s base r desc address capacity used ra bytes) :
    ∀ i < 8, ¬ Mutable s address used capacity bytes (s.regs.rsp.toBitVec + BitVec.ofNat 64 i) := by
  intro i hi writes
  have low := owned.stack.lowEnough
  have returnBound := owned.return_bound
  have position : s.regs.rsp.toNat ≤ (s.regs.rsp.toBitVec + BitVec.ofNat 64 i).toNat ∧
      (s.regs.rsp.toBitVec + BitVec.ofNat 64 i).toNat < s.regs.rsp.toNat + 8 := by bv_omega
  rcases writes with output | stack | cursor | arena
  · have atOutput := span_bounds owned.output_bound output
    have apart := owned.output_stack.nonempty (by decide) (by omega)
    omega
  · have atStack := stack_bounds low stack
    omega
  · have hb := owned.header_bound
    have atCursor : s.regs.rdx.toNat + 16 ≤ (s.regs.rsp.toBitVec + BitVec.ofNat 64 i).toNat ∧
        (s.regs.rsp.toBitVec + BitVec.ofNat 64 i).toNat < s.regs.rdx.toNat + 24 := by
      rcases cursor with ⟨j, hj, equal⟩
      bv_omega
    have apart := owned.header_stack.nonempty (by decide) (by omega)
    omega
  · have atArena := free_bounds owned.arena_bound owned.used_bound arena
    have nonempty : 0 < capacity.toNat - used.toNat := by omega
    have apart := owned.arena_stack.nonempty nonempty (by omega)
    omega

theorem Owned.header_safe {s : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (owned : Owned s base r desc address capacity used ra bytes) :
    ∀ i < 16, ¬ Mutable s address used capacity bytes (s.regs.rdx.toBitVec + BitVec.ofNat 64 i) := by
  intro i hi writes
  have low := owned.stack.lowEnough
  have hb := owned.header_bound
  have position : s.regs.rdx.toNat ≤ (s.regs.rdx.toBitVec + BitVec.ofNat 64 i).toNat ∧
      (s.regs.rdx.toBitVec + BitVec.ofNat 64 i).toNat < s.regs.rdx.toNat + 16 := by bv_omega
  rcases writes with output | stack | cursor | arena
  · have atOutput := span_bounds owned.output_bound output
    have apart := owned.header_output.nonempty (by decide) (by decide)
    omega
  · have atStack := stack_bounds low stack
    have apart := owned.header_stack.nonempty (by decide) (by omega)
    omega
  · rcases cursor with ⟨j, hj, equal⟩
    bv_omega
  · have atArena := free_bounds owned.arena_bound owned.used_bound arena
    have nonempty : 0 < capacity.toNat - used.toNat := by omega
    have apart := owned.arena_header.nonempty nonempty (by decide)
    omega

/-- A completed step's actual frame, retained mapping and observed cursor suffice
to re-establish the same original-entry physical resources at the new memory.
No execution or success of a later helper is assumed. -/
theorem Owned.transport {s : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra current : BitVec 64} {bytes : Nat}
    (owned : Owned s base r desc address capacity used ra bytes) (m : DataMem)
    (frame : Codec.MemoryFrame s.dmem m (Mutable s address used capacity bytes))
    (mapping : BitVector.Mapping.Extends s.dmem m)
    (lower : used.toNat ≤ current.toNat) (upper : current.toNat ≤ capacity.toNat)
    (cursor : widthLoad m (s.regs.rdx.toNat + 16) 8 = some current.toNat) :
    Owned {s with dmem := m} base r desc address capacity current ra bytes := by
  have protected : ∀ a, r a → ¬ Mutable s address used capacity bytes a := owned.readonly
  have mappedSpan (p : BitVec 64) (n : Nat) (hm : Large.Mapped s.dmem p n) : Large.Mapped m p n :=
    mapping p n hm
  have headerLoad (offset : Nat) (bound : offset + 8 ≤ 16) :
      Mem.loadInt m (s.regs.rdx.toBitVec + BitVec.ofNat 64 offset) 8 =
      Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 offset) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    have safe := owned.header_safe (offset + i) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at safe
    exact frame _ safe
  refine ⟨owned.descriptor.frame frame protected, ?_, owned.table_readonly,
    ⟨owned.stack.lowEnough, mappedSpan _ _ owned.stack.mapped⟩,
    owned.enough, owned.return_bound, ?_, owned.output_bound,
    mappedSpan _ _ owned.output_mapped, owned.output_stack,
    owned.header_bound, ?_, ?_, ?_, owned.header_output, owned.header_stack,
    owned.arena_bound, upper, owned.arena_nonzero, mappedSpan _ _ owned.arena_mapped,
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (frame _ (protected _ (owned.table_readonly i hi))).trans (owned.table i hi)
  · have same : Mem.loadInt m s.regs.rsp.toBitVec 8 = Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 := by
      apply memmove_loadInt_congr
      intro i hi
      exact frame _ (owned.return_safe i hi)
    exact same.trans owned.return_load
  · simpa using (headerLoad 0 (by decide)).trans owned.address_load
  · simpa using (headerLoad 8 (by decide)).trans owned.capacity_load
  · simpa only [width_address, BitVec.ofNat_toNat] using widthLoad_eq m _ _ _ cursor
  · have previous := owned.arena_output
    unfold Body.Apart at *
    omega
  · have previous := owned.arena_stack
    unfold Body.Apart at *
    omega
  · have previous := owned.arena_header
    unfold Body.Apart at *
    omega
  · intro a readonly write
    apply owned.readonly a readonly
    rcases write with output | stack | cursor | free
    · exact Or.inl output
    · exact Or.inr (Or.inl stack)
    · exact Or.inr (Or.inr (Or.inl cursor))
    · exact Or.inr (Or.inr (Or.inr (free_shrinks lower upper free)))

end SszX86.CodecMeasureFixed
