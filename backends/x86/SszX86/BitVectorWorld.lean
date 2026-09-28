import SszX86.BitVectorRebase
import SszX86.BitVectorHelperFrames

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- Exact arena write spans, separate from the caller's fixed work permissions. -/
def WriteFrame (s : MachineData) (before after : DataMem) (writes : List (Nat × Nat)) : Prop :=
  ∀ a : BitVec 64,
    Body.Outside a.toNat s.regs.rdi.toNat 80 →
    Body.Outside a.toNat (workStart s) workSize →
    Body.Outside a.toNat (s.regs.rbx.toNat + 16) 8 →
    (∀ span ∈ writes, Body.Outside a.toNat span.1 span.2) →
    after.get? a = before.get? a

theorem WriteFrame.refl (s : MachineData) (m : DataMem) : WriteFrame s m m [] :=
  fun _ _ _ _ _ => rfl

theorem WriteFrame.trans {s : MachineData} {first second third : DataMem}
    {left right : List (Nat × Nat)} (before : WriteFrame s first second left)
    (after : WriteFrame s second third right) : WriteFrame s first third (left ++ right) := by
  intro a output work cursor outside
  exact (after a output work cursor (fun span member => outside span (List.mem_append_right _ member))).trans
    (before a output work cursor (fun span member => outside span (List.mem_append_left _ member)))

theorem WriteFrame.of_regions {s : MachineData} {before after : DataMem} {writes : List (Nat × Nat)}
    (frame : RegionsFrame before after
      ([(s.regs.rdi.toNat, 80), (workStart s, workSize), (s.regs.rbx.toNat + 16, 8)] ++ writes)) :
    WriteFrame s before after writes := by
  intro a output work cursor outside
  apply frame a
  intro span member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl) | member
  · exact output
  · exact work
  · exact cursor
  · exact outside span member

theorem WriteFrame.stable {s : MachineData} {before after : DataMem}
    {address capacity used : BitVec 64} {writes : List (Nat × Nat)}
    (frame : WriteFrame s before after writes)
    (usedBound : used.toNat ≤ capacity.toNat)
    (inside : ∀ span ∈ writes, address.toNat + used.toNat ≤ span.1 ∧
      span.1 + span.2 ≤ address.toNat + capacity.toNat) :
    StableFrame {s with dmem := before} address capacity used after := by
  intro a outside
  apply frame a
  · exact outside (s.regs.rdi.toNat, 80) (by simp)
  · exact outside (workStart s, workSize) (by simp [workStart])
  · exact outside (s.regs.rbx.toNat + 16, 8) (by simp)
  · intro span member
    have free := outside (address.toNat + used.toNat, capacity.toNat - used.toNat) (by simp)
    obtain ⟨start, finish⟩ := inside span member
    unfold Body.Outside at *
    omega

/-- Every reached world has actual physical metadata and cursor observations.
Recorded spans only describe executed helper stores; no future allocation is
assumed, and charged alignment padding is never added to the write frame. -/
structure World (s : MachineData) (saved : Saved) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity initialUsed currentUsed : BitVec 64) (writes : List (Nat × Nat))
    (m : DataMem) : Prop where
  physical : Owned {s with dmem := m} saved length data address capacity currentUsed
  mapping : Mapping.Extends s.dmem m
  frame : WriteFrame s s.dmem m writes
  progress : initialUsed.toNat ≤ currentUsed.toNat
  inside : ∀ span ∈ writes, address.toNat + initialUsed.toNat ≤ span.1 ∧
    span.1 + span.2 ≤ address.toNat + capacity.toNat

theorem World.initial (s : MachineData) (saved : Saved) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (owned : Owned s saved length data address capacity used) :
    World s saved length data address capacity used used [] s.dmem := by
  refine ⟨?_, Mapping.Extends.refl _, WriteFrame.refl _ _, Nat.le_refl _, ?_⟩
  · simpa only using owned
  · intro span member
    simp only [List.not_mem_nil] at member

theorem World.advance {s : MachineData} {saved : Saved} {length : NatOperand} {data : Ssz.Bytes}
    {address capacity initialUsed currentUsed next : BitVec 64} {writes additions : List (Nat × Nat)}
    {before after : DataMem}
    (world : World s saved length data address capacity initialUsed currentUsed writes before)
    (frame : WriteFrame s before after additions) (mapping : Mapping.Extends before after)
    (inside : ∀ span ∈ additions, address.toNat + currentUsed.toNat ≤ span.1 ∧
      span.1 + span.2 ≤ address.toNat + capacity.toNat)
    (progress : currentUsed.toNat ≤ next.toNat) (bound : next.toNat ≤ capacity.toNat)
    (cursor : Mem.loadInt after (s.regs.rbx.toBitVec + 16) 8 = some (next.toNat : Int)) :
    World s saved length data address capacity initialUsed next (writes ++ additions) after := by
  have stable := frame.stable world.physical.used_bound inside
  have physical := Owned.rebase {s with dmem := before} saved length data address capacity currentUsed next
    world.physical after stable mapping progress bound cursor
  refine ⟨?_, world.mapping.trans mapping, world.frame.trans frame,
    Nat.le_trans world.progress progress, ?_⟩
  · simpa only using physical
  · intro span member
    rcases List.mem_append.mp member with member | member
    · exact world.inside span member
    · obtain ⟨start, finish⟩ := inside span member
      exact ⟨by have := world.progress; omega, finish⟩

end SszX86.BitVector
