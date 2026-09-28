import SszX86.BitVectorWorld
import SszX86.BitVectorCall

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem World.local {s : MachineData} {saved : Saved} {length : NatOperand} {data : Ssz.Bytes}
    {address capacity initialUsed currentUsed : BitVec 64} {writes : List (Nat × Nat)}
    {before after : DataMem}
    (world : World s saved length data address capacity initialUsed currentUsed writes before)
    (frame : RegionsFrame before after [(workStart s, workSize)])
    (mapping : Mapping.Extends before after) :
    World s saved length data address capacity initialUsed currentUsed writes after := by
  have localFrame : WriteFrame s before after [] := by
    intro a _ work _ _
    apply frame a
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    exact work
  have cursorKept := frame.load (s.regs.rbx.toNat + 16) 8
    (by have h := world.physical.header_bound; change s.regs.rbx.toNat + 24 ≤ 2^64 at h; omega)
    (by
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      have apart : Body.Apart s.regs.rbx.toNat 24 (workStart s) workSize := world.physical.header_work
      unfold Body.Apart at *
      omega)
  have cursor : Mem.loadInt after (s.regs.rbx.toBitVec + 16) 8 = some (currentUsed.toNat : Int) := by
    change Mem.loadInt after (BitVec.ofNat 64 (s.regs.rbx.toBitVec.toNat + 16)) 8 =
      Mem.loadInt before (BitVec.ofNat 64 (s.regs.rbx.toBitVec.toNat + 16)) 8 at cursorKept
    rw [width_address] at cursorKept
    exact cursorKept.trans world.physical.used_load
  have next := world.advance localFrame mapping (by intro span member; simp at member)
    (Nat.le_refl _) world.physical.used_bound cursor
  simpa only [List.append_nil] using next

theorem work_store_regions (s : MachineData) (m : DataMem) (destination : BitVec 64)
    (count : Nat) (value : Int)
    (start : workStart s ≤ destination.toNat)
    (finish : destination.toNat + count ≤ workStart s + workSize)
    (bound : destination.toNat + count ≤ 2^64) :
    RegionsFrame m (Mem.storeInt m destination count value) [(workStart s, workSize)] := by
  apply (store_regions_frame m destination count value bound).cover
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  exact ⟨(workStart s, workSize), by simp, start, finish⟩

theorem World.store {s : MachineData} {saved : Saved} {length : NatOperand} {data : Ssz.Bytes}
    {address capacity initialUsed currentUsed : BitVec 64} {writes : List (Nat × Nat)} {m : DataMem}
    (world : World s saved length data address capacity initialUsed currentUsed writes m)
    (destination : BitVec 64) (count : Nat) (value : Int)
    (start : workStart s ≤ destination.toNat)
    (finish : destination.toNat + count ≤ workStart s + workSize)
    (bound : destination.toNat + count ≤ 2^64) :
    World s saved length data address capacity initialUsed currentUsed writes
      (Mem.storeInt m destination count value) :=
  world.local (work_store_regions s m destination count value start finish bound)
    (Mapping.Extends.store m destination count value)

/-- The real CALL return-word store remains inside the caller's work interval. -/
theorem World.call {s u : MachineData} {saved : Saved} {length : NatOperand} {data : Ssz.Bytes}
    {address capacity initialUsed currentUsed : BitVec 64} {writes : List (Nat × Nat)}
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (stack : u.regs.rsp = s.regs.rsp) (ra : BitVec 64) :
    World s saved length data address capacity initialUsed currentUsed writes (callState u ra).dmem := by
  have low : 72 ≤ s.regs.rsp.toBitVec.toNat := world.physical.stack_low
  have high : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := world.physical.stack_bound
  apply world.local
  · intro a outside
    apply NatDivision.call_frame u ra a
    intro i hi
    have separated := outside (workStart s, workSize) (by simp)
    change Body.Outside a.toNat (s.regs.rsp.toBitVec.toNat - 72) 296 at separated
    rw [stack]
    unfold Body.Outside at separated
    bv_omega
  · exact Mapping.Extends.store u.dmem (u.regs.rsp.toBitVec - 8) 8 ra.toInt

end SszX86.BitVector
