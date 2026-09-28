import SszX86.NatMulProductMemory

namespace SszX86.NatMul.Product
open SszNative
open UintCodec

theorem RowFrame.read_disjoint {before after : DataMem} {dst source : BitVec 64}
    {index count capacity sourceCapacity start : Nat} {words : List (BitVec 64)}
    (frame : RowFrame before after dst index count)
    (read : ReadAt before source start words)
    (apart : Large.Disjoint source dst sourceCapacity capacity)
    (writeBound : 8*(index+count) ≤ capacity)
    (sourceBound : 8*(start+words.length) ≤ sourceCapacity) :
    ReadAt after source start words := by
  intro j
  have same : Mem.loadInt after (source + BitVec.ofNat 64 (8*(start+j.val))) 8 =
      Mem.loadInt before (source + BitVec.ofNat 64 (8*(start+j.val))) 8 := by
    apply memmove_loadInt_congr
    intro a ha
    apply frame
    intro b _ hb
    rw [memmove_addr_add]
    exact apart (8*(start+j.val)+a) (by have := j.isLt; omega) b (by omega)
  rw [same]
  exact read j

/-- These are the three real locals repeatedly read by PC512 and PC639. -/
structure Locals (m : DataMem) (sp leftPointer payload dst : BitVec 64) : Prop where
  payload : Mem.loadInt m sp 8 = some (payload.toNat : Int)
  destination : Mem.loadInt m (sp+8#64) 8 = some (dst.toNat : Int)
  left : Mem.loadInt m (sp+16#64) 8 = some (leftPointer.toNat : Int)

theorem Locals.preserve {before after : DataMem} {sp leftPointer payload dst : BitVec 64}
    {count : Nat} (locals : Locals before sp leftPointer payload dst)
    (frame : BufferFrame before after dst.toNat count)
    (span : sp.toNat+24 ≤ 2^64) (apart : Body.Apart sp.toNat 24 dst.toNat count) :
    Locals after sp leftPointer payload dst := by
  have load (offset : Nat) (inside : offset+8 ≤ 24) :
      Mem.loadInt after (sp + BitVec.ofNat 64 offset) 8 =
        Mem.loadInt before (sp + BitVec.ofNat 64 offset) 8 := by
    have natural : (sp + BitVec.ofNat 64 offset).toNat = sp.toNat+offset := by bv_omega
    apply frame.load
    · rw [natural]; omega
    · rw [natural]; unfold Body.Apart at *; omega
  constructor
  · simpa using (load 0 (by decide)).trans locals.payload
  · exact (load 8 (by decide)).trans locals.destination
  · exact (load 16 (by decide)).trans locals.left

/-- Concatenate one final low word with the still-live row suffix. -/
theorem ReadAt.cons {m : DataMem} {dst : BitVec 64} {index : Nat}
    {word : BitVec 64} {words : List (BitVec 64)}
    (head : Mem.loadInt m (dst+BitVec.ofNat 64 (8*index)) 8 = some (word.toNat : Int))
    (tail : ReadAt m dst (index+1) words) : ReadAt m dst index (word::words) := by
  intro j
  by_cases zero : j.val = 0
  · simpa [zero] using head
  · have bound : j.val-1 < words.length := by have := j.isLt; simp only [List.length_cons] at this; omega
    have eq : j.val = (j.val-1)+1 := by omega
    simpa [eq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail ⟨j.val-1, bound⟩

theorem RowFrame.head {before after : DataMem} {dst : BitVec 64} {index count : Nat}
    (frame : RowFrame before after dst (index+1) count)
    (span : dst.toNat+8*(index+1+count) ≤ 2^64) :
    Mem.loadInt after (dst+BitVec.ofNat 64 (8*index)) 8 =
      Mem.loadInt before (dst+BitVec.ofNat 64 (8*index)) 8 := by
  apply memmove_loadInt_congr
  intro a ha
  apply frame
  intro j lo hi same
  rw [memmove_addr_add] at same
  have inject := memmove_addr_injective dst (8*(index+1+count))
    (8*index+a) j span (by omega) (by omega) same
  omega

theorem fill_mapped (m : DataMem) (dst : BitVec 64) (index count : Nat)
    (words : List (BitVec 64)) (hmapped : Large.Mapped m dst count) :
    Large.Mapped (Large.fillMem m dst index words) dst count := by
  induction words generalizing m index with
  | nil => exact hmapped
  | cons word words ih =>
    exact ih _ _ (Large.mapped_store _ _ _ _ _ _ hmapped)

end SszX86.NatMul.Product
