import SszX86.MemsetMemory

namespace SszX86

open Std.ExtHashMap
open List

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- If two exact-frame fills have the same destination bytes and the same
length, then every address outside the destination image reads the same in both
memories. -/
theorem memset_lookup_eq_outside_dst
    {m t : DataMem} {dst : BitVec 64}
    {xs old : List UInt8} {frame : DataMem}
    (hm : FillMem m dst old (Eq frame))
    (ht : FillMem t dst xs (Eq frame))
    (hlen : old.length = xs.length)
    {a : BitVec 64}
    (ha : a ∉ xs.At dst) :
    t.get? a = m.get? a := by
  have h_old : a ∉ old.At dst := by
    intro hmem
    apply ha
    simpa [mem_At_iff, hlen] using hmem
  have hm' : m = (old.At dst).union frame :=
    memset_memory_unique m dst old frame hm
  have ht' : t = (xs.At dst).union frame :=
    memset_memory_unique t dst xs frame ht
  rw [ht', hm']
  change (xs.At dst ∪ frame)[a]? = (old.At dst ∪ frame)[a]?
  rw [getElem?_union_of_not_mem_left ha]
  rw [getElem?_union_of_not_mem_left h_old]

/-- The return slot is preserved when only the destination and the return-slot
addresses are separated. The destination may alias nothing in the return slot.
-/
theorem memset_loadBytes_eq_of_dst_sep
    {m t : DataMem} {dst rsp : BitVec 64}
    {xs old : List UInt8} {frame : DataMem}
    (hm : FillMem m dst old (Eq frame))
    (ht : FillMem t dst xs (Eq frame))
    (hlen : old.length = xs.length)
    (n : Nat)
    (hsep : ∀ i < n, ∀ j < xs.length,
      rsp + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j) :
    Mem.loadBytes t rsp n = Mem.loadBytes m rsp n := by
  unfold Mem.loadBytes
  apply congrArg List.allSome
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact memset_lookup_eq_outside_dst (m := m) (t := t) (dst := dst)
    (xs := xs) (old := old) (frame := frame) hm ht hlen (a := rsp + BitVec.ofNat 64 i)
    (by
      intro hmem
      rcases (mem_At_iff _ _ _).mp hmem with ⟨j, hj, hEq⟩
      exact (hsep i hi j hj) hEq)

/-- `ret` reads the same eight bytes after either fill, provided the return slot
is disjoint from the destination image. -/
theorem memset_loadInt_rsp_eq
    {m t : DataMem} {dst rsp : BitVec 64}
    {xs old : List UInt8} {frame : DataMem}
    (hm : FillMem m dst old (Eq frame))
    (ht : FillMem t dst xs (Eq frame))
    (hlen : old.length = xs.length)
    (hsep : ∀ i < 8, ∀ j < xs.length,
      rsp + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j) :
    Mem.loadInt t rsp 8 = Mem.loadInt m rsp 8 := by
  simpa [Mem.loadInt] using congrArg (fun x => x.map Int.ofBytes)
    (memset_loadBytes_eq_of_dst_sep (m := m) (t := t) (dst := dst)
      (rsp := rsp) (xs := xs) (old := old) (frame := frame) hm ht hlen 8 hsep)

end SszX86
