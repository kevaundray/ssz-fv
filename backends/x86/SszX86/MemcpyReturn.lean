import SszX86.MemcpyMemory

namespace SszX86

open Std.ExtHashMap
open List

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- If two exact-frame copies have the same source bytes and the same destination
length, then every address outside the destination image reads the same in both
memories. -/
theorem memcpy_lookup_eq_outside_dst
    {m t : DataMem} {src dst : BitVec 64}
    {xs old : List UInt8} {frame : DataMem}
    (hm : CopyMem m src dst xs old (Eq frame))
    (ht : CopyMem t src dst xs xs (Eq frame))
    (hlen : old.length = xs.length)
    {a : BitVec 64}
    (ha : a ∉ xs.At dst) :
    t.get? a = m.get? a := by
  have h_old : a ∉ old.At dst := by
    intro hmem
    apply ha
    simpa [mem_At_iff, hlen] using hmem
  have hm' : m = (old.At dst).union ((xs.At src).union frame) :=
    memcpy_memory_unique (m := m) (src := src) (dst := dst) (xs := xs)
      (old := old) (frame := frame) hm
  have ht' : t = (xs.At dst).union ((xs.At src).union frame) :=
    memcpy_memory_unique (m := t) (src := src) (dst := dst) (xs := xs)
      (old := xs) (frame := frame) ht
  rw [ht', hm']
  change ((xs.At dst) ∪ ((xs.At src) ∪ frame))[a]? =
    ((old.At dst) ∪ ((xs.At src) ∪ frame))[a]?
  rw [getElem?_union_of_not_mem_left ha]
  rw [getElem?_union_of_not_mem_left h_old]

/-- The return slot is preserved when only the destination and the return-slot
addresses are separated. Source may overlap the return slot; no frame hypothesis
mentions it. -/
theorem memcpy_loadBytes_eq_of_dst_sep
    {m t : DataMem} {src dst rsp : BitVec 64}
    {xs old : List UInt8} {frame : DataMem}
    (hm : CopyMem m src dst xs old (Eq frame))
    (ht : CopyMem t src dst xs xs (Eq frame))
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
  exact memcpy_lookup_eq_outside_dst (m := m) (t := t) (src := src) (dst := dst)
    (xs := xs) (old := old) (frame := frame) hm ht hlen (a := rsp + BitVec.ofNat 64 i)
    (by
      intro hmem
      rcases (mem_At_iff _ _ _).mp hmem with ⟨j, hj, hEq⟩
      exact (hsep i hi j hj) hEq)

/-- `ret` reads the same eight bytes after either copy, provided the return slot
is disjoint from the destination image. -/
theorem memcpy_loadInt_rsp_eq
    {m t : DataMem} {src dst rsp : BitVec 64}
    {xs old : List UInt8} {frame : DataMem}
    (hm : CopyMem m src dst xs old (Eq frame))
    (ht : CopyMem t src dst xs xs (Eq frame))
    (hlen : old.length = xs.length)
    (hsep : ∀ i < 8, ∀ j < xs.length,
      rsp + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j) :
    Mem.loadInt t rsp 8 = Mem.loadInt m rsp 8 := by
  simpa [Mem.loadInt] using congrArg (fun x => x.map Int.ofBytes)
    (memcpy_loadBytes_eq_of_dst_sep (m := m) (t := t) (src := src) (dst := dst)
      (rsp := rsp) (xs := xs) (old := old) (frame := frame) hm ht hlen 8 hsep)

end SszX86
