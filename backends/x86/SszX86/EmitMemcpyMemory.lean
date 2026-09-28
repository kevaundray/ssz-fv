import SszX86.EmitMemcpyEmbedded

namespace SszX86.Emit
open Std.ExtHashMap
open UintCodec

/-- Extracting a finite observed submap leaves its exact original complement. -/
theorem split_memory (m part : DataMem)
    (agrees : ∀ a, a ∈ part → m.get? a = part.get? a) :
    m =⋆ Eq part ⋆ Eq (m \ part) := by
  refine ⟨part, m \ part, ?_, ?_, rfl, rfl⟩
  · apply ext_getElem?
    intro a
    rw [union_eq, getElem?_union]
    change ((m \ part).get? a).or (part.get? a) = m.get? a
    rw [get?_diff]
    by_cases inside : a ∈ part
    · simpa only [inside, ↓reduceIte, Option.none_or] using (agrees a inside).symm
    · have absent : part.get? a = none := getElem?_eq_none inside
      simp only [inside, ↓reduceIte, absent, Option.or_none]
  · rw [eq_empty_iff_forall_not_mem]
    intro a
    simp only [inter_eq, mem_inter_iff, mem_diff_iff]
    rintro ⟨inside, _, outside⟩
    exact outside inside

def ListBytesAt (m : DataMem) (p : BitVec 64) (bytes : List UInt8) : Prop :=
  ∀ i, i < bytes.length → m.get? (p + BitVec.ofNat 64 i) = bytes[i]?

theorem bytes_submap (m : DataMem) (p : BitVec 64) (bytes : List UInt8)
    (bound : bytes.length ≤ 2 ^ 64) (stored : ListBytesAt m p bytes) :
    ∀ a, a ∈ bytes.At p → m.get? a = (bytes.At p).get? a := by
  intro a inside
  obtain ⟨i, hi, rfl⟩ := (mem_At_iff bytes p a).1 inside
  rw [get?_At_idx bytes p i (by omega) bound]
  exact stored i hi

/-- Source and destination separation is needed, not separation of all readonly
objects. The old destination bytes are arbitrary and are existentially extracted. -/
theorem copy_memory_of_bytes (m : DataMem) (src dst : BitVec 64)
    (bytes old : List UInt8) (length : old.length = bytes.length)
    (bound : bytes.length < 2 ^ 64)
    (source : ListBytesAt m src bytes) (destination : ListBytesAt m dst old)
    (apart : Large.Disjoint src dst bytes.length bytes.length) :
    CopyMem m src dst bytes old (Eq ((m \ old.At dst) \ bytes.At src)) := by
  have outer := split_memory m (old.At dst)
    (bytes_submap m dst old (by omega) destination)
  have inner : (m \ old.At dst) =⋆ Eq (bytes.At src) ⋆ Eq ((m \ old.At dst) \ bytes.At src) := by
    apply split_memory
    intro a inside
    have absent : a ∉ old.At dst := by
      obtain ⟨i, hi, rfl⟩ := (mem_At_iff bytes src a).1 inside
      intro inDestination
      obtain ⟨j, hj, equal⟩ := (mem_At_iff old dst _).1 inDestination
      exact apart i hi j (by omega) equal
    rw [get?_diff_of_not_mem_right absent]
    exact bytes_submap m src bytes (by omega) source a inside
  rcases outer with ⟨a, b, union, disjoint, rfl, rfl⟩
  exact ⟨old.At dst, m \ old.At dst, union, disjoint, rfl, inner⟩

def oldBytes (m : DataMem) (p : BitVec 64) (size : Nat) : List UInt8 :=
  (List.range size).map (fun i => (m.get? (p + BitVec.ofNat 64 i)).getD 0)

theorem oldBytes_length (m : DataMem) (p : BitVec 64) (size : Nat) :
    (oldBytes m p size).length = size := by
  simp only [oldBytes, List.length_map, List.length_range]

theorem oldBytes_at (m : DataMem) (p : BitVec 64) (size : Nat)
    (hmap : Large.Mapped m p size) : ListBytesAt m p (oldBytes m p size) := by
  intro i hi
  have within : i < size := by simpa only [oldBytes_length] using hi
  obtain ⟨byte, read⟩ := hmap i within
  simp only [get?_eq_getElem?] at read
  simp only [List.getElem?_eq_getElem hi]
  simp [oldBytes, read]

theorem copy_memory_of_mapped (m : DataMem) (src dst : BitVec 64)
    (bytes : List UInt8) (bound : bytes.length < 2 ^ 64)
    (source : ListBytesAt m src bytes) (hmap : Large.Mapped m dst bytes.length)
    (apart : Large.Disjoint src dst bytes.length bytes.length) :
    ∃ old frame, old.length = bytes.length ∧ CopyMem m src dst bytes old (Eq frame) := by
  let old := oldBytes m dst bytes.length
  refine ⟨old, (m \ old.At dst) \ bytes.At src, oldBytes_length _ _ _, ?_⟩
  exact copy_memory_of_bytes m src dst bytes old (oldBytes_length _ _ _) bound
    source (oldBytes_at _ _ _ hmap) apart

theorem listBytesAt_of_sep (m : DataMem) (p : BitVec 64) (bytes : List UInt8)
    (R : DataMem → Prop) (bound : bytes.length ≤ 2 ^ 64)
    (owned : m =⋆ Eq (bytes.At p) ⋆ R) : ListBytesAt m p bytes := by
  rcases owned with ⟨part, frame, union, disjoint, rfl, _⟩
  intro i hi
  rw [← union, union_comm_of_disjoint _ _ disjoint]
  have byte := get?_At_idx bytes p i (by omega) bound
  simp only [get?_eq_getElem?] at byte
  simp only [get?_eq_getElem?, union_eq, getElem?_union, byte,
    List.getElem?_eq_getElem hi, Option.some_or]

end SszX86.Emit
