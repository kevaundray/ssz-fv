import SszX86.MemcpyMemory

namespace SszX86

open Std.ExtHashMap

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The original source snapshot and the mapped destination. Kraken's data
memory has no separate permission bits: successful destination loads are the
mapping precondition of `MachineData.store`. The two ranges may overlap, and
an empty range imposes no mapping requirement on its pointer. The bounds permit
an endpoint equal to `2^64`; only addresses strictly inside a range are read. -/
structure MoveInput (m0 : DataMem) (src dst : BitVec 64) (n : Nat)
    (xs : List UInt8) : Prop where
  length : xs.length = n
  src_bound : src.toNat + n ≤ 2^64
  dst_bound : dst.toNat + n ≤ 2^64
  source : ∀ i < n, m0.get? (src + BitVec.ofNat 64 i) = xs[i]?
  destination : ∀ i < n, ∃ b, m0.get? (dst + BitVec.ofNat 64 i) = some b

/-- Precisely the destination interval `[lo, hi)` has been copied from the
original snapshot. Every other address, mapped or unmapped, has its original
lookup. In particular this does not incorrectly frame an overlapping source. -/
structure MoveInv (m m0 : DataMem) (dst : BitVec 64)
    (xs : List UInt8) (lo hi : Nat) : Prop where
  ordered : lo ≤ hi
  bounded : hi ≤ xs.length
  copied : ∀ i, lo ≤ i → i < hi → m.get? (dst + BitVec.ofNat 64 i) = xs[i]?
  frame : ∀ a, (∀ i, lo ≤ i → i < hi → a ≠ dst + BitVec.ofNat 64 i) →
    m.get? a = m0.get? a

abbrev MoveForward (m m0 : DataMem) (dst : BitVec 64) (xs : List UInt8) (k : Nat) :=
  MoveInv m m0 dst xs 0 k

abbrev MoveBackward (m m0 : DataMem) (dst : BitVec 64) (xs : List UInt8) (k : Nat) :=
  MoveInv m m0 dst xs (xs.length - k) xs.length

/-- Pointer advancement is modular even when the final endpoint wraps. -/
theorem memmove_addr_add (p : BitVec 64) (i j : Nat) :
    (p + BitVec.ofNat 64 i) + BitVec.ofNat 64 j = p + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- Only actual accesses, not the endpoint, need a strict nonwrapping bound. -/
theorem memmove_addr_toNat (p : BitVec 64) (i : Nat)
    (h : p.toNat + i < 2^64) :
    (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show i < 2^64 by omega), Nat.mod_eq_of_lt h]

theorem memmove_addr_injective (p : BitVec 64) (n i j : Nat)
    (hb : p.toNat + n ≤ 2^64) (hi : i < n) (hj : j < n)
    (h : p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 j) : i = j := by
  have he := congrArg BitVec.toNat h
  rw [memmove_addr_toNat p i (by omega), memmove_addr_toNat p j (by omega)] at he
  omega

/-- The low-level store really overwrites each mapped-image lookup. -/
theorem memmove_store_lookup_inside (m : DataMem) (p : BitVec 64)
    (bs : List UInt8) (i : Nat) (hi : i < bs.length) (hb : bs.length ≤ 2^64) :
    (Mem.storeBytes m p bs).get? (p + BitVec.ofNat 64 i) = bs[i]? := by
  have h := get?_At_idx bs p i (by omega) hb
  rw [get?_eq_getElem?] at h
  simp only [Mem.storeBytes, get?_eq_getElem?, union_eq, getElem?_union]
  rw [h, List.getElem?_eq_getElem hi]
  rfl

/-- The low-level store leaves every address outside its byte image unchanged. -/
theorem memmove_store_lookup_outside (m : DataMem) (p a : BitVec 64)
    (bs : List UInt8)
    (h : ∀ i < bs.length, a ≠ p + BitVec.ofNat 64 i) :
    (Mem.storeBytes m p bs).get? a = m.get? a := by
  change (m ∪ bs.At p)[a]? = m[a]?
  apply getElem?_union_of_not_mem_right
  intro ha
  rcases (mem_At_iff bs p a).mp ha with ⟨i, hi, he⟩
  exact h i hi he

private theorem memmove_mapM_some {α : Type} (xs acc : List α) :
    List.mapM.loop id (xs.map some) acc = some (acc.reverse ++ xs) := by
  induction xs generalizing acc <;> simp_all [List.mapM.loop]

private theorem memmove_allSome_some {α : Type} (xs : List α) :
    List.allSome (xs.map some) = some xs := by
  exact memmove_mapM_some xs []

private theorem memmove_range_lookup {α : Type} (xs : List α) :
    (List.range xs.length).map (fun i => xs[i]?) = xs.map some := by
  apply List.ext_get <;> simp

/-- Equality at precisely the accessed addresses preserves a byte load. -/
theorem memmove_loadBytes_congr {m m0 : DataMem} {p : BitVec 64} {k : Nat}
    (h : ∀ i < k, m.get? (p + BitVec.ofNat 64 i) =
      m0.get? (p + BitVec.ofNat 64 i)) :
    Mem.loadBytes m p k = Mem.loadBytes m0 p k := by
  unfold Mem.loadBytes
  apply congrArg List.allSome
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

theorem memmove_loadInt_congr {m m0 : DataMem} {p : BitVec 64} {k : Nat}
    (h : ∀ i < k, m.get? (p + BitVec.ofNat 64 i) =
      m0.get? (p + BitVec.ofNat 64 i)) :
    Mem.loadInt m p k = Mem.loadInt m0 p k := by
  exact congrArg (fun bs => bs.map Int.ofBytes) (memmove_loadBytes_congr h)

/-- Pointwise mapped-byte facts imply the actual Kraken byte load. -/
theorem memmove_loadBytes_of_lookup (m : DataMem) (p : BitVec 64)
    (bs : List UInt8)
    (h : ∀ i < bs.length, m.get? (p + BitVec.ofNat 64 i) = bs[i]?) :
    Mem.loadBytes m p bs.length = some bs := by
  unfold Mem.loadBytes
  rw [show (List.range bs.length).map (fun i => m.get? (p + BitVec.ofNat 64 i)) =
      (List.range bs.length).map (fun i => bs[i]?) by
    apply List.map_congr_left
    intro i hi
    exact h i (List.mem_range.mp hi)]
  rw [memmove_range_lookup, memmove_allSome_some]

theorem memmove_loadInt_of_lookup (m : DataMem) (p : BitVec 64)
    (bs : List UInt8)
    (h : ∀ i < bs.length, m.get? (p + BitVec.ofNat 64 i) = bs[i]?) :
    Mem.loadInt m p bs.length = some (Int.ofBytes bs) := by
  simp only [Mem.loadInt, memmove_loadBytes_of_lookup m p bs h, Option.map_some]

/-- A mapped byte at each access suffices for the old-value load demanded by
`MachineData.store`; the old bytes need not be the original destination bytes. -/
theorem memmove_loadInt_exists (m : DataMem) (p : BitVec 64) (n : Nat)
    (h : ∀ i < n, ∃ b, m.get? (p + BitVec.ofNat 64 i) = some b) :
    ∃ v, Mem.loadInt m p n = some v := by
  let bs := (List.range n).map (fun i => (m.get? (p + BitVec.ofNat 64 i)).getD 0)
  have hlen : bs.length = n := by simp [bs]
  have hlookup : ∀ i < bs.length, m.get? (p + BitVec.ofNat 64 i) = bs[i]? := by
    intro i hi
    have hin : i < n := by simpa [hlen] using hi
    obtain ⟨b, hb⟩ := h i hin
    change m[p + BitVec.ofNat 64 i]? = some b at hb
    rw [List.getElem?_eq_getElem hi]
    simp [bs, hb]
  exact ⟨Int.ofBytes bs, by simpa only [hlen] using memmove_loadInt_of_lookup m p bs hlookup⟩

/-- Snapshot slices have exactly the requested width, including width zero. -/
theorem memmove_chunk_length (xs : List UInt8) (t c : Nat)
    (h : t + c ≤ xs.length) : ((xs.drop t).take c).length = c := by
  apply List.length_take_of_le
  simp only [List.length_drop]
  omega

theorem memmove_chunk_lookup (xs : List UInt8) (t c i : Nat) (hi : i < c) :
    ((xs.drop t).take c)[i]? = xs[t + i]? := by
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop]

/-- The empty copied interval is the original memory, without requiring any
pointer to be mapped. -/
theorem memmove_init (m0 : DataMem) (dst : BitVec 64) (xs : List UInt8)
    (k : Nat) (hk : k ≤ xs.length) : MoveInv m0 m0 dst xs k k := by
  refine ⟨Nat.le_refl _, hk, ?_, ?_⟩
  · intro i hlo hhi
    omega
  · intro a _
    rfl

/-- Mapped destination bytes stay mapped under either directional invariant. -/
theorem memmove_destination_mapped {m m0 : DataMem} {src dst : BitVec 64}
    {n : Nat} {xs : List UInt8} {lo hi : Nat}
    (input : MoveInput m0 src dst n xs) (inv : MoveInv m m0 dst xs lo hi)
    (i : Nat) (hi' : i < n) :
    ∃ b, m.get? (dst + BitVec.ofNat 64 i) = some b := by
  by_cases hc : lo ≤ i ∧ i < hi
  · have hil : i < xs.length := by have := input.length; omega
    exact ⟨xs[i], (inv.copied i hc.1 hc.2).trans (List.getElem?_eq_getElem hil)⟩
  · rw [inv.frame (dst + BitVec.ofNat 64 i) (by
      intro j hjlo hjhi he
      have hij := memmove_addr_injective dst n i j input.dst_bound hi' (by
        have := inv.bounded
        have := input.length
        omega) he
      subst j
      exact hc ⟨hjlo, hjhi⟩)]
    exact input.destination i hi'

/-- Forward copying cannot overwrite an unread source byte, even if the ranges
partially overlap. -/
theorem memmove_forward_unread {m m0 : DataMem} {src dst : BitVec 64}
    {n k : Nat} {xs : List UInt8}
    (input : MoveInput m0 src dst n xs) (direction : dst.toNat ≤ src.toNat)
    (inv : MoveInv m m0 dst xs 0 k) (i : Nat) (hki : k ≤ i) (hin : i < n) :
    m.get? (src + BitVec.ofNat 64 i) = m0.get? (src + BitVec.ofNat 64 i) := by
  apply inv.frame
  intro j _ hj he
  have hnum := congrArg BitVec.toNat he
  rw [memmove_addr_toNat src i (by have := input.src_bound; omega),
    memmove_addr_toNat dst j (by have := input.dst_bound; omega)] at hnum
  omega

/-- Backward copying protects precisely the source prefix that has not yet
been read. This uses unsigned address order and both nonwrapping bounds. -/
theorem memmove_backward_unread {m m0 : DataMem} {src dst : BitVec 64}
    {n k : Nat} {xs : List UInt8}
    (input : MoveInput m0 src dst n xs) (direction : src.toNat ≤ dst.toNat)
    (inv : MoveInv m m0 dst xs (n - k) n) (i : Nat) (hi : i < n - k) :
    m.get? (src + BitVec.ofNat 64 i) = m0.get? (src + BitVec.ofNat 64 i) := by
  apply inv.frame
  intro j hjlo hjhi he
  have hnum := congrArg BitVec.toNat he
  rw [memmove_addr_toNat src i (by have := input.src_bound; omega),
    memmove_addr_toNat dst j (by have := input.dst_bound; omega)] at hnum
  omega

/-- Extend an exact copied interval by a snapshot chunk. The interval equation
is purely arithmetic; all load/store and lookup behavior is proved here. -/
theorem memmove_store_join {m m0 : DataMem} {dst : BitVec 64}
    {xs : List UInt8} {lo hi lo' hi' t c : Nat}
    (inv : MoveInv m m0 dst xs lo hi)
    (hb : dst.toNat + xs.length ≤ 2^64)
    (hlo : lo' ≤ hi') (hhi : hi' ≤ xs.length) (hc : t + c ≤ xs.length)
    (join : ∀ i, (lo' ≤ i ∧ i < hi') ↔
      ((lo ≤ i ∧ i < hi) ∨ (t ≤ i ∧ i < t + c))) :
    MoveInv (Mem.storeBytes m (dst + BitVec.ofNat 64 t) ((xs.drop t).take c))
      m0 dst xs lo' hi' := by
  have hlen := memmove_chunk_length xs t c hc
  refine ⟨hlo, hhi, ?_, ?_⟩
  · intro i hilo hihi
    by_cases hchunk : t ≤ i ∧ i < t + c
    · have hij : i - t < ((xs.drop t).take c).length := by omega
      have he : dst + BitVec.ofNat 64 i =
          (dst + BitVec.ofNat 64 t) + BitVec.ofNat 64 (i - t) := by
        rw [memmove_addr_add]
        congr 2
        omega
      rw [he, memmove_store_lookup_inside m _ _ (i - t) hij (by omega),
        memmove_chunk_lookup xs t c (i - t) (by omega)]
      congr 1
      omega
    · rw [memmove_store_lookup_outside m _ _ _ (by
        intro j hj he
        rw [memmove_addr_add] at he
        have hij := memmove_addr_injective dst xs.length i (t + j) hb
          (by omega) (by omega) he
        apply hchunk
        omega)]
      rcases (join i).mp ⟨hilo, hihi⟩ with hold | hnew
      · exact inv.copied i hold.1 hold.2
      · exact False.elim (hchunk hnew)
  · intro a ha
    rw [memmove_store_lookup_outside m _ _ _ (by
      intro j hj he
      rw [memmove_addr_add] at he
      have hnew := (join (t + j)).mpr (Or.inr (by omega))
      exact ha (t + j) hnew.1 hnew.2 he)]
    apply inv.frame
    intro i hilo hihi
    have hnew := (join i).mpr (Or.inl ⟨hilo, hihi⟩)
    exact ha i hnew.1 hnew.2

/-- A forward chunk is loaded entirely from the original snapshot before its
store. No separation between source and destination is assumed. This theorem
works at width one, width eight, and every other bounded width. -/
theorem memmove_forward_chunk {m m0 : DataMem} {src dst : BitVec 64}
    {n : Nat} {xs : List UInt8} (input : MoveInput m0 src dst n xs)
    (direction : dst.toNat ≤ src.toNat) (k c : Nat) (hk : k + c ≤ n)
    (inv : MoveInv m m0 dst xs 0 k) :
    Mem.loadInt m (src + BitVec.ofNat 64 k) c =
      some (Int.ofBytes ((xs.drop k).take c)) ∧
    (∃ old, Mem.loadInt m (dst + BitVec.ofNat 64 k) c = some old) ∧
    MoveInv (Mem.storeBytes m (dst + BitVec.ofNat 64 k) ((xs.drop k).take c))
      m0 dst xs 0 (k + c) := by
  have hlen := memmove_chunk_length xs k c (by have := input.length; omega)
  refine ⟨?_, ?_, ?_⟩
  · have hload := memmove_loadInt_of_lookup m (src + BitVec.ofNat 64 k)
      ((xs.drop k).take c) (by
        intro i hi
        rw [memmove_addr_add,
          memmove_forward_unread input direction inv (k + i) (by omega) (by omega),
          input.source (k + i) (by omega), memmove_chunk_lookup xs k c i (by omega)])
    simpa only [hlen] using hload
  · apply memmove_loadInt_exists
    intro i hi
    rw [memmove_addr_add]
    exact memmove_destination_mapped input inv (k + i) (by omega)
  · apply memmove_store_join inv (by have := input.length; have := input.dst_bound; omega)
      (by omega) (by have := input.length; omega) (by have := input.length; omega)
    intro i
    omega

/-- The next backward chunk begins at `n - (k + c)`. Loading its whole snapshot
before storing makes even a one-byte overlap safe for an eight-byte chunk. -/
theorem memmove_backward_chunk {m m0 : DataMem} {src dst : BitVec 64}
    {n : Nat} {xs : List UInt8} (input : MoveInput m0 src dst n xs)
    (direction : src.toNat ≤ dst.toNat) (k c : Nat) (hk : k + c ≤ n)
    (inv : MoveInv m m0 dst xs (n - k) n) :
    Mem.loadInt m (src + BitVec.ofNat 64 (n - (k + c))) c =
      some (Int.ofBytes ((xs.drop (n - (k + c))).take c)) ∧
    (∃ old, Mem.loadInt m (dst + BitVec.ofNat 64 (n - (k + c))) c = some old) ∧
    MoveInv (Mem.storeBytes m (dst + BitVec.ofNat 64 (n - (k + c)))
      ((xs.drop (n - (k + c))).take c)) m0 dst xs (n - (k + c)) n := by
  have hlen := memmove_chunk_length xs (n - (k + c)) c
    (by have := input.length; omega)
  refine ⟨?_, ?_, ?_⟩
  · have hload := memmove_loadInt_of_lookup m (src + BitVec.ofNat 64 (n - (k + c)))
      ((xs.drop (n - (k + c))).take c) (by
        intro i hi
        rw [memmove_addr_add,
          memmove_backward_unread input direction inv (n - (k + c) + i) (by omega),
          input.source (n - (k + c) + i) (by omega),
          memmove_chunk_lookup xs (n - (k + c)) c i (by omega)])
    simpa only [hlen] using hload
  · apply memmove_loadInt_exists
    intro i hi
    rw [memmove_addr_add]
    exact memmove_destination_mapped input inv (n - (k + c) + i) (by omega)
  · apply memmove_store_join inv (by have := input.length; have := input.dst_bound; omega)
      (by omega) (by have := input.length; omega) (by have := input.length; omega)
    intro i
    omega

/-- At completion the destination is exactly the original source snapshot,
and every address outside the destination has exactly its original lookup. -/
theorem memmove_final {m m0 : DataMem} {dst : BitVec 64} {xs : List UInt8}
    {n : Nat} (inv : MoveInv m m0 dst xs 0 n) :
    (∀ i < n, m.get? (dst + BitVec.ofNat 64 i) = xs[i]?) ∧
    (∀ a, (∀ i < n, a ≠ dst + BitVec.ofNat 64 i) → m.get? a = m0.get? a) := by
  exact ⟨fun i hi => inv.copied i (Nat.zero_le _) hi,
    fun a ha => inv.frame a (fun i _ hi => ha i hi)⟩

/-- An arbitrary framed read is unchanged. In particular the source may alias
the x86 return slot: only destination writes must avoid its eight addresses. -/
theorem memmove_loadBytes_frame {m m0 : DataMem} {dst p : BitVec 64}
    {xs : List UInt8} {lo hi : Nat} (inv : MoveInv m m0 dst xs lo hi) (c : Nat)
    (hsep : ∀ i < c, ∀ j, lo ≤ j → j < hi →
      p + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j) :
    Mem.loadBytes m p c = Mem.loadBytes m0 p c := by
  unfold Mem.loadBytes
  apply congrArg List.allSome
  apply List.map_congr_left
  intro i hi'
  exact inv.frame _ (hsep i (List.mem_range.mp hi'))

theorem memmove_loadInt_frame {m m0 : DataMem} {dst p : BitVec 64}
    {xs : List UInt8} {lo hi : Nat} (inv : MoveInv m m0 dst xs lo hi) (c : Nat)
    (hsep : ∀ i < c, ∀ j, lo ≤ j → j < hi →
      p + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j) :
    Mem.loadInt m p c = Mem.loadInt m0 p c := by
  exact congrArg (fun bs => bs.map Int.ofBytes) (memmove_loadBytes_frame inv c hsep)

end SszX86
