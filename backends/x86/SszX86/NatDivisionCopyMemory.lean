import SszX86.NatDivisionCore

namespace SszX86.NatDivision.Copy
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The copy writes every requested word; absent source words are zero. -/
def limb (words : List (BitVec 64)) (i : Nat) : BitVec 64 := words[i]?.getD 0

def memory (m : DataMem) (destination : BitVec 64) (words : List (BitVec 64)) : Nat → DataMem
  | 0 => m
  | n + 1 => Mem.storeInt (memory m destination words n)
      (destination + BitVec.ofNat 64 (8*n)) 8 (limb words n).toInt

@[simp] theorem memory_zero (m : DataMem) (p : BitVec 64) (words : List (BitVec 64)) :
    memory m p words 0 = m := rfl

@[simp] theorem memory_succ (m : DataMem) (p : BitVec 64) (words : List (BitVec 64)) (n : Nat) :
    memory m p words (n+1) = Mem.storeInt (memory m p words n)
      (p + BitVec.ofNat 64 (8*n)) 8 (limb words n).toInt := rfl

theorem limb_missing (words : List (BitVec 64)) (i : Nat) (h : words.length ≤ i) :
    limb words i = 0 := by simp [limb, List.getElem?_eq_none (by omega)]

/-- No store destroys an existing mapping, including unrelated mappings. -/
theorem memory_mapped (m : DataMem) (p q : BitVec 64) (words : List (BitVec 64))
    (n capacity : Nat) (hm : Large.Mapped m q capacity) :
    Large.Mapped (memory m p words n) q capacity := by
  induction n with
  | zero => exact hm
  | succ n ih => exact Large.mapped_store _ _ _ _ _ _ ih

/-- Exact byte frame: nothing outside the written prefix changes. -/
theorem memory_frame (m : DataMem) (p a : BitVec 64) (words : List (BitVec 64))
    (n : Nat) (outside : ∀ i < 8*n, a ≠ p + BitVec.ofNat 64 i) :
    (memory m p words n).get? a = m.get? a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [memory_succ, BoolCodec.store_frame _ p a (8*(n+1)) (8*n) 8 _ (by omega) outside]
    exact ih (fun i hi => outside i (by omega))

/-- Borrowed source loads still observe the original memory after every prefix. -/
theorem memory_source (m : DataMem) (source destination : BitVec 64)
    (words : List (BitVec 64)) (count n : Nat) (hn : n ≤ count)
    (apart : Large.Disjoint source destination (8*words.length) (8*count))
    (i : Nat) (hi : i < words.length) :
    Mem.loadInt (memory m destination words n) (source + BitVec.ofNat 64 (8*i)) 8 =
      Mem.loadInt m (source + BitVec.ofNat 64 (8*i)) 8 := by
  apply memmove_loadInt_congr
  intro j hj
  apply memory_frame
  intro k hk
  rw [memmove_addr_add]
  exact apart (8*i+j) (by omega) k (by omega)

private theorem word_apart (p : BitVec 64) (count i j : Nat)
    (bound : p.toNat + 8*count ≤ 2^64) (hi : i < count) (hj : j < count) (hne : i ≠ j) :
    ∀ a < 8, ∀ b < 8,
      p + BitVec.ofNat 64 (8*i) + BitVec.ofNat 64 a ≠
        p + BitVec.ofNat 64 (8*j) + BitVec.ofNat 64 b := by
  intro a ha b hb equal
  simp only [memmove_addr_add] at equal
  have h := memmove_addr_injective p (8*count) (8*i+a) (8*j+b)
    bound (by omega) (by omega) equal
  omega

/-- Every destination word is fully written before any division instruction. -/
theorem memory_load (m : DataMem) (p : BitVec 64) (words : List (BitVec 64))
    (n : Nat) (bound : p.toNat + 8*n ≤ 2^64) (i : Nat) (hi : i < n) :
    Mem.loadInt (memory m p words n) (p + BitVec.ofNat 64 (8*i)) 8 =
      some ((limb words i).toNat : Int) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [memory_succ]
    by_cases eq : i = n
    · subst i
      rw [BoolCodec.load_store_same _ _ 8 _ (by decide)]
      congr 1
      have cast := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := limb words n))
      simp only [BitVec.toNat_ofInt] at cast
      simp only [Int.take]
      omega
    · rw [BoolCodec.load_store_disjoint _ _ _ 8 8 _
        (word_apart p (n+1) i n bound hi (by omega) eq)]
      exact ih (by omega) (by omega)

end SszX86.NatDivision.Copy
