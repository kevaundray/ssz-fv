import SszX86.CodecPlanSingletonReserve

namespace SszX86.CodecPlanSingleton
open SszX86.UintCodec

structure PlanWords where
  children : BitVec 64
  count : BitVec 64
  sizePointer : BitVec 64
  sizePayload : BitVec 64
  leading : BitVec 64

/-- Only the five active Plan words; no assertion about a surrounding Result's padding. -/
def PlanWords.At (w : PlanWords) (m : DataMem) (p : BitVec 64) : Prop :=
  Mem.loadInt m p 8 = some (w.children.toNat : Int) ∧
  Mem.loadInt m (p + 8#64) 8 = some (w.count.toNat : Int) ∧
  Mem.loadInt m (p + 16#64) 8 = some (w.sizePointer.toNat : Int) ∧
  Mem.loadInt m (p + 24#64) 8 = some (w.sizePayload.toNat : Int) ∧
  Mem.loadInt m (p + 32#64) 8 = some (w.leading.toNat : Int)

def Apart (p : BitVec 64) (n : Nat) (q : BitVec 64) (k : Nat) : Prop :=
  ∀ i < n, ∀ j < k, p + BitVec.ofNat 64 i ≠ q + BitVec.ofNat 64 j

theorem apart_symm {p q : BitVec 64} {n k : Nat} (h : Apart p n q k) : Apart q k p n := by
  intro j hj i hi
  exact Ne.symm (h i hi j hj)

theorem load_store_apart (m : DataMem) (p q : BitVec 64) (n k a b w z : Nat) (v : Int)
    (apart : Apart p n q k) (ha : a + w ≤ n) (hb : b + z ≤ k) :
    Mem.loadInt (Mem.storeInt m (q + BitVec.ofNat 64 b) z v)
      (p + BitVec.ofNat 64 a) w = Mem.loadInt m (p + BitVec.ofNat 64 a) w := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  simp only [memmove_addr_add]
  exact apart (a+i) (by omega) (b+j) (by omega)

theorem stored_word (m : DataMem) (p v : BitVec 64) :
    Mem.loadInt (Mem.storeInt m p 8 v.toInt) p 8 = some (v.toNat : Int) := by
  rw [BoolCodec.load_store_same _ _ _ _ (by decide)]
  have eq := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := v))
  simp only [BitVec.toNat_ofInt] at eq
  congr 1
  have nonneg : 0 ≤ v.toInt.take 64 := by simp [Int.take]
  simpa [Int.take] using congrArg (fun x : Nat => (x : Int)) eq

def copyMem (m : DataMem) (p : BitVec 64) (w : PlanWords) : DataMem :=
  let m := Mem.storeInt m (p + 32#64) 8 w.leading.toInt
  let m := Mem.storeInt m (p + 24#64) 8 w.sizePayload.toInt
  let m := Mem.storeInt m (p + 16#64) 8 w.sizePointer.toInt
  let m := Mem.storeInt m (p + 8#64) 8 w.count.toInt
  Mem.storeInt m p 8 w.children.toInt

private theorem offset_keep (m : DataMem) (p : BitVec 64) (a b : Nat) (v : Int)
    (ha : a + 8 ≤ 40) (hb : b + 8 ≤ 40) (apart : a + 8 ≤ b ∨ b + 8 ≤ a) :
    Mem.loadInt (Mem.storeInt m (p + BitVec.ofNat 64 b) 8 v)
      (p + BitVec.ofNat 64 a) 8 = Mem.loadInt m (p + BitVec.ofNat 64 a) 8 := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  bv_omega

/-- Every copied active word is established by its literal store. -/
theorem copy_at (m : DataMem) (p : BitVec 64) (w : PlanWords) : w.At (copyMem m p w) p := by
  have keep0 (m : DataMem) (a : Nat) (v : Int) (lo : 8 ≤ a) (hi : a + 8 ≤ 40) :
      Mem.loadInt (Mem.storeInt m p 8 v) (p + BitVec.ofNat 64 a) 8 =
        Mem.loadInt m (p + BitVec.ofNat 64 a) 8 := by
    simpa using offset_keep m p a 0 v hi (by decide) (Or.inr lo)
  simp (disch := first | omega | decide) only
    [PlanWords.At, copyMem, keep0, offset_keep, stored_word]

theorem copy_frame (m : DataMem) (p a : BitVec 64) (w : PlanWords)
    (outside : ∀ i < 40, a ≠ p + BitVec.ofNat 64 i) :
    (copyMem m p w).get? a = m.get? a := by
  have zero : p = p + BitVec.ofNat 64 0 := by simp
  simp only [copyMem]
  rw [zero]
  simp (disch := first | assumption | omega | decide) only [BoolCodec.store_frame (limit := 40)]

def successMem (m : DataMem) (out pointer : BitVec 64) : DataMem :=
  Mem.storeInt (Mem.storeInt (Mem.storeInt m out 8 pointer.toInt) (out + 8#64) 8 1)
    (out + 64#64) 4 0

def errorMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + 56#64) 8 0
  let m := Mem.storeInt m (out + 48#64) 8 0
  let m := Mem.storeInt m (out + 40#64) 8 0
  let m := Mem.storeInt m (out + 32#64) 8 0
  let m := Mem.storeInt m (out + 24#64) 8 0
  let m := Mem.storeInt m (out + 16#64) 8 0
  let m := Mem.storeInt m out 8 1
  let m := Mem.storeInt m (out + 8#64) 8 0
  Mem.storeInt m (out + 64#64) 4 32768

theorem error_frame (m : DataMem) (out a : BitVec 64)
    (outside : ∀ i < 68, a ≠ out + BitVec.ofNat 64 i) :
    (errorMem m out).get? a = m.get? a := by
  have zero : out = out + BitVec.ofNat 64 0 := by simp
  simp only [errorMem]
  rw [zero]
  simp (disch := first | assumption | omega | decide) only [BoolCodec.store_frame (limit := 68)]

/-- Success publishes the slice and status only; bytes16..63 and bytes68..71
of the physical Result area are untouched by publication. -/
theorem success_frame (m : DataMem) (out pointer a : BitVec 64)
    (slice : ∀ i < 16, a ≠ out + BitVec.ofNat 64 i)
    (status : ∀ i < 4, a ≠ out + 64#64 + BitVec.ofNat 64 i) :
    (successMem m out pointer).get? a = m.get? a := by
  unfold successMem
  rw [memmove_store_lookup_outside _ _ _ _ (by
    intro i hi
    exact status i (by simpa only [Int.toBytes_length] using hi))]
  have zero : out = out + BitVec.ofNat 64 0 := by simp
  rw [zero]
  simp (disch := first | assumption | omega | decide) only [BoolCodec.store_frame (limit := 16)]

end SszX86.CodecPlanSingleton
