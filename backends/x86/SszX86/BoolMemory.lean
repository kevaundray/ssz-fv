import SszX86.MemmoveMemory
import SszBool

namespace SszX86.BoolCodec
open Std.ExtHashMap

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The internal result occupies 80 mapped bytes. Values and padding are arbitrary. -/
def Mapped (m : DataMem) (out : BitVec 64) : Prop :=
  ∀ i < 80, ∃ byte, m.get? (out + BitVec.ofNat 64 i) = some byte

def observe (m : DataMem) (out : BitVec 64) (offset width : Nat) : Option Nat :=
  (Mem.loadInt m (out + BitVec.ofNat 64 offset) width).map Int.toNat

theorem mapped_load (m : DataMem) (out : BitVec 64) (hm : Mapped m out)
    (offset width : Nat) (hb : offset + width ≤ 80) :
    ∃ value, Mem.loadInt m (out + BitVec.ofNat 64 offset) width = some value := by
  apply memmove_loadInt_exists
  intro i hi
  rw [memmove_addr_add]
  exact hm (offset + i) (by omega)

/-- Replacing bytes cannot unmap any previously mapped byte. -/
theorem mapped_store (m : DataMem) (out address : BitVec 64)
    (width : Nat) (value : Int) (hm : Mapped m out) :
    Mapped (Mem.storeInt m address width value) out := by
  intro i hi
  obtain ⟨old, hold⟩ := hm i hi
  change m[out + BitVec.ofNat 64 i]? = some old at hold
  simp only [Mem.storeInt, Mem.storeBytes, get?_eq_getElem?, union_eq, getElem?_union]
  cases hnew : ((Int.toBytes width value).At address)[out + BitVec.ofNat 64 i]? with
  | none => exact ⟨old, by simp [hold]⟩
  | some byte => exact ⟨byte, by simp⟩

theorem load_store_same (m : DataMem) (address : BitVec 64)
    (width : Nat) (value : Int) (hb : width ≤ 2^64) :
    Mem.loadInt (Mem.storeInt m address width value) address width =
      some (value.take (8 * width)) := by
  have h := memmove_loadInt_of_lookup (Mem.storeInt m address width value) address
    (Int.toBytes width value) (fun i hi =>
      memmove_store_lookup_inside m address (Int.toBytes width value) i hi
        (by simpa only [Int.toBytes_length] using hb))
  simpa only [Int.toBytes_length, ofBytes_toBytes] using h

/-- Signed register interpretation still observes the full unsigned 64-bit value. -/
theorem observe_store64 (m : DataMem) (out : BitVec 64) (offset : Nat) (value : BitVec 64) :
    observe (Mem.storeInt m (out + BitVec.ofNat 64 offset) 8 value.toInt) out offset 8 =
      some value.toNat := by
  rw [observe, load_store_same m _ 8 _ (by decide)]
  have h := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := value))
  simp only [BitVec.toNat_ofInt] at h
  simpa [Int.take] using congrArg some h

theorem load_store_disjoint (m : DataMem) (loadAt storeAt : BitVec 64)
    (loadWidth storeWidth : Nat) (value : Int)
    (hs : ∀ i < loadWidth, ∀ j < storeWidth,
      loadAt + BitVec.ofNat 64 i ≠ storeAt + BitVec.ofNat 64 j) :
    Mem.loadInt (Mem.storeInt m storeAt storeWidth value) loadAt loadWidth =
      Mem.loadInt m loadAt loadWidth := by
  apply memmove_loadInt_congr
  intro i hi
  apply memmove_store_lookup_outside
  intro j hj
  exact hs i hi j (by simpa only [Int.toBytes_length] using hj)

theorem offsets_disjoint (out : BitVec 64) (hb : out.toNat + 80 ≤ 2^64)
    (a n b k : Nat) (ha : a + n ≤ 80) (hb' : b + k ≤ 80)
    (hs : a + n ≤ b ∨ b + k ≤ a) :
    ∀ i < n, ∀ j < k,
      out + BitVec.ofNat 64 a + BitVec.ofNat 64 i ≠
        out + BitVec.ofNat 64 b + BitVec.ofNat 64 j := by
  intro i hi j hj he
  simp only [memmove_addr_add] at he
  have hij := memmove_addr_injective out 80 (a+i) (b+j) hb (by omega) (by omega) he
  omega

theorem load_store_offset_disjoint (m : DataMem) (out : BitVec 64)
    (hb : out.toNat + 80 ≤ 2^64) (a n b k : Nat) (value : Int)
    (ha : a + n ≤ 80) (hb' : b + k ≤ 80) (hs : a + n ≤ b ∨ b + k ≤ a) :
    Mem.loadInt (Mem.storeInt m (out + BitVec.ofNat 64 b) k value)
      (out + BitVec.ofNat 64 a) n = Mem.loadInt m (out + BitVec.ofNat 64 a) n :=
  load_store_disjoint m _ _ n k value (offsets_disjoint out hb a n b k ha hb' hs)

/-- Stores preserve every byte outside a specified enclosing interval. -/
theorem store_frame (m : DataMem) (out address : BitVec 64)
    (limit offset width : Nat) (value : Int) (hb : offset + width ≤ limit)
    (ha : ∀ i < limit, address ≠ out + BitVec.ofNat 64 i) :
    (Mem.storeInt m (out + BitVec.ofNat 64 offset) width value).get? address = m.get? address := by
  apply memmove_store_lookup_outside
  intro i hi
  rw [memmove_addr_add]
  apply ha (offset + i)
  have hi' : i < width := by simpa only [Int.toBytes_length] using hi
  omega

/-- Store order matches the scope-error path, including its shared error tail. -/
def scopeMem (m : DataMem) (out : BitVec 64) (length : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 64) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 length.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 72) 4 3
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1

/-- Store order matches the invalid-byte path, including its shared error tail. -/
def badMem (m : DataMem) (out : BitVec 64) (value : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 64) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 value.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 72) 4 13
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1

def successMem (m : DataMem) (out : BitVec 64) (value : Bool) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 2 (if value then 256 else 0)
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 0

private theorem signed64_nat (value : BitVec 64) :
    (value.toInt.take 64).toNat = value.toNat := by
  have h := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := value))
  simp only [BitVec.toNat_ofInt] at h
  simpa [Int.take] using h

private theorem observe_store_same (m : DataMem) (out : BitVec 64)
    (offset width : Nat) (value : Int) (hb : width ≤ 2^64) :
    observe (Mem.storeInt m (out + BitVec.ofNat 64 offset) width value) out offset width =
      some (value.take (8 * width)).toNat := by
  rw [observe, load_store_same m _ width value hb]
  rfl

private theorem observe_store_disjoint (m : DataMem) (out : BitVec 64)
    (hb : out.toNat + 80 ≤ 2^64) (a n b k : Nat) (value : Int)
    (ha : a + n ≤ 80) (hb' : b + k ≤ 80) (hs : a + n ≤ b ∨ b + k ≤ a) :
    observe (Mem.storeInt m (out + BitVec.ofNat 64 b) k value) out a n =
      observe m out a n := by
  simp only [observe, load_store_offset_disjoint m out hb a n b k value ha hb' hs]

theorem scope_result (m : DataMem) (out : BitVec 64) (length : BitVec 64)
    (hb : out.toNat + 80 ≤ 2^64) :
    SszNative.BoolCodec.ResultAt (observe (scopeMem m out length) out)
      (.error (.scope 1 length.toNat)) := by
  simp (disch := first | assumption | omega | decide) only
    [SszNative.BoolCodec.ResultAt, SszNative.BoolCodec.errorAt, SszNative.NatMemory.smallAt,
     scopeMem, observe_store_disjoint, observe_store_same, Nat.reduceAdd, Nat.reduceMul]
  simpa [Int.take] using signed64_nat length

theorem bad_result (m : DataMem) (out : BitVec 64) (value : BitVec 64)
    (hb : out.toNat + 80 ≤ 2^64) :
    SszNative.BoolCodec.ResultAt (observe (badMem m out value) out)
      (.error (.notABit value.toNat)) := by
  simp (disch := first | assumption | omega | decide) only
    [SszNative.BoolCodec.ResultAt, SszNative.BoolCodec.errorAt, SszNative.NatMemory.smallAt,
     badMem, observe_store_disjoint, observe_store_same, Nat.reduceAdd, Nat.reduceMul]
  simpa [Int.take] using signed64_nat value

theorem success_result (m : DataMem) (out : BitVec 64) (value : Bool)
    (hb : out.toNat + 80 ≤ 2^64) :
    SszNative.BoolCodec.ResultAt (observe (successMem m out value) out)
      (.ok (.bool value)) := by
  simp (disch := first | assumption | omega | decide) only
    [SszNative.BoolCodec.ResultAt, successMem, observe_store_disjoint, observe_store_same]
  cases value <;> decide

theorem scope_mapped (m : DataMem) (out : BitVec 64) (length : BitVec 64)
    (hm : Mapped m out) : Mapped (scopeMem m out length) out := by
  unfold scopeMem
  repeat' first | exact hm | apply mapped_store

theorem bad_mapped (m : DataMem) (out : BitVec 64) (value : BitVec 64)
    (hm : Mapped m out) : Mapped (badMem m out value) out := by
  unfold badMem
  repeat' first | exact hm | apply mapped_store

theorem success_mapped (m : DataMem) (out : BitVec 64) (value : Bool)
    (hm : Mapped m out) : Mapped (successMem m out value) out := by
  unfold successMem
  repeat' first | exact hm | apply mapped_store

/-- Error writes stop before the four trailing padding bytes. -/
theorem scope_frame (m : DataMem) (out address : BitVec 64) (length : BitVec 64)
    (ha : ∀ i < 76, address ≠ out + BitVec.ofNat 64 i) :
    (scopeMem m out length).get? address = m.get? address := by
  simp (disch := first | assumption | omega | decide) only
    [scopeMem, store_frame (limit := 76)]

theorem bad_frame (m : DataMem) (out address : BitVec 64) (value : BitVec 64)
    (ha : ∀ i < 76, address ≠ out + BitVec.ofNat 64 i) :
    (badMem m out value).get? address = m.get? address := by
  simp (disch := first | assumption | omega | decide) only
    [badMem, store_frame (limit := 76)]

theorem success_frame (m : DataMem) (out address : BitVec 64) (value : Bool)
    (htag : ∀ i < 8, address ≠ out + BitVec.ofNat 64 i)
    (hvalue : ∀ i < 2, address ≠ out + 16#64 + BitVec.ofNat 64 i) :
    (successMem m out value).get? address = m.get? address := by
  unfold successMem
  rw [store_frame (limit := 8) _ _ _ _ _ _ (by decide) htag]
  apply memmove_store_lookup_outside
  intro i hi
  exact hvalue i (by simpa only [Int.toBytes_length] using hi)

end SszX86.BoolCodec
