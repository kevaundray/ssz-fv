import SszX86.BitVectorLoad

namespace SszX86.BitVector
open SszNative UintCodec

private theorem error_allSome_take {α : Type} (items : List (Option α)) (values : List α)
    (loaded : items.allSome = some values) (count : Nat) :
    (items.take count).allSome = some (values.take count) := by
  induction items generalizing values count with
  | nil =>
    change (some [] : Option (List α)) = some values at loaded
    cases loaded
    simp only [List.take_nil]
    rfl
  | cons first rest ih =>
    cases first with
    | none => simp [List.allSome] at loaded
    | some value =>
      cases remainder : rest.allSome with
      | none =>
        change rest.mapM id = none at remainder
        simp [List.allSome, remainder] at loaded
      | some remaining =>
        change rest.mapM id = some remaining at remainder
        simp only [List.allSome, List.mapM_cons, id_eq, remainder] at loaded
        cases loaded
        cases count with
        | zero => rfl
        | succ count =>
          have projected := ih remaining remainder count
          change (rest.take count).mapM id = some (remaining.take count) at projected
          simp only [List.take_succ_cons, List.allSome, List.mapM_cons, id_eq, projected]
          rfl

/-- A shorter real load is the corresponding byte prefix of the same memory. -/
theorem errors_loadBytes_take (m : DataMem) (pointer : BitVec 64)
    (count prefixCount : Nat) (bytes : List UInt8)
    (loaded : Mem.loadBytes m pointer count = some bytes) (within : prefixCount ≤ count) :
    Mem.loadBytes m pointer prefixCount = some (bytes.take prefixCount) := by
  have projected := error_allSome_take
    ((List.range count).map (fun i => m.get? (pointer + BitVec.ofNat 64 i))) bytes loaded prefixCount
  simpa only [Mem.loadBytes, ← List.map_take, List.take_range, Nat.min_eq_left within] using projected

/-- Coherence of actual 64-bit and 32-bit reads; no status or padding is invented. -/
theorem errors_load_low32 (m : DataMem) (pointer : BitVec 64)
    (whole : BitVec 64) (low : BitVec 32)
    (loadedWhole : Mem.loadInt m pointer 8 = some (whole.toNat : Int))
    (loadedLow : Mem.loadInt m pointer 4 = some (low.toNat : Int)) :
    whole.setWidth 32 = low := by
  cases bytesRead : Mem.loadBytes m pointer 8 with
  | none =>
    simp only [Mem.loadInt, bytesRead, Option.map_none] at loadedWhole
    cases loadedWhole
  | some bytes =>
    have prefixLoad := errors_loadBytes_take m pointer 8 4 bytes bytesRead (by decide)
    have wholeValue : Int.ofBytes bytes = (whole.toNat : Int) := by
      simpa only [Mem.loadInt, bytesRead, Option.map_some, Option.some.injEq] using loadedWhole
    have lowValue : Int.ofBytes (bytes.take 4) = (low.toNat : Int) := by
      simpa only [Mem.loadInt, prefixLoad, Option.map_some, Option.some.injEq] using loadedLow
    have bits := BitVec.ofInt_ofBytes_take 32 4 rfl bytes
    rw [wholeValue, lowValue] at bits
    simpa only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq] using bits

theorem errors_uint_address (sp : UInt64) (off : Nat) :
    BitVec.ofNat 64 (sp.toNat + off) = sp.toBitVec + BitVec.ofNat 64 off := by
  simpa only [UInt64.toNat_toBitVec] using width_address sp.toBitVec off

theorem errors_raw_read (m : DataMem) (sp : UInt64) (off count value : Nat)
    (observed : widthLoad m (sp.toNat + off) count = some value) :
    Mem.loadInt m (sp.toBitVec + BitVec.ofNat 64 off) count = some (value : Int) := by
  simpa only [errors_uint_address] using widthLoad_eq m (sp.toNat + off) count value observed

theorem errors_word_unique {n : Nat} (m : DataMem) (pointer : BitVec 64) (count : Nat)
    (left right : BitVec n)
    (hleft : Mem.loadInt m pointer count = some (left.toNat : Int))
    (hright : Mem.loadInt m pointer count = some (right.toNat : Int)) : left = right := by
  have same := Option.some.inj (hleft.symm.trans hright)
  apply BitVec.eq_of_toNat_eq
  omega

end SszX86.BitVector
