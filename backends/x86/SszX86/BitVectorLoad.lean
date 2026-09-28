import SszX86.BitVectorCore

namespace SszX86.BitVector
open UintCodec

private theorem all_some_length {α : Type} (items : List (Option α)) (values : List α)
    (loaded : items.allSome = some values) : values.length = items.length := by
  induction items generalizing values with
  | nil =>
    change (some [] : Option (List α)) = some values at loaded
    cases loaded
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
        change some (value :: remaining) = some values at loaded
        cases loaded
        have lengths := ih remaining remainder
        simpa only [List.length_cons] using congrArg Nat.succ lengths

/-- Every real Kraken load is an unsigned integer of exactly its byte width. -/
theorem load_unsigned_bounds (m : DataMem) (pointer : BitVec 64) (count : Nat) (value : Int)
    (loaded : Mem.loadInt m pointer count = some value) :
    0 ≤ value ∧ value < (2 : Int) ^ (8 * count) := by
  unfold Mem.loadInt at loaded
  cases bytesRead : Mem.loadBytes m pointer count with
  | none => simp only [bytesRead, Option.map_none] at loaded; cases loaded
  | some bytes =>
    simp only [bytesRead, Option.map_some, Option.some.injEq] at loaded
    subst value
    have lengths := all_some_length
      ((List.range count).map (fun i => m.get? (pointer + BitVec.ofNat 64 i))) bytes bytesRead
    simp only [List.length_map, List.length_range] at lengths
    have bound := Int.ofBytes_lt bytes
    rw [lengths, show (256 : Int) = 2^8 by decide, ← Int.pow_mul] at bound
    exact ⟨Int.ofBytes_ge_zero bytes, bound⟩

/-- Mapped but semantically unspecified native padding is still a concrete word;
this derives its value from memory rather than assigning padding a model value. -/
theorem mapped_word (m : DataMem) (pointer : BitVec 64) (count : Nat)
    (hm : ∃ value, Mem.loadInt m pointer count = some value) :
    ∃ value : BitVec (8 * count), Mem.loadInt m pointer count = some (value.toNat : Int) := by
  obtain ⟨value, loaded⟩ := hm
  obtain ⟨nonnegative, bound⟩ := load_unsigned_bounds m pointer count value loaded
  refine ⟨BitVec.ofInt (8 * count) value, ?_⟩
  have boundNat : value < ((2 ^ (8 * count) : Nat) : Int) := by
    rw [Int.natCast_pow]
    change value < (2 : Int) ^ (8 * count)
    exact bound
  have remainder := Int.emod_eq_of_lt nonnegative boundNat
  have cast : ((BitVec.ofInt (8 * count) value).toNat : Int) = value := by
    simp only [BitVec.toNat_ofInt, remainder]
    omega
  simpa only [cast] using loaded

end SszX86.BitVector
