import SszX86.MeasureBitsLoads
import SszX86.MeasureBitsMapped

namespace SszX86.Measure.Bits
open UintCodec

private theorem all_some_member {α : Type} (items : List (Option α)) (values : List α)
    (loaded : items.allSome = some values) (item : Option α) (member : item ∈ items) :
    ∃ value, item = some value := by
  induction items generalizing values with
  | nil => cases member
  | cons first rest ih =>
    cases first with
    | none => simp [List.allSome] at loaded
    | some value =>
      rcases List.mem_cons.mp member with equal | member
      · exact ⟨value, equal⟩
      · cases remaining : rest.allSome with
        | none =>
          change rest.mapM id = none at remaining
          simp [List.allSome, remaining] at loaded
        | some values' => exact ih values' remaining member

theorem load_mapped (m : DataMem) (pointer : BitVec 64) (byteCount : Nat) (value : Int)
    (loaded : Mem.loadInt m pointer byteCount = some value) : Large.Mapped m pointer byteCount := by
  unfold Mem.loadInt at loaded
  cases bytesRead : Mem.loadBytes m pointer byteCount with
  | none => simp only [bytesRead, Option.map_none] at loaded; cases loaded
  | some bytes =>
    intro i hi
    exact all_some_member _ bytes bytesRead _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem arena_mapped (m : DataMem) (header address capacity used : BitVec 64)
    (stored : ArenaAt m header address capacity used) : Large.Mapped m header 24 := by
  have raw := arena_loads m header address capacity used stored
  have first := load_mapped m header 8 _ raw.1
  have second := load_mapped m (header + 8) 8 _ raw.2.1
  have third := load_mapped m (header + 16) 8 _ raw.2.2
  intro i hi
  by_cases firstWord : i < 8
  · exact first i firstWord
  by_cases secondWord : i < 16
  · have same : header + 8 + BitVec.ofNat 64 (i - 8) = header + BitVec.ofNat 64 i := by bv_omega
    simpa only [same] using second (i - 8) (by omega)
  · have same : header + 16 + BitVec.ofNat 64 (i - 16) = header + BitVec.ofNat 64 i := by bv_omega
    simpa only [same] using third (i - 16) (by omega)

theorem stored_word_load (m : DataMem) (pointer value : BitVec 64) :
    Mem.loadInt (Mem.storeInt m pointer 8 value.toInt) pointer 8 = some (value.toNat : Int) := by
  have observed := BoolCodec.observe_store64 m pointer 0 value
  have stored : widthLoad (Mem.storeInt m pointer 8 value.toInt) pointer.toNat 8 = some value.toNat := by
    simpa only [BoolCodec.observe, widthLoad, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero] using observed
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using widthLoad_eq _ pointer.toNat 8 value.toNat stored

end SszX86.Measure.Bits
