import SszX86.NatMulLoopInner
import SszX86.NatMulMemoryBuffer

namespace SszX86.NatMul.Product
open SszNative
open UintCodec

/-- Observe both the freshly stored prefix and the unchanged old suffix. -/
theorem ReadAt.fill_prefix (m : DataMem) (dst : BitVec 64) (index : Nat)
    (buffer front : List (BitVec 64)) (read : ReadAt m dst index buffer)
    (inside : front.length ≤ buffer.length)
    (span : dst.toNat + 8*(index+buffer.length) ≤ 2^64) :
    ReadAt (Large.fillMem m dst index front) dst index (front ++ buffer.drop front.length) := by
  intro j
  by_cases low : j.val < front.length
  · have written := Large.fill_words m dst index front (by omega) ⟨j.val, low⟩
    have loaded := widthLoad_eq _ _ _ _ written
    simpa [width_address, List.getElem_append_left low] using loaded
  · have high : front.length ≤ j.val := by omega
    have bound : j.val < buffer.length := by
      have := j.isLt
      simp only [List.length_append, List.length_drop] at this
      omega
    have old := read ⟨j.val, bound⟩
    have same : Mem.loadInt (Large.fillMem m dst index front)
        (dst + BitVec.ofNat 64 (8*(index+j.val))) 8 =
        Mem.loadInt m (dst + BitVec.ofNat 64 (8*(index+j.val))) 8 := by
      apply memmove_loadInt_congr
      intro k hk
      apply Large.fill_frame
      intro off lower upper eq
      rw [memmove_addr_add] at eq
      have inject := memmove_addr_injective dst (8*(index+buffer.length))
        (8*(index+j.val)+k) off span (by omega) (by omega) eq
      omega
    rw [same]
    simpa [List.getElem_append_right high, List.getElem_drop, Nat.add_sub_of_le high] using old

theorem nativeRow_length (factor : BitVec 64) (right buffer : List (BitVec 64))
    (inside : right.length+1 ≤ buffer.length) :
    (LimbMul.nativeRow factor right buffer).length = buffer.length := by
  simp only [LimbMul.nativeRow, List.length_append, LimbMul.row_length, List.length_drop]
  omega

/-- Exactly the original inner writes and the explicit carry overwrite. -/
theorem ReadAt.nativeRow (m : DataMem) (dst : BitVec 64) (index : Nat)
    (factor : BitVec 64) (right buffer : List (BitVec 64))
    (read : ReadAt m dst index buffer) (inside : right.length+1 ≤ buffer.length)
    (span : dst.toNat + 8*(index+buffer.length) ≤ 2^64) :
    ReadAt (Large.fillMem m dst index (LimbMul.row factor right buffer)) dst index
      (LimbMul.nativeRow factor right buffer) := by
  simpa only [LimbMul.nativeRow, LimbMul.row_length] using
    read.fill_prefix m dst index buffer (LimbMul.row factor right buffer)
      (by rw [LimbMul.row_length]; exact inside) span

/-- Indexed buffer frames retain the low prefix peeled off by nativeRows. -/
def RowFrame (before after : DataMem) (dst : BitVec 64) (index count : Nat) : Prop :=
  ∀ a, (∀ j, 8*index ≤ j → j < 8*(index+count) → a ≠ dst + BitVec.ofNat 64 j) →
    after.get? a = before.get? a

theorem rowFrame_fill (m : DataMem) (dst : BitVec 64) (index count : Nat)
    (words : List (BitVec 64)) (inside : words.length ≤ count) :
    RowFrame m (Large.fillMem m dst index words) dst index count := by
  intro a outside
  apply Large.fill_frame
  intro j lo hi
  exact outside j lo (by omega)

theorem RowFrame.trans {a b c : DataMem} {dst : BitVec 64} {index count : Nat}
    (first : RowFrame a b dst index count) (second : RowFrame b c dst index count) :
    RowFrame a c dst index count := by
  intro p outside
  exact (second p outside).trans (first p outside)

theorem RowFrame.widen {before after : DataMem} {dst : BitVec 64}
    {index count outerIndex outerCount : Nat}
    (frame : RowFrame before after dst index count)
    (low : outerIndex ≤ index) (high : index+count ≤ outerIndex+outerCount) :
    RowFrame before after dst outerIndex outerCount := by
  intro a outside
  apply frame
  intro j lo hi
  exact outside j (by omega) (by omega)

theorem RowFrame.to_buffer {before after : DataMem} {dst : BitVec 64} {index count capacity : Nat}
    (frame : RowFrame before after dst index count)
    (span : dst.toNat + 8*capacity ≤ 2^64) (inside : index+count ≤ capacity) :
    BufferFrame before after dst.toNat (8*capacity) := by
  intro a outside
  apply frame
  intro j _ hi
  exact Body.outside_byte dst a (8*capacity) j span outside (by omega)

end SszX86.NatMul.Product
