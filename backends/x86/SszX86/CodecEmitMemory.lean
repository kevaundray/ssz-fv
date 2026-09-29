import SszX86.CodecStorageBase
import SszCodecEmitMemory

set_option autoImplicit false

namespace SszX86.CodecEmit
open SszNative

/-- Natural-address view of physical memory. No initialized padding or old
output byte is asserted by this view. Physical bounds are owned separately. -/
def byteView (m : DataMem) (address : Nat) : Option UInt8 :=
  m.get? (BitVec.ofNat 64 address)

/-- The whole caller output slice follows the shared ordered-write trace.
Stack and result writes are intentionally handled by a separate physical frame. -/
def OutputAt (before after : DataMem) (out : BitVec 64) (capacity : Nat)
    (writes : List SszNative.CodecEmit.Write) : Prop :=
  ∀ i, i < capacity → byteView after (out.toNat + i) =
    SszNative.CodecEmit.applyWrites (byteView before) writes (out.toNat + i)

@[simp] theorem byteView_offset (m : DataMem) (out : BitVec 64) (i : Nat) :
    byteView m (out.toNat + i) = m.get? (out + BitVec.ofNat 64 i) := by
  simp only [byteView, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

namespace OutputAt

theorem refl (m : DataMem) (out : BitVec 64) (capacity : Nat) :
    OutputAt m m out capacity [] := by
  intro i hi
  rfl

/-- Composition preserves the actual order of offset stores and child writes.
Only the cell currently observed is required from the intermediate memory. -/
theorem append {before middle after : DataMem} {out : BitVec 64} {capacity : Nat}
    {first second : List SszNative.CodecEmit.Write}
    (hfirst : OutputAt before middle out capacity first)
    (hsecond : OutputAt middle after out capacity second) :
    OutputAt before after out capacity (first ++ second) := by
  intro i hi
  rw [hsecond i hi, SszNative.CodecEmit.applyWrites_append]
  exact SszNative.CodecEmit.applyWrites_pointwise _ _ second _ (hfirst i hi)

/-- Machine byte initialization plus the untouched suffix proves the exact
shared trace relation whenever the shared trace encodes these bytes. -/
theorem of_bytes {before after : DataMem} {out : BitVec 64} {capacity : Nat}
    {writes : List SszNative.CodecEmit.Write} {bytes : Ssz.Bytes}
    (encoded : SszNative.CodecEmit.Encodes writes out.toNat bytes)
    (stored : Emit.BytesAt after out bytes)
    (suffix : ∀ i, bytes.size ≤ i → i < capacity →
      after.get? (out + BitVec.ofNat 64 i) = before.get? (out + BitVec.ofNat 64 i)) :
    OutputAt before after out capacity writes := by
  intro i hi
  rw [encoded (byteView before)]
  by_cases live : i < bytes.size
  · rw [SszNative.CodecEmit.applyWrite_inside (byteView before) ⟨out.toNat, bytes⟩
      (out.toNat + i) (Nat.le_add_right _ _) (Nat.add_lt_add_left live _)]
    simpa only [byteView_offset, Nat.add_sub_cancel_left] using stored i live
  · rw [SszNative.CodecEmit.applyWrite_outside (byteView before) ⟨out.toNat, bytes⟩
      (out.toNat + i) (Or.inr (Nat.add_le_add_left (Nat.le_of_not_gt live) _))]
    simpa only [byteView_offset] using suffix i (by omega) hi

/-- Every byte of the exact initialized prefix is an actual machine byte. -/
theorem initialized {before after : DataMem} {out : BitVec 64} {capacity : Nat}
    {writes : List SszNative.CodecEmit.Write} {bytes : Ssz.Bytes}
    (h : OutputAt before after out capacity writes)
    (encoded : SszNative.CodecEmit.Encodes writes out.toNat bytes)
    (fits : bytes.size ≤ capacity) : Emit.BytesAt after out bytes := by
  intro i hi
  have cell := h i (by omega)
  rw [encoded (byteView before),
    SszNative.CodecEmit.applyWrite_inside (byteView before) ⟨out.toNat, bytes⟩
      (out.toNat + i) (Nat.le_add_right _ _) (Nat.add_lt_add_left hi _)] at cell
  simpa only [byteView_offset, Nat.add_sub_cancel_left] using cell

/-- The suffix retains its exact previous Option byte, including unreadable
cells; it is not silently initialized by the semantic encoding. -/
theorem suffix {before after : DataMem} {out : BitVec 64} {capacity : Nat}
    {writes : List SszNative.CodecEmit.Write} {bytes : Ssz.Bytes}
    (h : OutputAt before after out capacity writes)
    (encoded : SszNative.CodecEmit.Encodes writes out.toNat bytes)
    (i : Nat) (lower : bytes.size ≤ i) (upper : i < capacity) :
    after.get? (out + BitVec.ofNat 64 i) = before.get? (out + BitVec.ofNat 64 i) := by
  have cell := h i upper
  rw [encoded (byteView before),
    SszNative.CodecEmit.applyWrite_outside (byteView before) ⟨out.toNat, bytes⟩
      (out.toNat + i) (Or.inr (Nat.add_le_add_left lower _))] at cell
  simpa only [byteView_offset] using cell

end OutputAt

/-- Widening an actual machine frame does not add byte observations. -/
theorem frame_mono {before after : DataMem} {small large : Codec.Footprint}
    (h : Codec.MemoryFrame before after small) (included : ∀ a, small a → large a) :
    Codec.MemoryFrame before after large := by
  intro a outside
  exact h a (fun inside => outside (included a inside))

/-- Recursive calls may change only their output subrange and activation.
Readonly aliases are transported by the storage owner's frame lemmas. -/
theorem frame_append {before middle after : DataMem} {first second : Codec.Footprint}
    (hfirst : Codec.MemoryFrame before middle first)
    (hsecond : Codec.MemoryFrame middle after second) :
    Codec.MemoryFrame before after (fun a => first a ∨ second a) := by
  intro a outside
  exact (hsecond a (fun inside => outside (Or.inr inside))).trans
    (hfirst a (fun inside => outside (Or.inl inside)))

end SszX86.CodecEmit
