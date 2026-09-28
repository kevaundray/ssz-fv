import SszX86.BitVectorMemory

namespace SszX86.BitVector
open SszNative UintCodec

/-- A byte-exact write frame, used to compose caller work with actual helper
reservations. No ownership is granted to gaps or reservation alignment padding. -/
def RegionsFrame (before after : DataMem) (spans : List (Nat × Nat)) : Prop :=
  ∀ a : BitVec 64, (∀ span ∈ spans, Body.Outside a.toNat span.1 span.2) →
    after.get? a = before.get? a

theorem RegionsFrame.refl (m : DataMem) (spans : List (Nat × Nat)) :
    RegionsFrame m m spans := fun _ _ => rfl

theorem RegionsFrame.weaken {before after : DataMem} {small large : List (Nat × Nat)}
    (frame : RegionsFrame before after small) (included : ∀ span ∈ small, span ∈ large) :
    RegionsFrame before after large := by
  intro a outside
  exact frame a (fun span hspan => outside span (included span hspan))

theorem RegionsFrame.trans {first second third : DataMem} {left right : List (Nat × Nat)}
    (before : RegionsFrame first second left) (after : RegionsFrame second third right) :
    RegionsFrame first third (left ++ right) := by
  intro a outside
  exact (after a (fun span member => outside span (List.mem_append_right _ member))).trans
    (before a (fun span member => outside span (List.mem_append_left _ member)))

theorem store_regions_frame (m : DataMem) (address : BitVec 64) (count : Nat) (value : Int)
    (bound : address.toNat + count ≤ 2^64) :
    RegionsFrame m (Mem.storeInt m address count value) [(address.toNat, count)] := by
  intro a outside
  have apart := outside (address.toNat, count) (by simp)
  apply memmove_store_lookup_outside
  intro i hi
  exact Body.outside_byte address a count i bound apart (by simpa only [Int.toBytes_length] using hi)

theorem RegionsFrame.load {before after : DataMem} {spans : List (Nat × Nat)}
    (frame : RegionsFrame before after spans) (p n : Nat) (bound : p + n ≤ 2^64)
    (apart : ∀ span ∈ spans, Body.Apart p n span.1 span.2) :
    Mem.loadInt after (BitVec.ofNat 64 p) n = Mem.loadInt before (BitVec.ofNat 64 p) n := by
  apply memmove_loadInt_congr
  intro i hi
  rw [← BitVec.ofNat_add]
  apply frame
  intro span member
  have separated := apart span member
  have inside : p + i < 2^64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt inside]
  unfold Body.Outside Body.Apart at *
  omega

theorem RegionsFrame.width {before after : DataMem} {spans : List (Nat × Nat)}
    (frame : RegionsFrame before after spans) (p n : Nat) (bound : p + n ≤ 2^64)
    (apart : ∀ span ∈ spans, Body.Apart p n span.1 span.2) :
    widthLoad after p n = widthLoad before p n := by
  unfold widthLoad
  rw [frame.load p n bound apart]

theorem RegionsFrame.operand {before after : DataMem} {spans : List (Nat × Nat)}
    (frame : RegionsFrame before after spans) (operand : NatOperand)
    (stored : operand.At (widthLoad before))
    (apart : ∀ pointer words, operand = .large pointer words →
      ∀ span ∈ spans, Body.Apart pointer.toNat (8 * words.length) span.1 span.2) :
    operand.At (widthLoad after) := by
  cases operand with
  | small limb => trivial
  | large pointer words =>
    obtain ⟨positive, aligned, bound, limbs⟩ := stored
    refine ⟨positive, aligned, bound, ?_⟩
    intro i
    rw [frame.width (pointer.toNat + 8 * i.val) 8 (by have := i.isLt; omega)]
    · exact limbs i
    · intro span member
      have separated := apart pointer words rfl span member
      have := i.isLt
      unfold Body.Apart at *
      omega

theorem RegionsFrame.bytes {before after : DataMem} {spans : List (Nat × Nat)}
    (frame : RegionsFrame before after spans) (pointer : Nat) (data : Ssz.Bytes)
    (bound : pointer + data.size ≤ 2^64)
    (stored : SszNative.ByteView.BytesAt (widthLoad before) pointer data)
    (apart : ∀ span ∈ spans, Body.Apart pointer data.size span.1 span.2) :
    SszNative.ByteView.BytesAt (widthLoad after) pointer data := by
  intro i hi
  rw [frame.width (pointer + i) 1 (by omega)]
  · exact stored i hi
  · intro span member
    have separated := apart span member
    unfold Body.Apart at *
    omega

end SszX86.BitVector
