import SszCodecDecodeCore

namespace SszArm.Codec.Decode.Reserve

open SszNative

/-- Every completed typed reservation, including zero-count and ZST cases,
certifies the positive-isize product bound used by the compiled initializers. -/
theorem reserved_bytes (layout : TypedArena.Layout) (base capacity used count : Nat)
    (reservation : Arena.Reservation)
    (reserved : TypedArena.reserve layout base capacity used count = some reservation) :
    layout.size * count < 2 ^ 63 := by
  unfold TypedArena.reserve at reserved
  split at reserved
  · rename_i empty
    rcases empty with zero | zero <;> simp [zero]
  · split at reserved
    · rename_i checked
      exact checked.1
    · cases reserved

/-- `decode_struct_values` omits UMULH only after the actual Slot reservation.
This is a consequence of committed physical storage, never a metadata cap. -/
theorem values_product_of_slots (base capacity used count : Nat)
    (reservation : Arena.Reservation)
    (reserved : TypedArena.reserve CodecDecode.slotLayout base capacity used count = some reservation) :
    CodecDecode.valueLayout.size * count < 2 ^ 64 := by
  have bound := reserved_bytes CodecDecode.slotLayout base capacity used count reservation reserved
  simp only [CodecDecode.slotLayout, CodecDecode.valueLayout] at bound ⊢
  omega

/-- Offset-table callers have already checked the physical table against the
scope before using the specialized Value allocator without a high-product test. -/
theorem values_product_of_offsets (count scope : Nat)
    (table : 4 * count ≤ scope) (composite : scope < 2 ^ 32) :
    CodecDecode.valueLayout.size * count < 2 ^ 63 := by
  simp only [CodecDecode.valueLayout]
  omega

/-- The high-product guard precedes the sign-bit guard in decode_fixed. Their
conjunction is exactly the typed arena's stronger positive-isize product guard. -/
theorem value_product_guards (count : Nat) :
    (CodecDecode.valueLayout.size * count < 2 ^ 64 ∧
      CodecDecode.valueLayout.size * count < 2 ^ 63) ↔
    CodecDecode.valueLayout.size * count < 2 ^ 63 := by
  omega

/-- Native CMN(address,16)/B.HI permits the final aligned sixteen-byte address;
its strictness is exactly the checked addition by alignment-minus-one. -/
theorem value_alignment_guard (address : Nat) :
    address ≤ 2 ^ 64 - 16 ↔ address + (CodecDecode.valueLayout.alignment - 1) < 2 ^ 64 := by
  simp only [CodecDecode.valueLayout, TypedArena.Layout.alignment]
  omega

theorem slot_alignment_guard (address : Nat) :
    address ≤ 2 ^ 64 - 8 ↔ address + (CodecDecode.slotLayout.alignment - 1) < 2 ^ 64 := by
  simp only [CodecDecode.slotLayout, TypedArena.Layout.alignment]
  omega

/-- Empty typed arrays return the layout's dangling pointer without inspecting
base, capacity or even an invalid incoming cursor. -/
theorem value_zero (base capacity used : Nat) :
    TypedArena.reserve CodecDecode.valueLayout base capacity used 0 = some ⟨16, used⟩ := by
  exact TypedArena.reserve_zero _ _ _ _

theorem slot_zero (base capacity used : Nat) :
    TypedArena.reserve CodecDecode.slotLayout base capacity used 0 = some ⟨8, used⟩ := by
  exact TypedArena.reserve_zero _ _ _ _

theorem positive_table_has_offset (count scope : Nat) (positive : 0 < count)
    (table : 4 * count ≤ scope) : 4 ≤ scope := by
  omega

end SszArm.Codec.Decode.Reserve
