import SszX86.CodecStorageBase
import SszNatShiftResources
import SszTypedArena

set_option autoImplicit false

namespace SszX86.IndicesNatShr
open SszNative UintCodec

/-- Concatenating initializer segments composes the existing exact ascending
store sequence. This also handles empty segments without claiming a write. -/
theorem fill_append (m : DataMem) (p : BitVec 64) (position : Nat)
    (prefix suffix : List (BitVec 64)) :
    Large.fillMem m p position (prefix ++ suffix) =
      Large.fillMem (Large.fillMem m p position prefix) p
        (position + prefix.length) suffix := by
  induction prefix generalizing m position with
  | nil => simp only [List.nil_append, Large.fillMem, List.length_nil, Nat.add_zero]
  | cons first rest ih =>
      simp only [List.cons_append, Large.fillMem, List.length_cons]
      rw [ih]
      congr 1
      omega

/-- Previously mapped caller bytes remain mapped through every limb store;
no disjointness is required merely to retain mapping. -/
theorem fill_mapped (m : DataMem) (p q : BitVec 64) (position bytes : Nat)
    (words : List (BitVec 64)) (mapped : Large.Mapped m q bytes) :
    Large.Mapped (Large.fillMem m p position words) q bytes := by
  induction words generalizing m position with
  | nil => exact mapped
  | cons first rest ih =>
      exact ih _ (position + 1) (Large.mapped_store _ _ _ _ _ _ mapped)

/-- The exact byte frame for a complete or partial initializer sequence. Opaque
padding and unused arena suffixes are outside this footprint. -/
theorem fill_frame (m : DataMem) (p : BitVec 64) (words : List (BitVec 64)) :
    Codec.MemoryFrame m (Large.fillMem m p 0 words)
      (fun a => Codec.InSpan a p (8 * words.length)) := by
  intro address outside
  apply Large.fill_frame
  intro index _ inside equal
  exact outside ⟨index, by simpa only [Nat.zero_add] using inside, equal⟩

/-- Arbitrarily aliased readonly Nat objects are transported through the exact
write frame. Only separation from the fresh mutable buffer is required. -/
theorem fill_preserves_nat (m : DataMem) (p q : BitVec 64)
    (words : List (BitVec 64)) (readable : Codec.Footprint) (operand : NatOperand)
    (stored : Codec.NatAt m readable q operand)
    (separate : ∀ a, readable a → ¬ Codec.InSpan a p (8 * words.length)) :
    Codec.NatAt (Large.fillMem m p 0 words) readable q operand :=
  stored.frame (fill_frame m p words) separate

/-- A positive u64 reservation inherits mapping from the original arena. Its
alignment gap is not included in the initialized limb span. -/
theorem reserved_mapped (m : DataMem) (base : BitVec 64) (capacity used count : Nat)
    (reservation : Arena.Reservation) (positive : 0 < count)
    (reserved : TypedArena.reserve ⟨8, 3⟩ base.toNat capacity used count = some reservation)
    (mapped : Large.Mapped m base capacity) :
    Large.Mapped m (BitVec.ofNat 64 reservation.pointer) (8 * count) := by
  rw [TypedArena.reserve_u64] at reserved
  obtain ⟨checks, shape⟩ :=
    (Arena.reserve_eq_some_iff_checks _ _ _ _ positive reservation).mp reserved
  have pointer : BitVec.ofNat 64 reservation.pointer =
      base + BitVec.ofNat 64 (Arena.start base.toNat used) := by
    rw [shape]
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  intro index inside
  rw [pointer, memmove_addr_add]
  apply mapped
  have fits := checks.2.2.2.2.2
  unfold Arena.finish at fits
  omega

/-- Physical output ownership after exactly the reserved ascending limb writes.
The output retains all written limbs, including a zero high limb. This is a
memory transformer theorem; instruction execution is a separate obligation. -/
theorem reserved_fill (m : DataMem) (base capacity used count : Nat)
    (valid : Arena.Valid base capacity used) (positive : 0 < count)
    (reservation : Arena.Reservation)
    (reserved : TypedArena.reserve ⟨8, 3⟩ base capacity used count = some reservation)
    (words : List (BitVec 64)) (length : words.length = count) :
    (.large (BitVec.ofNat 64 reservation.pointer) words : NatOperand).At
        (widthLoad (Large.fillMem m (BitVec.ofNat 64 reservation.pointer) 0 words)) ∧
      base + used ≤ reservation.pointer ∧
      reservation.pointer + 8 * words.length = base + reservation.used ∧
      used < reservation.used ∧ reservation.used ≤ capacity ∧
      Codec.MemoryFrame m (Large.fillMem m (BitVec.ofNat 64 reservation.pointer) 0 words)
        (fun a => Codec.InSpan a (BitVec.ofNat 64 reservation.pointer) (8 * words.length)) := by
  rw [TypedArena.reserve_u64] at reserved
  obtain ⟨aligned, nonnull, pointerBound, consumed, fits, prefix, finish, _, bound⟩ :=
    Arena.success_properties base capacity used count valid positive reservation reserved
  have pointer : (BitVec.ofNat 64 reservation.pointer).toNat = reservation.pointer :=
    Nat.mod_eq_of_lt pointerBound
  have outputBound : (BitVec.ofNat 64 reservation.pointer).toNat + 8 * words.length ≤ 2 ^ 64 := by
    rw [pointer, length]
    exact bound
  refine ⟨?_, prefix, ?_, consumed, fits, fill_frame _ _ _⟩
  · exact ⟨by simpa only [pointer] using nonnull,
      by simpa only [pointer] using aligned, outputBound,
      Large.fill_wordsAt _ _ _ outputBound⟩
  · simpa only [length] using finish

/-- An initialized prefix owns exactly its recorded values; the untouched suffix
need only be mapped. No canonicality or successful future continuation is used. -/
theorem initialized_prefix (m : DataMem) (p : BitVec 64)
    (words : List (BitVec 64)) (initialized : Nat)
    (bound : p.toNat + 8 * words.length ≤ 2 ^ 64) :
    NatMemory.wordsAt (widthLoad (Large.fillMem m p 0 (words.take initialized)))
      p.toNat (words.take initialized) := by
  apply Large.fill_wordsAt
  have length : (words.take initialized).length ≤ words.length := by simp
  omega

end SszX86.IndicesNatShr
