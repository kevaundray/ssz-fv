import SszArm.CodecStorageProjection

set_option autoImplicit false

namespace SszArm.Codec.Measure

open SszNative.CodecMeasure (Parts)
open Delimited (Span MemoryFrame)
open Storage (Image)

/-- The actual native Parts niche: repeated uses null at +0 and a descriptor
pointer at +8; fields uses a non-null Field slice pointer at +0 and length at +8.
These are the words loaded at measure_parts+28 and measure_child+40, and stored
by measure+1000 (fields) / measure+3072,+3076 (repeated). No Rust enum tag is
inferred from declaration order. -/
def partsImage (address : Nat) : Parts → Image
  | .repeated element => Storage.record address 16 8 (
      .word address 8 0 ⋏ .existsPointer fun pointer =>
        .word (address + 8) 8 pointer ⋏ Storage.desc pointer element)
  | .fields fields => Storage.record address 16 8 (
      .existsPointer fun pointer => .word address 8 pointer ⋏
        .word (address + 8) 8 fields.length ⋏
        Storage.slice pointer fields.length 24 8 ⋏ Storage.fieldEntries pointer fields)

def PartsAt (s : ArmState) (address : Nat) (parts : Parts) : Prop :=
  (partsImage address parts).At s

def PartsOwned (writes : List Span) (s : ArmState) (address : Nat) (parts : Parts) : Prop :=
  (partsImage address parts).Owned writes s

theorem parts_at {writes s address parts} (input : PartsOwned writes s address parts) :
    PartsAt s address parts := input.at

theorem parts_preserved {writes s t address parts} (input : PartsOwned writes s address parts)
    (frame : MemoryFrame writes s t) : PartsOwned writes t address parts :=
  Storage.Image.preserved _ frame input

theorem parts_physical {s address parts} (input : PartsAt s address parts) :
    Storage.Physical address 16 8 := by
  cases parts <;> exact input.1.1

theorem repeated_header {s address element} (input : PartsAt s address (.repeated element)) :
    UintCodec.widthLoad s address 8 = some 0 ∧
      ∃ pointer, UintCodec.widthLoad s (address + 8) 8 = some pointer ∧
        Storage.DescAt s pointer element := by
  obtain ⟨pointer, word, child⟩ := input.2.2
  exact ⟨input.2.1.2.2, pointer, word.2.2, child⟩

theorem fields_header {s address fields} (input : PartsAt s address (.fields fields)) :
    ∃ pointer, UintCodec.widthLoad s address 8 = some pointer ∧
      UintCodec.widthLoad s (address + 8) 8 = some fields.length ∧
      Storage.Physical pointer (fields.length * 24) 8 ∧
      (Storage.fieldEntries pointer fields).At s := by
  obtain ⟨pointer, word, length, physical, children⟩ := input.2
  exact ⟨pointer, word.2.2, length.2.2, physical, children⟩

theorem fields_nonnull {s address fields} (input : PartsAt s address (.fields fields)) :
    read_mem_bytes 8 (BitVec.ofNat 64 address) s ≠ 0#64 := by
  obtain ⟨pointer, word, length, physical, children⟩ := fields_header input
  have read : (read_mem_bytes 8 (BitVec.ofNat 64 address) s).toNat = pointer := Option.some.inj word
  intro zero
  rw [zero] at read
  have positive := physical.1
  simp only [BitVec.toNat_ofNat] at read
  omega

end SszArm.Codec.Measure
