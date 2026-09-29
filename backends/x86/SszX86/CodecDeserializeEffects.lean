import SszX86.CodecDeserializeWords
import SszCodecDecodeResourcesPrefix
import SszBitVectorMemory

set_option autoImplicit false

namespace SszX86.CodecDeserialize
open SszNative UintCodec

/-- Actual payload-write regions of the existing operational effects. A typed
reservation alone writes no payload: uninitialized array suffixes and alignment
gaps are therefore absent from this footprint. -/
def effectRegions : CodecDecode.Effect → List (Nat × Nat)
  | .fixedSize _ _ call => call.calls.flatMap BitVector.allocationWrites
  | .add _ _ _ call | .mul _ _ _ call => BitVector.allocationWrites call
  | .uint _ _ _ none _ => []
  | .uint _ _ _ (some allocation) words => [(allocation.pointer, 8 * words.length)]
  | .bitVector _ _ _ call => call.writes
  | .delimited _ _ _ call =>
    match call.allocation with
    | none => []
    | some allocation => [(allocation.pointer, 16)]
  | .reserve _ _ _ _ => []
  | .writeSlot address _ _ => [(address, 40)]
  | .writeValue address _ _ => [(address, 48)]

def EffectWrites (effects : List CodecDecode.Effect) : Codec.Footprint := fun a =>
  ∃ effect ∈ effects, ∃ region ∈ effectRegions effect,
    Codec.InSpan a (BitVec.ofNat 64 region.1) region.2

/-- Arithmetic allocations retain every written limb, even on later failure. -/
def effectWordsAt (m : DataMem) : CodecDecode.Effect → Prop
  | .fixedSize _ _ call => ∀ arithmetic ∈ call.calls,
      BitVector.allocationAt (widthLoad m) arithmetic
  | .add _ _ _ call | .mul _ _ _ call => BitVector.allocationAt (widthLoad m) call
  | .uint _ _ _ none _ => True
  | .uint _ _ _ (some allocation) words => NatMemory.wordsAt (widthLoad m) allocation.pointer words
  | .bitVector _ _ _ call => call.writtenAt (widthLoad m)
  | .delimited _ _ _ call => Delimited.Outcome.PreparedAt (widthLoad m) call
  | .reserve _ _ _ _ | .writeSlot _ _ _ | .writeValue _ _ _ => True

/-- A Slot can be updated several times during width planning and validation.
Only its last actual event is observed in the final machine memory. -/
def LastSlot (effects : List CodecDecode.Effect) (address : Nat) (slot : CodecDecode.Slot) : Prop :=
  ∃ before after index,
    effects = before ++ .writeSlot address index slot :: after ∧
    ∀ laterIndex laterSlot, .writeSlot address laterIndex laterSlot ∉ after

/-- Exact initialized prefixes, as already computed by the shared event fold;
there is deliberately no requirement on a reserved but unwritten Value slot. -/
structure EffectsAt (m : DataMem) (readable : Codec.Footprint) (source : BitVec 64)
    (effects : List CodecDecode.Effect) : Prop where
  words : ∀ effect ∈ effects, effectWordsAt m effect
  values : ∀ address node,
    CodecDecode.storeValues effects (fun _ => none) address = some node →
    Codec.NodeAt m readable source (BitVec.ofNat 64 address) node
  slots : ∀ address slot, LastSlot effects address slot →
    Codec.SlotAt m readable (BitVec.ofNat 64 address) slot

theorem effectWrites_nil (a : BitVec 64) : ¬ EffectWrites [] a := by
  rintro ⟨effect, member, rest⟩
  cases member

theorem effectWrites_append (first second : List CodecDecode.Effect) (a : BitVec 64) :
    EffectWrites (first ++ second) a ↔ EffectWrites first a ∨ EffectWrites second a := by
  constructor
  · rintro ⟨effect, member, region, regionMember, inside⟩
    rcases List.mem_append.mp member with left | right
    · exact Or.inl ⟨effect, left, region, regionMember, inside⟩
    · exact Or.inr ⟨effect, right, region, regionMember, inside⟩
  · rintro (⟨effect, member, region, regionMember, inside⟩ |
      ⟨effect, member, region, regionMember, inside⟩)
    · exact ⟨effect, List.mem_append_left _ member, region, regionMember, inside⟩
    · exact ⟨effect, List.mem_append_right _ member, region, regionMember, inside⟩

theorem reserve_payload_untouched (layout : TypedArena.Layout) (count : Nat)
    (arena : Delimited.ArenaState) (allocation : Option Arena.Reservation) (a : BitVec 64) :
    ¬ EffectWrites [.reserve layout count arena allocation] a := by
  rintro ⟨effect, member, region, regionMember, inside⟩
  have same : effect = .reserve layout count arena allocation := by simpa using member
  subst effect
  cases regionMember

theorem writeValue_footprint (address index : Nat) (node : CodecDecode.Node) (a : BitVec 64) :
    EffectWrites [.writeValue address index node] a ↔
      Codec.InSpan a (BitVec.ofNat 64 address) 48 := by
  simp [EffectWrites, effectRegions]

/-- The copy's physical 48-byte range is allowed by its one existing initializer
event without claiming that padding became a meaningful initialized field. -/
theorem copyWords_effect_frame (m : DataMem) (address index : Nat)
    (node : CodecDecode.Node) (words : CodecDeserialize.ValueWords) :
    Codec.MemoryFrame m (copyWords m (BitVec.ofNat 64 address) words)
      (EffectWrites [.writeValue address index node]) := by
  intro a outside
  apply copyWords_frame
  intro inside
  exact outside ((writeValue_footprint address index node a).2 inside)

end SszX86.CodecDeserialize
