import SszArm.EmitMemory
import SszCodecMeasure
import SszCodecDecodeCore

namespace SszArm.Codec.Storage

open SszNative (NatOperand)
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

/-- Physical geometry is not an assertion that every byte is initialized. -/
def Physical (address bytes alignment : Nat) : Prop :=
  0 < address ∧ address % alignment = 0 ∧ address + bytes ≤ 2^64 ∧ bytes < 2^63

def Backing (protect : Nat → Nat → Prop) : NatOperand → Prop
  | .small _ => True
  | .large pointer words =>
      8 * words.length < 2^63 ∧ protect pointer.toNat (8 * words.length)

/-- A compositional description of meaningful observations. Existential pointers
permit arbitrary immutable aliasing. No constructor observes enum padding. -/
inductive Image where
  | pure (fact : Prop)
  | region (address size alignment : Nat)
  | word (address bytes value : Nat)
  | operand (address : Nat) (value : NatOperand)
  | bytes (address : Nat) (value : Ssz.Bytes)
  | both (left right : Image)
  | existsPointer (body : Nat → Image)

namespace Image

def Holds (protect : Nat → Nat → Prop) (s : ArmState) : Image → Prop
  | .pure fact => fact
  | .region address size alignment => Physical address size alignment ∧ protect address size
  | .word address size value =>
      address + size ≤ 2^64 ∧ protect address size ∧
        widthLoad s address size = some value
  | .operand address value =>
      address + 16 ≤ 2^64 ∧ protect address 16 ∧ Backing protect value ∧
        SszNative.NatArithmetic.operandAt (widthLoad s) address value
  | .bytes address value =>
      address + value.size ≤ 2^64 ∧ protect address value.size ∧
        SszNative.ByteView.BytesAt (widthLoad s) address value
  | .both left right => left.Holds protect s ∧ right.Holds protect s
  | .existsPointer body => ∃ pointer, (body pointer).Holds protect s

def At (s : ArmState) (image : Image) : Prop := image.Holds (fun _ _ => True) s

def Owned (writes : List Span) (s : ArmState) (image : Image) : Prop :=
  image.Holds (Protected writes) s

theorem weaken {p q : Nat → Nat → Prop} {s : ArmState} (image : Image)
    (weaker : ∀ a n, p a n → q a n) (input : image.Holds p s) : image.Holds q s := by
  induction image with
  | pure fact => exact input
  | region a n alignment => exact ⟨input.1, weaker a n input.2⟩
  | word a n v => exact ⟨input.1, weaker a n input.2.1, input.2.2⟩
  | operand a v =>
      refine ⟨input.1, weaker a 16 input.2.1, ?_, input.2.2.2⟩
      cases v with
      | small word => trivial
      | large pointer words => exact ⟨input.2.2.1.1, weaker _ _ input.2.2.1.2⟩
  | bytes a v => exact ⟨input.1, weaker a v.size input.2.1, input.2.2⟩
  | both l r il ir => exact ⟨il input.1, ir input.2⟩
  | existsPointer body ih =>
      obtain ⟨pointer, stored⟩ := input
      exact ⟨pointer, ih pointer stored⟩

theorem Owned.at {writes : List Span} {s : ArmState} {image : Image}
    (input : image.Owned writes s) : image.At s :=
  image.weaken (fun _ _ _ => True.intro) input

theorem preserved {writes : List Span} {s t : ArmState} (image : Image)
    (frame : MemoryFrame writes s t) (input : image.Owned writes s) :
    image.Owned writes t := by
  induction image with
  | pure fact => exact input
  | region a n alignment => exact input
  | word a n v =>
      exact ⟨input.1, input.2.1, (frame.load a n input.1 input.2.1).trans input.2.2⟩
  | operand a v =>
      refine ⟨input.1, input.2.1, input.2.2.1, ?_⟩
      apply Emit.operand_header_preserved frame a v input.1 input.2.1 _ input.2.2.2
      cases v with
      | small word => trivial
      | large pointer words => exact input.2.2.1.2
  | bytes a v =>
      refine ⟨input.1, input.2.1, ?_⟩
      intro i hi
      rw [frame.load (a + i) 1 (by have bound := input.1; omega)
        (input.2.1.subspan i 1 (by omega))]
      exact input.2.2 i hi
  | both l r il ir => exact ⟨il input.1, ir input.2⟩
  | existsPointer body ih =>
      obtain ⟨pointer, stored⟩ := input
      exact ⟨pointer, ih pointer stored⟩

end Image

infixr:35 " ⋏ " => Image.both

def record (address bytes alignment : Nat) (fields : Image) : Image :=
  .region address bytes alignment ⋏ fields

def slice (address count stride alignment : Nat) : Image :=
  .pure (Physical address (count * stride) alignment)

def optionOperand (address : Nat) : Option NatOperand → Image
  | none => .word address 8 0
  | some number => .word address 8 1 ⋏ .operand (address + 8) number

/-- Only initialized entries are observed; the reservation can be longer. -/
def entries {α : Type} (entry : Nat → α → Image) (stride address : Nat) : List α → Image
  | [] => .pure True
  | value :: rest => entry address value ⋏ entries entry stride (address + stride) rest

theorem prefix_head {α : Type} (entry : Nat → α → Image) (stride address : Nat)
    (value : α) (rest : List α) {p : Nat → Nat → Prop} {s : ArmState}
    (input : (entries entry stride address (value :: rest)).Holds p s) :
    (entry address value).Holds p s := input.1

theorem prefix_tail {α : Type} (entry : Nat → α → Image) (stride address : Nat)
    (value : α) (rest : List α) {p : Nat → Nat → Prop} {s : ArmState}
    (input : (entries entry stride address (value :: rest)).Holds p s) :
    (entries entry stride (address + stride) rest).Holds p s := input.2

end SszArm.Codec.Storage
