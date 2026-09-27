import SszLimbs

set_option autoImplicit false

namespace SszNative.NatMemory

/-- The pinned Rust Small representation: a null niche and one unsigned word.
The loader may use absolute addresses or offsets relative to a containing object. -/
def smallAt (load : Nat → Nat → Option Nat) (address value : Nat) : Prop :=
  load address 8 = some 0 ∧ load (address + 8) 8 = some value

/-- A little-endian limb slice in absolute machine memory. High zero limbs are
permitted, matching publicly supplied native Large values. -/
def wordsAt (load : Nat → Nat → Option Nat) (pointer : Nat)
    (words : List (BitVec 64)) : Prop :=
  ∀ i : Fin words.length, load (pointer + 8 * i.val) 8 = some words[i].toNat

/-- Native Large stores a non-null limb pointer and a machine-sized slice length.
These are representation conditions, not an allocator or pointer-provenance proof. -/
def largeAt (load : Nat → Nat → Option Nat) (address pointer : Nat)
    (words : List (BitVec 64)) : Prop :=
  0 < pointer ∧ pointer < 2 ^ 64 ∧ pointer % 8 = 0 ∧
  pointer + 8 * words.length ≤ 2 ^ 64 ∧
  load address 8 = some pointer ∧ load (address + 8) 8 = some words.length ∧
  wordsAt load pointer words

/-- An exact natural value in the internal native representation. This relation
uses absolute addresses; it does not impose canonicality on borrowed Large inputs. -/
def At (load : Nat → Nat → Option Nat) (address value : Nat) : Prop :=
  (smallAt load address value ∧ value < 2 ^ 64) ∨
  ∃ pointer words, largeAt load address pointer words ∧ SszNative.Limbs.value words = value

end SszNative.NatMemory
