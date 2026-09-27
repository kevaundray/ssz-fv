import SszNatMemory

set_option autoImplicit false

namespace SszNative.NatMemory

/-- A native Nat passed as two machine words, without a memory-resident header.
Borrowed Large inputs may be empty or have redundant high zero limbs. Writable
region separation belongs to each callee's ownership contract, not this relation. -/
def Pair (load : Nat → Nat → Option Nat) (pointer payload : BitVec 64)
    (value : Nat) : Prop :=
  (pointer = 0#64 ∧ payload.toNat = value) ∨
  ∃ words : List (BitVec 64),
    0 < pointer.toNat ∧ pointer.toNat % 8 = 0 ∧
    pointer.toNat + 8 * words.length ≤ 2^64 ∧ payload.toNat = words.length ∧
    wordsAt load pointer.toNat words ∧ SszNative.Limbs.value words = value

/-- Storing the two argument words establishes the existing memory observation. -/
theorem Pair.at (load : Nat → Nat → Option Nat) (pointer payload : BitVec 64)
    (value address : Nat) (h : Pair load pointer payload value)
    (hp : load address 8 = some pointer.toNat)
    (hc : load (address + 8) 8 = some payload.toNat) : At load address value := by
  rcases h with ⟨rfl, hv⟩ | ⟨words, hpos, halign, hspace, hcount, hm, hv⟩
  · exact Or.inl ⟨⟨hp, by simpa only [hv] using hc⟩, hv ▸ payload.isLt⟩
  · exact Or.inr ⟨pointer.toNat, words,
      ⟨hpos, pointer.isLt, halign, hspace, hp, by simpa only [hcount] using hc, hm⟩, hv⟩

/-- Loading a valid Nat header supplies the internal two-word call argument. -/
theorem pair_of_at (load : Nat → Nat → Option Nat) (pointer payload : BitVec 64)
    (value address : Nat) (h : At load address value)
    (hp : load address 8 = some pointer.toNat)
    (hc : load (address + 8) 8 = some payload.toNat) : Pair load pointer payload value := by
  rcases h with ⟨⟨hz, hv⟩, _⟩ | ⟨p, words, ⟨hpos, _, halign, hspace, hptr, hcount, hm⟩, hv⟩
  · have hzero : pointer = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      simpa using Option.some.inj (hp.symm.trans hz)
    exact Or.inl ⟨hzero, Option.some.inj (hc.symm.trans hv)⟩
  · have hptr' : pointer.toNat = p := Option.some.inj (hp.symm.trans hptr)
    refine Or.inr ⟨words, ?_, ?_, ?_, Option.some.inj (hc.symm.trans hcount), ?_, hv⟩
    · simpa only [hptr'] using hpos
    · simpa only [hptr'] using halign
    · simpa only [hptr'] using hspace
    · simpa only [hptr'] using hm

/-- Shared Rust Option<Nat> layout. None has no payload observation; Some
retains the original Nat representation, including noncanonical Large values. -/
def OptionAt (observe : Nat → Nat → Option Nat) (address : Nat) : Option Nat → Prop
  | none => observe address 4 = some 0
  | some value => observe address 4 = some 1 ∧ At observe (address + 8) value

theorem option_some_iff_pair (observe : Nat → Nat → Option Nat) (address value : Nat)
    (pointer payload : BitVec 64)
    (hp : observe (address + 8) 8 = some pointer.toNat)
    (hw : observe (address + 8 + 8) 8 = some payload.toNat) :
    OptionAt observe address (some value) ↔
      observe address 4 = some 1 ∧ Pair observe pointer payload value := by
  constructor
  · rintro ⟨tag, repr⟩
    exact ⟨tag, pair_of_at observe pointer payload value (address + 8) repr hp hw⟩
  · rintro ⟨tag, repr⟩
    exact ⟨tag, repr.at observe pointer payload value (address + 8) hp hw⟩

end SszNative.NatMemory

namespace SszNative.NatABI

/-- Rust Ordering's signed byte ABI; higher return-register bits are not observed. -/
def orderingByte : Ordering → BitVec 8
  | .lt => 255#8
  | .eq => 0#8
  | .gt => 1#8

end SszNative.NatABI
