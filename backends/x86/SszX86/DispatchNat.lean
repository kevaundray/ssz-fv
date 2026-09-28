import SszX86.DispatchOwned

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

/-- A physical two-word native Nat. Borrowing is determined solely by the
original non-null pointer and physical count, without canonicality constraints. -/
structure NatOwned (s : MachineData) (address capacity used : BitVec 64)
    (slot value : Nat) : Prop where
  header : ReadOnly s address capacity used slot 16
  «at» : NatMemory.At (widthLoad s.dmem) slot value
  borrowed : ∀ p count, 0 < p →
    widthLoad s.dmem slot 8 = some p → widthLoad s.dmem (slot + 8) 8 = some count →
    ReadOnly s address capacity used p (8 * count)

theorem NatOwned.pointer {s : MachineData} {address capacity used : BitVec 64}
    {slot value : Nat} (h : NatOwned s address capacity used slot value)
    (low : 472 ≤ s.regs.rsp.toNat) :
    widthLoad (savedMem s) slot 8 = widthLoad s.dmem slot 8 := by
  simpa only [Nat.add_zero] using (h.header.subrange 0 8 (by decide)).width low

theorem NatOwned.payload {s : MachineData} {address capacity used : BitVec 64}
    {slot value : Nat} (h : NatOwned s address capacity used slot value)
    (low : 472 ≤ s.regs.rsp.toNat) :
    widthLoad (savedMem s) (slot + 8) 8 = widthLoad s.dmem (slot + 8) 8 :=
  (h.header.subrange 8 8 (by decide)).width low

theorem NatOwned.large_protected {s : MachineData} {address capacity used : BitVec 64}
    {slot value : Nat} (h : NatOwned s address capacity used slot value)
    (low : 472 ≤ s.regs.rsp.toNat) (p : Nat) (words : List (BitVec 64))
    (stored : NatMemory.largeAt (widthLoad (savedMem s)) slot p words) :
    ReadOnly s address capacity used p (8 * words.length) := by
  rcases stored with ⟨positive, _, _, _, pointer, payload, _⟩
  rw [h.pointer low] at pointer
  rw [h.payload low] at payload
  exact h.borrowed p words.length positive pointer payload

theorem NatOwned.represented {s : MachineData} {address capacity used : BitVec 64}
    {slot value : Nat} (h : NatOwned s address capacity used slot value)
    (low : 472 ≤ s.regs.rsp.toNat) :
    NatMemory.At (widthLoad (savedMem s)) slot value := by
  rcases h.at with ⟨⟨pointer, payload⟩, bound⟩ | ⟨p, words, stored, value⟩
  · exact Or.inl ⟨⟨by rw [h.pointer low]; exact pointer,
      by rw [h.payload low]; exact payload⟩, bound⟩
  · rcases stored with ⟨positive, high, aligned, bound, pointer, payload, bytes⟩
    have limbRegion := h.borrowed p words.length positive pointer payload
    refine Or.inr ⟨p, words, ⟨positive, high, aligned, bound, ?_, ?_, ?_⟩, value⟩
    · rw [h.pointer low]; exact pointer
    · rw [h.payload low]; exact payload
    · intro i
      rw [(limbRegion.subrange (8 * i.val) 8 (by have := i.isLt; omega)).width low]
      exact bytes i

structure OptionOwned (s : MachineData) (address capacity used : BitVec 64)
    (slot : Nat) (limit : Option Nat) : Prop where
  header : ReadOnly s address capacity used slot 24
  «at» : NatMemory.OptionAt (widthLoad s.dmem) slot limit
  payload : ∀ cap, limit = some cap → NatOwned s address capacity used (slot + 8) cap

theorem OptionOwned.represented {s : MachineData} {address capacity used : BitVec 64}
    {slot : Nat} {limit : Option Nat} (h : OptionOwned s address capacity used slot limit)
    (low : 472 ≤ s.regs.rsp.toNat) :
    NatMemory.OptionAt (widthLoad (savedMem s)) slot limit := by
  have tag := (h.header.subrange 0 4 (by decide)).width low
  simp only [Nat.add_zero] at tag
  cases limit with
  | none => change widthLoad (savedMem s) slot 4 = some 0; rw [tag]; exact h.at
  | some cap =>
    exact ⟨by rw [tag]; exact h.at.1, (h.payload cap rfl).represented low⟩

end SszX86.Dispatch
