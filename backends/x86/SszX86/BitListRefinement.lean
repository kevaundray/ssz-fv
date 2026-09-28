import SszX86.BitListProofs

namespace SszX86.BitList
open SszNative UintCodec BoolCodec

/-- All native resources and ABI facts accompany the pinned BitList result. -/
theorem list_refines (e : Executable) (base : Int64) (code : JointCodeAt e base)
    (s : MachineData) (saved : Saved) (cap : Nat) (pointer payload : BitVec 64)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : ListOwned s saved cap pointer payload data address capacity used) :
    Eventually (step e) (fun t =>
      Post s saved false (some cap) data address capacity used t ∧
      if SszNative.Delimited.Exhausted data ⟨address.toNat, capacity.toNat, used.toNat⟩ then
        SszNative.UintCodec.errorAt (widthLoad t.1.dmem) s.regs.rdi.toNat 32768 0 0
      else SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
        (Ssz.deserialize (.bitList cap) data))
      (s, base + Int64.ofNat listEntry) := by
  apply eventually_weaken _ _ _ _ _
    (list_correct e base code s saved cap pointer payload data address capacity used h)
  intro t post
  exact ⟨post, post.list_refines h.toOwned⟩

/-- Both None and arbitrary Some representations use the true tail entry. -/
theorem progressive_refines (e : Executable) (base : Int64) (code : JointCodeAt e base)
    (s : MachineData) (saved : Saved) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64)
    (h : ProgressiveOwned s saved limit data address capacity used) :
    Eventually (step e) (fun t =>
      Post s saved true limit data address capacity used t ∧
      if SszNative.Delimited.Exhausted data ⟨address.toNat, capacity.toNat, used.toNat⟩ then
        SszNative.UintCodec.errorAt (widthLoad t.1.dmem) s.regs.rdi.toNat 32768 0 0
      else SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
        (Ssz.deserialize (.progressiveBitList limit) data))
      (s, base + Int64.ofNat progressiveEntry) := by
  apply eventually_weaken _ _ _ _ _
    (progressive_correct e base code s saved limit data address capacity used h)
  intro t post
  exact ⟨post, post.progressive_refines h.toOwned⟩

theorem list_borrowed_preserved {s : MachineData} {saved : Saved} {cap : Nat}
    {pointer payload : BitVec 64} {data : Ssz.Bytes} {address capacity used : BitVec 64}
    {t : MachineState} (h : ListOwned s saved cap pointer payload data address capacity used)
    (post : Post s saved false (some cap) data address capacity used t)
    (limbs : List (BitVec 64))
    (stored : NatMemory.largeAt (widthLoad s.dmem) (s.regs.rbp.toNat + 8) pointer.toNat limbs) :
    ∀ i < 8 * limbs.length,
      t.1.dmem.get? (BitVec.ofNat 64 (pointer.toNat + i)) =
      s.dmem.get? (BitVec.ofNat 64 (pointer.toNat + i)) :=
  post.preserves_region h.toOwned _ _ (h.borrowed limbs stored)

theorem progressive_borrowed_preserved {s : MachineData} {saved : Saved} {limit : Option Nat}
    {data : Ssz.Bytes} {address capacity used : BitVec 64} {t : MachineState}
    (h : ProgressiveOwned s saved limit data address capacity used)
    (post : Post s saved true limit data address capacity used t)
    (cap p : Nat) (limbs : List (BitVec 64)) (selected : limit = some cap)
    (stored : NatMemory.largeAt (widthLoad s.dmem) (s.regs.rbp.toNat + 16) p limbs) :
    ∀ i < 8 * limbs.length,
      t.1.dmem.get? (BitVec.ofNat 64 (p + i)) = s.dmem.get? (BitVec.ofNat 64 (p + i)) :=
  post.preserves_region h.toOwned _ _ (h.borrowed cap selected p limbs stored)

end SszX86.BitList
