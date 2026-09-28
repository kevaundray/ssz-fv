import SszX86.BitListMemory

namespace SszX86.BitList
open SszNative UintCodec BoolCodec

theorem frame_preserves_region (s : MachineData) (saved : Saved) (tail : Bool)
    (limit : Option Nat) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : Owned s saved tail data address capacity used) (m : DataMem)
    (frame : Frame s tail m
      (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩).allocation)
    (p n : Nat) (hp : Protected s tail address capacity used p n) :
    ∀ i < n, m.get? (BitVec.ofNat 64 (p + i)) = s.dmem.get? (BitVec.ofNat 64 (p + i)) := by
  have physical : data.size < 2^64 := by rw [h.length]; exact s.regs.r14.toBitVec.isLt
  have resources := (SszNative.Delimited.run_resources limit data
    ⟨address.toNat, capacity.toNat, used.toNat⟩ physical).1
  intro i hi
  have within : p + i < 2^64 := by have := hp.bound; omega
  apply frame
  · have apart := hp.output
    unfold Body.Apart Body.Outside at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt within]
    omega
  · have apart := hp.work
    unfold Body.Apart Body.Outside at *
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt within]
    omega
  · intro r hr
    rw [resources] at hr
    unfold SszNative.Delimited.allocation at hr
    split at hr
    · have bounds := SszNative.Delimited.reservation_bounds address.toNat capacity.toNat used.toNat
        h.arena_bound h.arena_nonzero r hr
      have cursorApart := hp.cursor
      have arenaApart := hp.arena
      have usedBound := h.used_bound
      unfold Body.Apart Body.Outside at *
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt within]
      constructor <;> omega
    · contradiction

theorem frame_preserves_load (s : MachineData) (saved : Saved) (tail : Bool)
    (limit : Option Nat) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : Owned s saved tail data address capacity used) (m : DataMem)
    (frame : Frame s tail m
      (SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩).allocation)
    (p n j k : Nat) (hp : Protected s tail address capacity used p n) (within : j + k ≤ n) :
    Mem.loadInt m (BitVec.ofNat 64 (p + j)) k =
      Mem.loadInt s.dmem (BitVec.ofNat 64 (p + j)) k := by
  apply memmove_loadInt_congr
  intro i hi
  rw [← BitVec.ofNat_add]
  simpa only [Nat.add_assoc] using frame_preserves_region s saved tail limit data
    address capacity used h m frame p n hp (j + i) (by omega)

theorem Post.preserves_region {s : MachineData} {saved : Saved} {tail : Bool}
    {limit : Option Nat} {data : Ssz.Bytes} {address capacity used : BitVec 64}
    {t : MachineState} (h : Owned s saved tail data address capacity used)
    (post : Post s saved tail limit data address capacity used t)
    (p n : Nat) (hp : Protected s tail address capacity used p n) :
    ∀ i < n, t.1.dmem.get? (BitVec.ofNat 64 (p + i)) =
      s.dmem.get? (BitVec.ofNat 64 (p + i)) :=
  frame_preserves_region s saved tail limit data address capacity used h t.1.dmem post.frame p n hp

theorem Post.source_preserved {s : MachineData} {saved : Saved} {tail : Bool}
    {limit : Option Nat} {data : Ssz.Bytes} {address capacity used : BitVec 64}
    {t : MachineState} (h : Owned s saved tail data address capacity used)
    (post : Post s saved tail limit data address capacity used t) :
    ∀ i < data.size, t.1.dmem.get? (s.regs.rdx.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rdx.toBitVec + BitVec.ofNat 64 i) := by
  intro i hi
  simpa only [← UInt64.toNat_toBitVec, width_address] using
    post.preserves_region h _ _ h.source_owned i hi

theorem Post.descriptor_preserved {s : MachineData} {saved : Saved} {tail : Bool}
    {limit : Option Nat} {data : Ssz.Bytes} {address capacity used : BitVec 64}
    {t : MachineState} (h : Owned s saved tail data address capacity used)
    (post : Post s saved tail limit data address capacity used t) :
    ∀ i < (if tail then 32 else 24),
      t.1.dmem.get? (s.regs.rbp.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rbp.toBitVec + BitVec.ofNat 64 i) := by
  intro i hi
  simpa only [← UInt64.toNat_toBitVec, width_address] using
    post.preserves_region h _ _ h.descriptor i hi

end SszX86.BitList
