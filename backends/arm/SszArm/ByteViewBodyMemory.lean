import SszArm.ByteViewVectorWidth
import SszArm.ByteViewTails

namespace SszArm.ByteView

open UintCodec (widthLoad WidthFrame)

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

structure Owned (s : ArmState) (capacity : Nat) (data : Ssz.Bytes) : Prop where
  separated : Tail.Separated s
  input : Tail.Input s data
  descriptorHigh : (r (.GPR 1#5) s).toNat + 24 ≤ 2^64
  descriptorOutput : (r (.GPR 1#5) s).toNat + 24 ≤ (r (.GPR 0#5) s).toNat ∨
    (r (.GPR 0#5) s).toNat + 76 ≤ (r (.GPR 1#5) s).toNat
  descriptorStack : (r (.GPR 1#5) s).toNat + 24 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 1#5) s).toNat
  pair : Tail.NatPair s (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s)
    (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s) capacity

theorem Owned.width_at {s : ArmState} {capacity : Nat} {data : Ssz.Bytes}
    (ho : Owned s capacity data) :
    SszNative.NatMemory.At (widthLoad s) ((r (.GPR 1#5) s).toNat + 8) capacity := by
  apply Tail.nat_at s s _ _ capacity _ (fun _ _ _ => rfl) ho.pair
  · simp [widthLoad, BitVec.ofNat_add]
  · simp [widthLoad, BitVec.ofNat_add, Nat.add_assoc]

theorem Owned.scratch {s : ArmState} {capacity : Nat} {data : Ssz.Bytes}
    (ho : Owned s capacity data) : ScratchSeparated s := by
  refine ⟨ho.separated.stackLow, ?_⟩
  dsimp only
  intro hp hc
  rcases ho.pair with ⟨hzero, _⟩ | ⟨words, _, _, _, hcount, _, _, hsep⟩
  · exact False.elim (hp hzero)
  · rcases hsep with hz | ⟨_, hstack⟩
    · subst words
      have hcount0 : read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s = 0#64 := by
        apply BitVec.eq_of_toNat_eq
        simpa using hcount
      exact False.elim (hc hcount0)
    · simpa only [hcount, BitVec.ofNat_eq_ofNat] using hstack

structure Result (s t : ArmState) (outcome : Except Ssz.Err Ssz.Value) (data : Ssz.Bytes) : Prop where
  returned : Tail.Returned s t
  error : read_err t = .None
  observed : SszNative.ByteView.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat outcome
  aliases : outcome = .ok (.bytes data) →
    widthLoad t ((r (.GPR 0#5) s).toNat + 24) 8 = some (r (.GPR 2#5) s).toNat
  source : SszNative.ByteView.BytesAt (widthLoad t) (r (.GPR 2#5) s).toNat data
  descriptor : ∀ i < 24,
    t.mem (r (.GPR 1#5) s + BitVec.ofNat 64 i) =
      s.mem (r (.GPR 1#5) s + BitVec.ofNat 64 i)

theorem result_of_returned {s t : ArmState} {capacity : Nat} {data : Ssz.Bytes}
    {outcome : Except Ssz.Err Ssz.Value} (ho : Owned s capacity data)
    (hr : Tail.Returned s t) (he : read_err t = .None)
    (hob : SszNative.ByteView.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat outcome)
    (halias : outcome = .ok (.bytes data) →
      widthLoad t ((r (.GPR 0#5) s).toNat + 24) 8 = some (r (.GPR 2#5) s).toNat) :
    Result s t outcome data := by
  refine ⟨hr, he, hob, halias, Tail.frame_bytes s t data hr.frame ho.input, ?_⟩
  intro i hi
  have hh := ho.descriptorHigh
  have hout := ho.descriptorOutput
  have hstack := ho.descriptorStack
  apply hr.frame <;> bv_omega

/-- Both original descriptor words and every borrowed limb still denote exactly
the original arbitrary Nat after either return outcome. -/
theorem Result.descriptor_at {s t : ArmState} {capacity : Nat} {data : Ssz.Bytes}
    {outcome : Except Ssz.Err Ssz.Value} (h : Result s t outcome data)
    (ho : Owned s capacity data) :
    SszNative.NatMemory.At (widthLoad t) ((r (.GPR 1#5) s).toNat + 8) capacity := by
  have hword (offset : Nat) (hb : offset + 8 ≤ 24) :
      read_mem_bytes 8 (r (.GPR 1#5) s + BitVec.ofNat 64 offset) t =
        read_mem_bytes 8 (r (.GPR 1#5) s + BitVec.ofNat 64 offset) s := by
    apply BoolCodec.read_bytes_congr
    intro i hi
    change t.mem (r (.GPR 1#5) s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) =
      s.mem (r (.GPR 1#5) s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
      h.descriptor (offset + i) (by omega)
  apply Tail.nat_at s t _ _ capacity _ h.returned.frame ho.pair
  · simpa [widthLoad, BitVec.ofNat_add] using
      congrArg (fun v : BitVec 64 => some v.toNat) (hword 8 (by decide))
  · simpa [widthLoad, Nat.add_assoc, BitVec.ofNat_add, BitVec.add_assoc] using
      congrArg (fun v : BitVec 64 => some v.toNat) (hword 16 (by decide))

end SszArm.ByteView

namespace SszArm.UintCodec.WidthFrame

open ByteView

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem byteSeparated {s t : ArmState} (h : WidthFrame s t)
    (hs : ByteView.Tail.Separated s) : ByteView.Tail.Separated t := by
  have h0 := h.registers 0#5 (by decide)
  have h31 : r (.GPR 31#5) t = r (.GPR 31#5) s := h.sp
  rcases hs with ⟨hl, hh, ho, hw, ha⟩
  constructor
  · simpa only [h31] using hl
  · simpa only [h31] using hh
  · simpa only [h0] using ho
  · simpa only [h0, h31] using hw
  · simpa only [h0, h31] using ha

theorem byteFrame {s t : ArmState} (h : WidthFrame s t) : ByteView.Tail.Frame s t := by
  intro a _ hs
  exact h.memory a (by simpa only [BitVec.ofNat_eq_ofNat] using hs)

theorem bytePair {s t : ArmState} (h : WidthFrame s t)
    (pointer count : BitVec 64) (value : Nat) (hn : ByteView.Tail.NatPair s pointer count value) :
    ByteView.Tail.NatPair t pointer count value := by
  have h0 := h.registers 0#5 (by decide)
  have h31 : r (.GPR 31#5) t = r (.GPR 31#5) s := h.sp
  rcases hn with hsmall | ⟨words, hp, halign, hspace, hcount, hm, hv, hsep⟩
  · exact Or.inl hsmall
  · refine Or.inr ⟨words, hp, halign, hspace, hcount, ?_, hv, ?_⟩
    · rcases hsep with hempty | ⟨hout, hstack⟩
      · subst words
        intro i
        exact Fin.elim0 i
      · exact ByteView.Tail.frame_words s t pointer words h.byteFrame hspace hout hstack hm
    · simpa only [h0, h31] using hsep

theorem byteInput {s t : ArmState} (h : WidthFrame s t) {data : Ssz.Bytes}
    (hi : ByteView.Tail.Input s data) : ByteView.Tail.Input t data := by
  have h0 := h.registers 0#5 (by decide)
  have h2 := h.registers 2#5 (by decide)
  have h3 := h.registers 3#5 (by decide)
  have h31 : r (.GPR 31#5) t = r (.GPR 31#5) s := h.sp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [h3] using hi.size
  · simpa only [h2] using hi.high
  · simpa only [h2] using ByteView.Tail.frame_bytes s t data h.byteFrame hi
  · simpa only [h0, h2, h31] using hi.separated

theorem byteReturned {s t u : ArmState} (h : WidthFrame s t)
    (hs : ByteView.Tail.Separated s) (hr : ByteView.Tail.Returned t u) :
    ByteView.Tail.Returned s u := by
  have h0 := h.registers 0#5 (by decide)
  have h31 : r (.GPR 31#5) t = r (.GPR 31#5) s := h.sp
  have hact := ByteView.Tail.frame_activation s t hs h.byteFrame
  have hword (offset : Nat) (hb : offset + 8 ≤ 96) :
      read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 (272 + offset)) t =
      read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 (272 + offset)) s :=
    BoolCodec.activation_word s t offset hact hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.pc, h31]
    simpa only [Nat.reduceAdd] using hword 8 (by decide)
  · rw [hr.sp, h31]
  · intro reg offset hm
    rw [hr.registers reg offset hm, h31]
    have hb := BoolCodec.savedRegister_bounds reg offset hm
    have hw := hword (offset - 272) (by omega)
    simpa only [show 272 + (offset - 272) = offset by omega] using hw
  · intro i hi
    have hu := hr.activation i hi
    change read_mem (r (.GPR 31#5) t + BitVec.ofNat 64 (272 + i)) u =
      read_mem (r (.GPR 31#5) t + BitVec.ofNat 64 (272 + i)) t at hu
    rw [h31] at hu
    exact hu.trans (hact i hi)
  · intro a ho hw
    exact (hr.frame a (by simpa only [h0] using ho)
      (by simpa only [h31] using hw)).trans (h.byteFrame a ho hw)

end SszArm.UintCodec.WidthFrame
