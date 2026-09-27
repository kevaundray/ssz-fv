import SszArm.UintPrefix
import SszArm.UintTails

namespace SszArm.UintCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem Small.Stable.tail_separated {s t : ArmState} (h : Small.Stable s t)
    (hs : Tail.Separated s) : Tail.Separated t := by
  have h0 := h.regs 0#5 (by decide)
  have h31 := h.regs 31#5 (by decide)
  rcases hs with ⟨hl, hh, ho, hw, ha⟩
  constructor
  · simpa only [h31] using hl
  · simpa only [h31] using hh
  · simpa only [h0] using ho
  · simpa only [h0, h31] using hw
  · simpa only [h0, h31] using ha

theorem Small.Stable.tail_frame {s t : ArmState} (h : Small.Stable s t) : Tail.Frame s t := by
  intro a _ hs
  apply h.frame a
  change a.toNat < (r (.GPR 31#5) s).toNat - 16 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat
  omega

theorem Small.Stable.nat_pair {s t : ArmState} (h : Small.Stable s t)
    (pointer count : BitVec 64) (value : Nat) (hn : Tail.NatPair s pointer count value) :
    Tail.NatPair t pointer count value := by
  have h0 := h.regs 0#5 (by decide)
  have h31 := h.regs 31#5 (by decide)
  rcases hn with hsmall | ⟨words, hp, halign, hspace, hcount, hm, hv, hsep⟩
  · exact Or.inl hsmall
  · refine Or.inr ⟨words, hp, halign, hspace, hcount, ?_, hv, ?_⟩
    · rcases hsep with hempty | ⟨hout, hstack⟩
      · subst words
        intro i
        exact Fin.elim0 i
      · exact Tail.frame_words s t pointer words h.tail_frame hspace hout hstack hm
    · simpa only [h0, h31] using hsep

theorem Small.Stable.returned {s t u : ArmState} (h : Small.Stable s t)
    (hs : Tail.Separated s) (hr : Tail.Returned t u) : Tail.Returned s u := by
  have h0 := h.regs 0#5 (by decide)
  have h31 := h.regs 31#5 (by decide)
  have hact := Tail.frame_activation s t hs h.tail_frame
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
      (by simpa only [h31] using hw)).trans (h.tail_frame a ho hw)

/-- The physical width pair read by the actual header LDP, including borrowed
Large slices whose lifetime extends through a possible scope-error result. -/
def WidthPair (s : ArmState) (width : Nat) : Prop :=
  Tail.NatPair s (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s)
    (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s) width

theorem width_at_of_pair (s : ArmState) (width : Nat) (h : WidthPair s width) :
    SszNative.NatMemory.At (widthLoad s) ((r (.GPR 1#5) s).toNat + 8) width := by
  apply Tail.nat_at s s _ _ width _ (fun _ _ _ => rfl) h
  · simp [widthLoad, BitVec.ofNat_add]
  · simp [widthLoad, BitVec.ofNat_add, Nat.add_assoc]

end SszArm.UintCodec
