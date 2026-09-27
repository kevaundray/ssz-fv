import SszArm.NatDivisionCopyFacts

namespace SszArm.NatDivision

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The complete forward copy counts up to the retained significant count.
The original physical count is used solely to justify each real source read;
therefore redundant high zeros remain protected but are not copied. -/
theorem copy_loop (base pointer destination : BitVec 64) (words : List (BitVec 64))
    (count : Nat) (hn : count ≤ words.length)
    (hsep : pointer.toNat + 8 * words.length ≤ destination.toNat ∨
      destination.toNat + 8 * count ≤ pointer.toNat) :
    ∀ remaining i (s : ArmState), i + remaining = count →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = (if i = count then base + 520#64 else base + 452#64) →
      r (.GPR 1#5) s = pointer →
      r (.GPR 2#5) s = BitVec.ofNat 64 words.length →
      r (.GPR 8#5) s = BitVec.ofNat 64 count →
      r (.GPR 9#5) s = BitVec.ofNat 64 i →
      r (.GPR 24#5) s = destination →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      CopyDestination s destination count → Copied s destination words i →
      ∃ fuel t, run fuel s = t ∧ CopyFrame destination count s t ∧
        read_pc t = base + 520#64 ∧ r (.GPR 1#5) t = pointer ∧
        r (.GPR 9#5) t = BitVec.ofNat 64 count ∧ Copied t destination words count := by
  intro remaining
  induction remaining with
  | zero =>
    intro i s hcount hc he ha hp h1 h2 h8 h9 h24 hs hm hd copied
    have hi : i = count := by omega
    subst i
    exact ⟨0, s, rfl, CopyFrame.refl destination count s,
      by simpa using hp, h1, h9, copied⟩
  | succ remaining ih =>
    intro i s hcount hc he ha hp h1 h2 h8 h9 h24 hs hm hd copied
    have hi : i < count := by omega
    have hpc : read_pc s = base + 452#64 := by
      simpa [show i ≠ count by omega] using hp
    have hbound : count < 2^64 := by have := hs.2.1; omega
    let u := copyRoundResult s base (words[i]?.getD 0#64)
    have hu : run 22 s = u := copy_round_run s base pointer destination words count i
      hc he ha hpc h1 h2 h9 h24 hi hn hs hm hd
    have huf : CopyFrame destination count s u := copy_round_frame s base destination _ i count
      h9 h24 hi hs.1 hd
    obtain ⟨hu9, hu1, hup⟩ := copy_round_registers s base (words[i]?.getD 0#64) i count h9 h8 hi hbound
    change r (.GPR 9#5) u = BitVec.ofNat 64 (i + 1) at hu9
    change r (.GPR 1#5) u = r (.GPR 1#5) s at hu1
    change read_pc u = (if i + 1 = count then base + 520#64 else base + 452#64) at hup
    have hucopied : Copied u destination words (i + 1) :=
      copy_round_copied s base destination words i count h9 h24 hi hs.1 hd copied
    obtain ⟨fuel, t, ht, htf, htp, ht1, ht9, hcopied⟩ := ih (i + 1) u (by omega)
      (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup (hu1.trans h1)
      ((huf.registers 2#5 (by decide)).trans h2)
      ((huf.registers 8#5 (by decide)).trans h8) hu9
      ((huf.registers 24#5 (by decide)).trans h24)
      (huf.source _ _ hs) (huf.words hs hm hsep) (huf.destination hd) hucopied
    refine ⟨22 + fuel, t, ?_, huf.trans htf, htp, ht1, ht9, hcopied⟩
    rw [run_plus, hu, ht]

/-- Full scratch initialization starting at the allocator's pc452 branch.
All original bytes (not merely the significant prefix) survive. The endpoint
pc520 is before the reverse division loop's X1 := 0 initialization. -/
theorem copy_full (s : ArmState) (base pointer destination : BitVec 64)
    (words : List (BitVec 64)) (count : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 452#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 count)
    (h9 : r (.GPR 9#5) s = 0#64)
    (h24 : r (.GPR 24#5) s = destination)
    (hpositive : 0 < count) (hn : count ≤ words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words)
    (hd : CopyDestination s destination count)
    (hsep : pointer.toNat + 8 * words.length ≤ destination.toNat ∨
      destination.toNat + 8 * count ≤ pointer.toNat) :
    ∃ fuel t, run fuel s = t ∧ CopyFrame destination count s t ∧
      read_pc t = base + 520#64 ∧ r (.GPR 1#5) t = pointer ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 count ∧
      NatCompare.Words t destination (words.take count) ∧
      NatCompare.Words t pointer words ∧
      (∀ a : BitVec 64, pointer.toNat ≤ a.toNat →
        a.toNat < pointer.toNat + 8 * words.length → t.mem a = s.mem a) := by
  obtain ⟨fuel, t, ht, htf, htp, ht1, ht9, copied⟩ :=
    copy_loop base pointer destination words count hn hsep count 0 s (by omega)
      hc he ha (by simpa [show 0 ≠ count by omega] using hp) h1 h2 h8 h9 h24 hs hm hd
      (by intro i hi; omega)
  exact ⟨fuel, t, ht, htf, htp, ht1, ht9, copied.words hn,
    htf.words hs hm hsep, fun a lo hi => htf.input_byte hs hsep a lo hi⟩

/-- The native significant-count copy writes exactly Limbs.trim, without
requiring the original physical operand to be canonical. -/
theorem copy_significant (s : ArmState) (base pointer destination : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 452#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 (sigWords words))
    (h9 : r (.GPR 9#5) s = 0#64)
    (h24 : r (.GPR 24#5) s = destination)
    (hpositive : 0 < sigWords words)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words)
    (hd : CopyDestination s destination (sigWords words))
    (hsep : pointer.toNat + 8 * words.length ≤ destination.toNat ∨
      destination.toNat + 8 * sigWords words ≤ pointer.toNat) :
    ∃ fuel t, run fuel s = t ∧ CopyFrame destination (sigWords words) s t ∧
      read_pc t = base + 520#64 ∧ r (.GPR 1#5) t = pointer ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 (sigWords words) ∧
      NatCompare.Words t destination (trim words) ∧ NatCompare.Words t pointer words ∧
      (∀ a : BitVec 64, pointer.toNat ≤ a.toNat →
        a.toNat < pointer.toNat + 8 * words.length → t.mem a = s.mem a) := by
  simpa only [trim_eq_take] using copy_full s base pointer destination words (sigWords words)
    hc he ha hp h1 h2 h8 h9 h24 hpositive (sigWords_le_length words) hs hm hd hsep

end SszArm.NatDivision
