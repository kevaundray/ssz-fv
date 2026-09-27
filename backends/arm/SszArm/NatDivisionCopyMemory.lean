import SszArm.NatDivisionCopyStore

namespace SszArm.NatDivision

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The forward copy can write its full reserved significant prefix and the
lowering slot, but never any byte of the original physical operand. -/
structure CopyFrame (destination : BitVec 64) (count : Nat) (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [1#5, 9#5, 10#5, 11#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ a : BitVec 64,
    (a.toNat < (r (.GPR 31#5) s).toNat - 16 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) →
    (a.toNat < destination.toNat ∨ destination.toNat + 8 * count ≤ a.toNat) →
    t.mem a = s.mem a

theorem CopyFrame.refl (destination : BitVec 64) (count : Nat) (s : ArmState) :
    CopyFrame destination count s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

theorem CopyFrame.sp {destination : BitVec 64} {count : Nat} {s t : ArmState}
    (hf : CopyFrame destination count s t) : r (.GPR 31#5) t = r (.GPR 31#5) s :=
  hf.registers _ (by decide)

theorem CopyFrame.trans {destination : BitVec 64} {count : Nat} {s t u : ArmState}
    (st : CopyFrame destination count s t) (tu : CopyFrame destination count t u) :
    CopyFrame destination count s u := by
  refine ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg hr => (tu.registers reg hr).trans (st.registers reg hr),
    fun reg => (tu.vectors reg).trans (st.vectors reg), ?_⟩
  intro a hs hd
  exact (tu.memory a (by simpa only [st.sp] using hs) hd).trans (st.memory a hs hd)

theorem CopyFrame.code {destination : BitVec 64} {count : Nat} {s t : ArmState}
    (hf : CopyFrame destination count s t) {base : BitVec 64}
    (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, hf.program] using hc

theorem CopyFrame.aligned {destination : BitVec 64} {count : Nat} {s t : ArmState}
    (hf : CopyFrame destination count s t) (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, hf.sp] using ha

theorem CopyFrame.source {destination : BitVec 64} {count : Nat} {s t : ArmState}
    (hf : CopyFrame destination count s t) (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : NatCompare.Source s pointer words) : NatCompare.Source t pointer words := by
  simpa only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat, hf.sp] using hs

/-- Byte preservation covers the entire physical source, including high zeros
that are not copied into the significant scratch prefix. -/
theorem CopyFrame.input_byte {destination pointer : BitVec 64} {count : Nat}
    {s t : ArmState} {words : List (BitVec 64)}
    (hf : CopyFrame destination count s t) (hs : NatCompare.Source s pointer words)
    (hsep : pointer.toNat + 8 * words.length ≤ destination.toNat ∨
      destination.toNat + 8 * count ≤ pointer.toNat)
    (a : BitVec 64) (lo : pointer.toNat ≤ a.toNat)
    (hi : a.toNat < pointer.toNat + 8 * words.length) : t.mem a = s.mem a := by
  simp only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat] at hs
  apply hf.memory
  · rcases hs.2.2 with hempty | hstack
    · subst words
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hi
      exact False.elim (Nat.not_lt_of_ge lo hi)
    · omega
  · omega

theorem CopyFrame.words {destination pointer : BitVec 64} {count : Nat}
    {s t : ArmState} {words : List (BitVec 64)}
    (hf : CopyFrame destination count s t) (hs : NatCompare.Source s pointer words)
    (hm : NatCompare.Words s pointer words)
    (hsep : pointer.toNat + 8 * words.length ≤ destination.toNat ∨
      destination.toNat + 8 * count ≤ pointer.toNat) : NatCompare.Words t pointer words := by
  intro i
  rw [← hm i]
  apply BoolCodec.read_bytes_congr
  intro j hj
  have hb := hs.2.1
  have hi := i.isLt
  apply hf.input_byte hs hsep
  · bv_omega
  · bv_omega

/-- Observations for the exact already-copied prefix. -/
def Copied (s : ArmState) (destination : BitVec 64) (words : List (BitVec 64)) (count : Nat) : Prop :=
  ∀ i, i < count → read_mem_bytes 8 (destination + BitVec.ofNat 64 (8 * i)) s = words[i]?.getD 0#64

theorem Copied.words {s : ArmState} {destination : BitVec 64} {words : List (BitVec 64)}
    {count : Nat} (hc : Copied s destination words count) (hn : count ≤ words.length) :
    NatCompare.Words s destination (words.take count) := by
  intro i
  have hi : i.val < count := by have := i.isLt; simp only [List.length_take] at this; omega
  have hil : i.val < words.length := by omega
  have h := hc i.val hi
  simpa [List.getElem?_eq_getElem hil, List.getElem_take] using h

/-- Destination ownership includes the complete reserved prefix and excludes
the lowering slot. It places no restriction on arena capacity. -/
def CopyDestination (s : ArmState) (destination : BitVec 64) (count : Nat) : Prop :=
  destination.toNat + 8 * count ≤ 2^64 ∧
  (destination.toNat + 8 * count ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat ≤ destination.toNat)

theorem CopyFrame.destination {destination : BitVec 64} {count : Nat} {s t : ArmState}
    (hf : CopyFrame destination count s t) (hd : CopyDestination s destination count) :
    CopyDestination t destination count := by
  simpa only [CopyDestination, hf.sp] using hd

end SszArm.NatDivision
