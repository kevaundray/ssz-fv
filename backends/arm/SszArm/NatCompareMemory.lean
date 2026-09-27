import SszArm.NatCompareExec

namespace SszArm.NatCompare

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Only the result and five caller-saved work registers may change. -/
structure Frame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [0#5, 8#5, 9#5, 10#5, 11#5, 12#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ a : BitVec 64,
    a.toNat < (r (.GPR 31#5) s).toNat - 16 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat →
    t.mem a = s.mem a

theorem Frame.refl (s : ArmState) : Frame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem Frame.sp {s t : ArmState} (h : Frame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := h.registers _ (by decide)

theorem Frame.trans {s t u : ArmState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  refine ⟨k.program.trans h.program, k.error.trans h.error,
    fun reg hr => (k.registers reg hr).trans (h.registers reg hr),
    fun reg => (k.vectors reg).trans (h.vectors reg), ?_⟩
  intro a ha
  exact (k.memory a (by simpa only [h.sp] using ha)).trans (h.memory a ha)

theorem Frame.aligned {s t : ArmState} (h : Frame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  have hp := h.sp
  simpa only [CheckSPAlignment, state_simp_rules, hp] using ha

theorem Frame.code {s t : ArmState} (h : Frame s t) {base : BitVec 64}
    (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, h.program] using hc

def saved (s : ArmState) (reg : BitVec 5) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR reg) s) s

theorem saved_frame (s : ArmState) (reg : BitVec 5)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) : Frame s (saved s reg) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [saved, state_simp_rules]
  · simp [saved, state_simp_rules]
  · intro i hi; simp [saved, state_simp_rules]
  · intro i; simp [saved, state_simp_rules]
  · intro a ha
    exact BoolCodec.write_mem_bytes_frame s _ 8 _ a (by bv_omega) (by bv_omega)

theorem spill_mem_w (s : ArmState) (f : StateField) (v : state_value f)
    (n : Nat) (addr : BitVec 64) (value : BitVec (n * 8)) :
    (write_mem_bytes n addr value (w f v s)).mem =
      (write_mem_bytes n addr value s).mem :=
  mem_write_mem_bytes_of_mem_eq (ArmState.mem_w_eq_mem f v s) n addr value

theorem read_spill_w (s : ArmState) (f : StateField) (v : state_value f)
    (n m : Nat) (addr dst : BitVec 64) (value : BitVec (m * 8)) :
    read_mem_bytes n addr (write_mem_bytes m dst value (w f v s)) =
      read_mem_bytes n addr (write_mem_bytes m dst value s) :=
  (Memory.mem_eq_iff_read_mem_bytes_eq.mp (spill_mem_w s f v m dst value)) n addr

abbrev Source := ByteView.Source
abbrev Words := WidthWords

theorem Frame.source {s t : ArmState} (h : Frame s t)
    (pointer : BitVec 64) (words : List (BitVec 64)) (hs : Source s pointer words) :
    Source t pointer words := by
  simpa only [Source, ByteView.Source, BitVec.ofNat_eq_ofNat, h.sp] using hs

theorem Frame.words {s t : ArmState} (h : Frame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : Source s pointer words) (hm : Words s pointer words) : Words t pointer words := by
  intro i
  rw [← hm i]
  apply BoolCodec.read_bytes_congr
  intro j hj
  change t.mem _ = s.mem _
  apply h.memory
  simp only [Source, ByteView.Source, BitVec.ofNat_eq_ofNat] at hs
  rcases hs with ⟨hsp, hbound, hempty | hsep⟩
  · subst words; exact Fin.elim0 i
  · have hi := i.isLt
    have haddr : (pointer + BitVec.ofNat 64 (8 * i.val) + BitVec.ofNat 64 j).toNat =
        pointer.toNat + 8 * i.val + j := by bv_omega
    rw [haddr]
    omega

/-- Static lowering-slot ownership. Empty borrowed spans impose no separation. -/
def Owned (s : ArmState) (pointer payload : BitVec 64) : Prop :=
  16 ≤ (r (.GPR 31#5) s).toNat ∧
  (pointer ≠ 0#64 → payload ≠ 0#64 →
    pointer.toNat + 8 * payload.toNat ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ pointer.toNat)

/-- Logical limbs used by the native zero-extended word operation. -/
def Operand (s : ArmState) (pointer payload : BitVec 64) (words : List (BitVec 64)) : Prop :=
  (pointer = 0#64 ∧ words = [payload]) ∨
  (pointer ≠ 0#64 ∧ payload.toNat = words.length ∧ Source s pointer words ∧ Words s pointer words)

theorem Operand.of_pair (s : ArmState) (pointer payload : BitVec 64) (value : Nat)
    (hp : SszNative.NatMemory.Pair (widthLoad s) pointer payload value)
    (hs : Owned s pointer payload) :
    ∃ words, Operand s pointer payload words ∧ SszNative.Limbs.value words = value := by
  rcases hp with ⟨hz, hv⟩ | ⟨words, hpos, halign, hbound, hcount, hm, hv⟩
  · exact ⟨[payload], Or.inl ⟨hz, rfl⟩, by simpa [SszNative.Limbs.value] using hv⟩
  · have hn : pointer ≠ 0#64 := by intro h; simp [h] at hpos
    refine ⟨words, Or.inr ⟨hn, hcount, ⟨hs.1, hbound, ?_⟩, ?_⟩, hv⟩
    · by_cases he : words = []
      · exact Or.inl he
      · right
        have hc : payload ≠ 0#64 := by
          intro h
          cases words <;> simp_all
        simpa only [hcount, BitVec.ofNat_eq_ofNat] using hs.2 hn hc
    · intro i
      apply BitVec.eq_of_toNat_eq
      have hi := Option.some.inj (hm i)
      simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using hi

theorem Frame.operand {s t : ArmState} (h : Frame s t)
    (pointer payload : BitVec 64) (words : List (BitVec 64)) (ho : Operand s pointer payload words) :
    Operand t pointer payload words := by
  rcases ho with hsmall | ⟨hn, hc, hs, hm⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨hn, hc, h.source _ _ hs, h.words _ _ hs hm⟩

theorem Operand.length_bound {s : ArmState} {pointer payload : BitVec 64}
    {words : List (BitVec 64)} (h : Operand s pointer payload words) : words.length < 2^64 := by
  rcases h with ⟨_, rfl⟩ | ⟨_, hc, _, _⟩
  · simp
  · rw [← hc]; exact payload.isLt

theorem Operand.small {s : ArmState} {pointer payload : BitVec 64}
    {words : List (BitVec 64)} (h : Operand s pointer payload words) (hz : pointer = 0#64) :
    words = [payload] := by
  rcases h with ⟨_, hw⟩ | ⟨hn, _⟩
  · exact hw
  · exact False.elim (hn hz)

theorem Operand.large {s : ArmState} {pointer payload : BitVec 64}
    {words : List (BitVec 64)} (h : Operand s pointer payload words) (hz : pointer ≠ 0#64) :
    payload.toNat = words.length ∧ Source s pointer words ∧ Words s pointer words := by
  rcases h with ⟨hn, _⟩ | ⟨_, hl⟩
  · exact False.elim (hz hn)
  · exact hl

end SszArm.NatCompare
