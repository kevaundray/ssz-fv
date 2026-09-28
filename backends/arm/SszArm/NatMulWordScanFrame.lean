import SszArm.NatMulWordLoad
import SszArm.NatCompareOrder

namespace SszArm.NatMulWord

open UintCodec SszNative.Limbs

/-- The normalization scans only write their lowering spill; the input registers
may subsequently be replaced by the canonical borrowed representation. -/
structure ScanFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [1#5, 2#5, 8#5, 9#5, 10#5, 11#5, 12#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ a : BitVec 64,
    a.toNat < (r (.GPR 31#5) s).toNat - 16 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat →
    t.mem a = s.mem a

theorem ScanFrame.refl (s : ArmState) : ScanFrame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem ScanFrame.sp {s t : ArmState} (h : ScanFrame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := h.registers _ (by decide)

theorem ScanFrame.trans {s t u : ArmState} (h : ScanFrame s t) (k : ScanFrame t u) :
    ScanFrame s u := by
  refine ⟨k.program.trans h.program, k.error.trans h.error,
    fun reg hr => (k.registers reg hr).trans (h.registers reg hr),
    fun reg => (k.vectors reg).trans (h.vectors reg), ?_⟩
  intro a ha
  exact (k.memory a (by simpa only [h.sp] using ha)).trans (h.memory a ha)

theorem ScanFrame.code {s t : ArmState} (h : ScanFrame s t) {base : BitVec 64}
    (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, h.program] using hc

theorem ScanFrame.aligned {s t : ArmState} (h : ScanFrame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, h.sp] using ha

theorem ScanFrame.source {s t : ArmState} (h : ScanFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : NatCompare.Source s pointer words) : NatCompare.Source t pointer words := by
  simpa only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat, h.sp] using hs

theorem ScanFrame.words {s t : ArmState} (h : ScanFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    NatCompare.Words t pointer words := by
  intro i
  rw [← hm i]
  apply BoolCodec.read_bytes_congr
  intro j hj
  apply h.memory
  simp only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat] at hs
  rcases hs with ⟨hsp, hbound, hempty | hsep⟩
  · subst words; exact Fin.elim0 i
  · have hi := i.isLt
    have haddr : (pointer + BitVec.ofNat 64 (8 * i.val) + BitVec.ofNat 64 j).toNat =
        pointer.toNat + 8 * i.val + j := by bv_omega
    rw [haddr]
    omega

theorem scan_load_frame (site : LoadSite) (s : ArmState) (base word : BitVec 64)
    (hsite : site ≠ .input)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) : ScanFrame s (loaded site s base word) := by
  have h := NatCompare.saved_frame s site.scratch hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [loaded, state_simp_rules] using h.program
  · simpa [loaded, state_simp_rules] using h.error
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    cases site <;> simp_all [loaded, LoadSite.destination, NatCompare.saved, state_simp_rules]
  · intro reg; simpa [loaded, state_simp_rules] using h.vectors reg
  · intro a ha; simpa [loaded, state_simp_rules] using h.memory a ha

/-- Read-only instructions at dispatch, scan heads, and normalization exits. -/
def scanPureOps : List Op :=
  [.p0, .p4, .p8, .p100, .p104, .p108, .p112, .p148, .p152, .p156,
   .p160, .p164, .p168, .p172, .p176, .p228, .p232, .p236, .p240,
   .p244, .p248, .p252, .p256, .p292, .p296, .p300, .p304, .p308,
   .p312, .p316, .p920, .p924]

theorem scan_pure_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hops : ∀ op ∈ ops, op ∈ scanPureOps) : ScanFrame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact ScanFrame.refl s
  | cons op ops ih =>
    have hx := hops op List.mem_cons_self
    have hf : ScanFrame s (op.effect base s) := by
      simp only [scanPureOps, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx |
        hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx |
        hx | hx | hx | hx | hx | hx | hx | hx | hx
      all_goals subst op
      all_goals
        constructor
        · exact Op.program _ _ _
        · exact Op.error _ _ _
        · intro reg hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp (disch := simp_all) [Op.effect, put, next, Udivti3.compare,
            Udivti3.next, state_simp_rules]
        · intro reg; exact Op.sfp _ _ _ _
        · intro a ha; simp [Op.effect, put, next, Udivti3.compare,
            Udivti3.next, state_simp_rules]
    exact hf.trans (ih _ (fun op hop => hops op (List.mem_cons_of_mem _ hop)))

/-- All load premises are consequences of the original physical source span. -/
theorem scan_limb (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64))
    (n : Nat) (hn : n < words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    let address := pointer + (BitVec.ofNat 64 n <<< 3)
    address.toNat + 8 ≤ 2^64 ∧
      (address.toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
        (r (.GPR 31#5) s).toNat ≤ address.toNat) ∧
      read_mem_bytes 8 address s = words[n]?.getD 0#64 := by
  have hbound := hs.2.1
  have haddr : (pointer + (BitVec.ofNat 64 n <<< 3)).toNat = pointer.toNat + 8 * n := by
    bv_omega
  have heq : pointer + (BitVec.ofNat 64 n <<< 3) = pointer + BitVec.ofNat 64 (8 * n) := by
    bv_omega
  refine ⟨by rw [haddr]; omega, ?_, ?_⟩
  · rw [haddr]
    rcases hs.2.2 with empty | sep
    · simp [empty] at hn
    · have separate : pointer.toNat + 8 * words.length ≤ (r (.GPR 31#5) s).toNat - 16 ∨
          (r (.GPR 31#5) s).toNat ≤ pointer.toNat := by
        with_unfolding_all exact sep
      omega
  · dsimp
    rw [heq]
    simpa [List.getElem?_eq_getElem hn] using hm ⟨n, hn⟩

end SszArm.NatMulWord
