import SszArm.NatMulExec
import SszArm.NatCompareBlocks
import SszNatOperandNormalization

namespace SszArm.NatMul

open UintCodec SszNative.Limbs

/-- Main count scans only write their six work registers and the current
16-byte lowering slot. In particular all six raw ABI arguments survive. -/
structure ScanFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5, 11#5, 21#5, 22#5] →
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

theorem ScanFrame.operand {s t : ArmState} (h : ScanFrame s t)
    (pointer payload : BitVec 64) (words : List (BitVec 64))
    (ho : NatCompare.Operand s pointer payload words) : NatCompare.Operand t pointer payload words := by
  rcases ho with hsmall | ⟨hn, hc, hs, hm⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨hn, hc, h.source _ _ hs, h.words _ _ hs hm⟩

def scanPureOps : List Op :=
  [.p28, .p32, .p36, .p40, .p44, .p80, .p84, .p88, .p92, .p96, .p100,
   .p104, .p108, .p112, .p116, .p120, .p124, .p128, .p132, .p136, .p140,
   .p144, .p148, .p152, .p156, .p160, .p164, .p168, .p172, .p204, .p208,
   .p212, .p216, .p220, .p376, .p380, .p384, .p388, .p392]

theorem scan_pure_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (allowed : ∀ op ∈ ops, op ∈ scanPureOps) : ScanFrame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact ScanFrame.refl s
  | cons op ops ih =>
    have hx := allowed op List.mem_cons_self
    have frame : ScanFrame s (op.effect base s) := by
      simp only [scanPureOps, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h
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
        · intro a ha
          simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
    exact frame.trans (ih _ (fun op hop => allowed op (List.mem_cons_of_mem _ hop)))

end SszArm.NatMul
