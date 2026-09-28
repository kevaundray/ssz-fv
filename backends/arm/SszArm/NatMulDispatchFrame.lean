import SszArm.NatMulDispatchLeft
import SszArm.NatCompareOrder

namespace SszArm.NatMul

open SszNative.Limbs

/-- Dispatch additionally prepares X1..X4 for the real tail helper. All other
scalars, vector registers, and bytes outside the lowering slot are framed. -/
structure DispatchFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [1#5, 2#5, 3#5, 4#5, 8#5, 9#5, 10#5, 11#5, 21#5, 22#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ a : BitVec 64,
    a.toNat < (r (.GPR 31#5) s).toNat - 16 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat →
    t.mem a = s.mem a

theorem DispatchFrame.refl (s : ArmState) : DispatchFrame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem DispatchFrame.sp {s t : ArmState} (h : DispatchFrame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := h.registers _ (by decide)

theorem DispatchFrame.trans {s t u : ArmState} (h : DispatchFrame s t)
    (k : DispatchFrame t u) : DispatchFrame s u := by
  refine ⟨k.program.trans h.program, k.error.trans h.error,
    fun reg hr => (k.registers reg hr).trans (h.registers reg hr),
    fun reg => (k.vectors reg).trans (h.vectors reg), ?_⟩
  intro a ha
  exact (k.memory a (by simpa only [h.sp] using ha)).trans (h.memory a ha)

theorem ScanFrame.dispatch {s t : ArmState} (h : ScanFrame s t) : DispatchFrame s t := by
  refine ⟨h.program, h.error, ?_, h.vectors, h.memory⟩
  intro reg hr
  apply h.registers reg
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
  exact hr.2.2.2.2

theorem DispatchFrame.code {s t : ArmState} (h : DispatchFrame s t) {base : BitVec 64}
    (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, h.program] using hc

theorem DispatchFrame.aligned {s t : ArmState} (h : DispatchFrame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, h.sp] using ha

theorem DispatchFrame.source {s t : ArmState} (h : DispatchFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : NatCompare.Source s pointer words) : NatCompare.Source t pointer words := by
  simpa only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat, h.sp] using hs

theorem DispatchFrame.words {s t : ArmState} (h : DispatchFrame s t)
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

theorem DispatchFrame.operand {s t : ArmState} (h : DispatchFrame s t)
    (pointer payload : BitVec 64) (words : List (BitVec 64))
    (ho : NatCompare.Operand s pointer payload words) : NatCompare.Operand t pointer payload words := by
  rcases ho with hsmall | ⟨hn, hc, hs, hm⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨hn, hc, h.source _ _ hs, h.words _ _ hs hm⟩

def dispatchPureOps : List Op :=
  [.p212, .p216, .p220, .p224, .p228, .p376, .p380, .p384, .p388, .p392,
   .p396, .p400, .p404, .p408]

theorem dispatch_pure_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (allowed : ∀ op ∈ ops, op ∈ dispatchPureOps) : DispatchFrame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact DispatchFrame.refl s
  | cons op ops ih =>
    have hx := allowed op List.mem_cons_self
    have frame : DispatchFrame s (op.effect base s) := by
      simp only [dispatchPureOps, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h
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

def RawArgs (s t : ArmState) : Prop :=
  r (.GPR 1#5) t = r (.GPR 1#5) s ∧ r (.GPR 2#5) t = r (.GPR 2#5) s ∧
  r (.GPR 3#5) t = r (.GPR 3#5) s ∧ r (.GPR 4#5) t = r (.GPR 4#5) s

theorem ScanFrame.raw {s t : ArmState} (h : ScanFrame s t) : RawArgs s t :=
  ⟨h.registers _ (by decide), h.registers _ (by decide),
    h.registers _ (by decide), h.registers _ (by decide)⟩

/-- Branch precedence is explicit: zero, then right-one, then left-one,
then the original allocation body. The right-one exit is before MOV X3,X4.
At allocation, X9 retains the right scan's final significant index, used
by the native row-end and next-row address setup. -/
def DispatchExit (s t : ArmState) (base : BitVec 64)
    (left right : List (BitVec 64)) : Prop :=
  if sigWords left = 0 ∨ sigWords right = 0 then
    read_pc t = base + 264#64 ∧ RawArgs s t
  else if sigWords right = 1 then
    read_pc t = base + 228#64 ∧
    r (.GPR 1#5) t = r (.GPR 1#5) s ∧ r (.GPR 2#5) t = r (.GPR 2#5) s ∧
    r (.GPR 3#5) t = r (.GPR 3#5) s ∧ r (.GPR 4#5) t = right[0]?.getD 0#64
  else if sigWords left = 1 then
    read_pc t = base + 232#64 ∧
    r (.GPR 1#5) t = r (.GPR 3#5) s ∧ r (.GPR 2#5) t = r (.GPR 4#5) s ∧
    r (.GPR 3#5) t = left[0]?.getD 0#64
  else
    read_pc t = base + 412#64 ∧ RawArgs s t ∧
    r (.GPR 21#5) t = BitVec.ofNat 64 (sigWords left) ∧
    r (.GPR 22#5) t = BitVec.ofNat 64 (sigWords right) ∧
    r (.GPR 8#5) t = r (.GPR 2#5) s ∧
    r (.GPR 9#5) t = BitVec.ofNat 64 (sigWords right - 1)

theorem DispatchExit.prepend {s u t : ArmState} {base : BitVec 64}
    {left right : List (BitVec 64)} (frame : ScanFrame s u)
    (exit : DispatchExit u t base left right) : DispatchExit s t base left right := by
  rcases frame.raw with ⟨h1, h2, h3, h4⟩
  simpa only [DispatchExit, RawArgs, h1, h2, h3, h4] using exit

end SszArm.NatMul
