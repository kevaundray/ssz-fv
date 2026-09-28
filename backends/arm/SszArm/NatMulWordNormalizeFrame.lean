import SszArm.NatMulWordScanFrame
import SszArm.NatMulWordReturnValues
import SszArm.NatAddZeroOwned

namespace SszArm.NatMulWord

open UintCodec SszNative.Limbs
open Delimited (MemoryFrame Returned)

/-- Rows1464..1492 only read memory; only X8, X9, and X12 are scratch. -/
structure NormalizeFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 12#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : t.mem = s.mem

theorem NormalizeFrame.refl (s : ArmState) : NormalizeFrame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩

theorem NormalizeFrame.trans {s t u : ArmState} (h : NormalizeFrame s t)
    (k : NormalizeFrame t u) : NormalizeFrame s u :=
  ⟨k.program.trans h.program, k.error.trans h.error,
    fun reg hr => (k.registers reg hr).trans (h.registers reg hr),
    fun reg => (k.vectors reg).trans (h.vectors reg), k.memory.trans h.memory⟩

theorem NormalizeFrame.sp {s t : ArmState} (h : NormalizeFrame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := h.registers _ (by decide)

theorem NormalizeFrame.out {s t : ArmState} (h : NormalizeFrame s t) :
    r (.GPR 0#5) t = r (.GPR 0#5) s := h.registers _ (by decide)

theorem NormalizeFrame.code {s t : ArmState} (h : NormalizeFrame s t) {base : BitVec 64}
    (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, h.program] using hc

theorem NormalizeFrame.aligned {s t : ArmState} (h : NormalizeFrame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, h.sp] using ha

theorem NormalizeFrame.source {s t : ArmState} (h : NormalizeFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : NatCompare.Source s pointer words) : NatCompare.Source t pointer words := by
  simpa only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat, h.sp] using hs

theorem NormalizeFrame.words {s t : ArmState} (h : NormalizeFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hm : NatCompare.Words s pointer words) : NatCompare.Words t pointer words := by
  intro i
  rw [← hm i]
  apply BoolCodec.read_bytes_congr
  intro j hj
  exact congrFun h.memory _

theorem NormalizeFrame.loads {s t : ArmState} (h : NormalizeFrame s t) :
    widthLoad t = widthLoad s := by
  funext address bytes
  unfold widthLoad
  congr 1
  congr 1
  apply BoolCodec.read_bytes_congr
  intro j hj
  exact congrFun h.memory _

theorem NormalizeFrame.owned {s t : ArmState} (h : NormalizeFrame s t)
    (owned : ReturnOwned s) : ReturnOwned t := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [h.sp] using owned.stack
  · simpa only [h.out] using owned.output
  · simpa only [h.sp, h.out] using owned.separate

theorem NormalizeFrame.writes {s t : ArmState} (h : NormalizeFrame s t) :
    valueWrites t = valueWrites s := by
  simp only [valueWrites, NatAdd.valueWrites, h.out, h.sp]

theorem NormalizeFrame.returned {s t u : ArmState} (h : NormalizeFrame s t)
    (returned : Returned t u) : Returned s u := by
  refine ⟨returned.pc.trans (h.registers _ (by decide)), returned.error,
    returned.sp.trans h.sp, ?_, ?_⟩
  · intro reg low high
    apply (returned.registers reg low high).trans
    apply h.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · intro eq; subst reg; simp at low
    constructor
    · intro eq; subst reg; simp at low
    · intro eq; subst reg; simp at low
  · intro reg low high
    exact (returned.vectors reg low high).trans
      (congrArg (fun x : BitVec 128 => x.setWidth 64) (h.vectors reg))

def normalizeReadOps : List Op :=
  [.p1464, .p1468, .p1472, .p1476, .p1480, .p1484, .p1488, .p1492]

theorem normalize_read_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (allowed : ∀ op ∈ ops, op ∈ normalizeReadOps) : NormalizeFrame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact NormalizeFrame.refl s
  | cons op ops ih =>
    have hx := allowed op List.mem_cons_self
    have frame : NormalizeFrame s (op.effect base s) := by
      simp only [normalizeReadOps, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h | h | h | h
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
        · funext a
          simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
    exact frame.trans (ih _ (fun op hop => allowed op (List.mem_cons_of_mem _ hop)))

end SszArm.NatMulWord
