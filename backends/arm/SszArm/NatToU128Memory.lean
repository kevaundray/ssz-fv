import SszArm.NatToU128Contract
import SszArm.NatCompareBlocks

namespace SszArm.NatNarrow

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The descending significant-width scans change only their five work
registers and the sixteen-byte lowering slot. The ABI inputs stay intact. -/
structure Frame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5, 11#5, 12#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ a : BitVec 64,
    a.toNat < (r (.GPR 31#5) s).toNat - 16 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat →
    t.mem a = s.mem a

theorem Frame.refl (s : ArmState) : Frame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem Frame.sp {s t : ArmState} (hf : Frame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := hf.registers _ (by decide)

theorem Frame.trans {s t u : ArmState} (st : Frame s t) (tu : Frame t u) :
    Frame s u := by
  refine ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg hr => (tu.registers reg hr).trans (st.registers reg hr),
    fun reg => (tu.vectors reg).trans (st.vectors reg), ?_⟩
  intro a ha
  exact (tu.memory a (by simpa only [st.sp] using ha)).trans (st.memory a ha)

theorem Frame.aligned {s t : ArmState} (hf : Frame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, hf.sp] using ha

theorem Frame.compare {s t : ArmState} (hf : Frame s t) : NatCompare.Frame s t := by
  refine ⟨hf.program, hf.error, ?_, hf.vectors, hf.memory⟩
  intro reg hr
  exact hf.registers reg (fun member => hr (List.mem_cons_of_mem _ member))

theorem Frame.source {s t : ArmState} (hf : Frame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : NatCompare.Source s pointer words) : NatCompare.Source t pointer words :=
  hf.compare.source pointer words hs

theorem Frame.words {s t : ArmState} (hf : Frame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    NatCompare.Words t pointer words := hf.compare.words pointer words hs hm

theorem Frame.memoryFrame {s t : ArmState} (hf : Frame s t)
    (writes : List Delimited.Span)
    (slot : ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writes)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat) :
    Delimited.MemoryFrame writes s t := by
  intro a outside
  have separate := outside _ slot
  apply hf.memory
  rcases separate with low | high
  · exact Or.inl low
  · right; omega

theorem saved_frame (s : ArmState) (reg : BitVec 5)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat) : Frame s (NatCompare.saved s reg) := by
  have hf := NatCompare.saved_frame s reg safe
  refine ⟨hf.program, hf.error, ?_, hf.vectors, hf.memory⟩
  intro index outside
  simp [NatCompare.saved, state_simp_rules]

end SszArm.NatNarrow

namespace SszArm.NatToU128

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem frame_code {s t : ArmState} (hf : NatNarrow.Frame s t) {base : BitVec 64}
    (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, hf.program] using hc

def scanPureOps : List Op := [.p0, .p4, .p8, .p12, .p48, .p52, .p56, .p60, .p64, .p68,
  .p120, .p124, .p128, .p132, .p136, .p148, .p240, .p336]

theorem scan_pure_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hops : ∀ op ∈ ops, op ∈ scanPureOps) : NatNarrow.Frame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact NatNarrow.Frame.refl s
  | cons op ops ih =>
    have member := hops op List.mem_cons_self
    have hf : NatNarrow.Frame s (op.effect base s) := by
      cases op <;> simp_all only [scanPureOps, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, false_or, or_self]
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

end SszArm.NatToU128

namespace SszArm.NatNarrow

open UintCodec

theorem large_source (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64))
    (writes : List Delimited.Span)
    (input : (SszNative.NatOperand.large pointer words).At (widthLoad s))
    (owned : NatDivision.OperandOwned writes (.large pointer words))
    (slot : ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writes)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat) :
    NatCompare.Source s pointer words := by
  refine ⟨safe, input.2.2.1, ?_⟩
  by_cases empty : words = []
  · exact Or.inl empty
  · right
    have positive : 0 < words.length := by
      cases words with
      | nil => exact False.elim (empty rfl)
      | cons first rest => simp
    rcases owned with zero | separate
    · omega
    · have apart := separate _ slot
      rcases apart with low | high
      · exact Or.inl low
      · right
        change (r (.GPR 31#5) s).toNat ≤ pointer.toNat
        omega

theorem large_words (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64))
    (input : (SszNative.NatOperand.large pointer words).At (widthLoad s)) :
    NatCompare.Words s pointer words := by
  intro i
  apply BitVec.eq_of_toNat_eq
  have equal := Option.some.inj (input.2.2.2 i)
  simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using equal

end SszArm.NatNarrow

namespace SszArm.NatToU128

theorem Owned.large_source {s : ArmState} {pointer : BitVec 64}
    {words : List (BitVec 64)} (owned : Owned s (.large pointer words)) :
    NatCompare.Source s pointer words :=
  NatNarrow.large_source s pointer words (localWrites s) owned.operandAt
    owned.operandOwned (by simp [localWrites]) owned.stackBound

theorem Owned.large_words {s : ArmState} {pointer : BitVec 64}
    {words : List (BitVec 64)} (owned : Owned s (.large pointer words)) :
    NatCompare.Words s pointer words :=
  NatNarrow.large_words s pointer words owned.operandAt

end SszArm.NatToU128
