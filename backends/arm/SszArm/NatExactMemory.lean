import SszArm.NatExactContract
import SszArm.NatToU128Memory

namespace SszArm.NatExact

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem frame_code {s t : ArmState} (hf : NatNarrow.Frame s t) {base : BitVec 64}
    (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, hf.program] using hc

def scanPureOps : List Op := [.p0, .p4, .p8, .p12, .p16, .p52, .p56, .p60, .p64, .p68, .p72, .p76, .p80, .p84, .p88, .p92, .p96, .p100, .p104, .p108, .p112, .p116, .p120, .p124, .p268, .p276, .p280, .p284, .p288, .p292]

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


theorem Owned.expected_reads {s : ArmState} {expected : SszNative.NatOperand}
    (owned : Owned s expected) :
    read_mem_bytes 8 (r (.GPR 1#5) s) s = expected.pointer ∧
      read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = expected.payload := by
  constructor
  · apply BitVec.eq_of_toNat_eq
    have equal := Option.some.inj owned.expectedAt.1
    simpa [widthLoad, BitVec.ofNat_toNat] using equal
  · apply BitVec.eq_of_toNat_eq
    have equal := Option.some.inj owned.expectedAt.2.1
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using equal

theorem Owned.large_source {s : ArmState} {pointer : BitVec 64}
    {words : List (BitVec 64)} (owned : Owned s (.large pointer words)) :
    NatCompare.Source s pointer words :=
  NatNarrow.large_source s pointer words (localWrites s) owned.expectedAt.2.2
    owned.operandOwned (by simp [localWrites]) owned.stackBound

theorem Owned.large_words {s : ArmState} {pointer : BitVec 64}
    {words : List (BitVec 64)} (owned : Owned s (.large pointer words)) :
    NatCompare.Words s pointer words :=
  NatNarrow.large_words s pointer words owned.expectedAt.2.2

end SszArm.NatExact
