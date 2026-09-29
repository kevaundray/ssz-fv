import SszArm.CodecFixedActivation
import SszArm.CodecStorageChildren

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (Desc)
open Dispatch.Block (next put save branch greater)

theorem desc_tag (s : ArmState) (address : BitVec 64) (desc : Desc)
    (input : Storage.DescAt s address.toNat desc) :
    read_mem_bytes 8 address s = tagWord desc.tag := by
  cases desc with
  | primitive shape =>
    have tag := (Storage.primitive_projection input).1
    cases shape <;> exact tag
  | vector child count =>
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using Storage.word_bits (7#64) input.2.1
  | list child count =>
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using Storage.word_bits (8#64) input.2.1
  | progressiveList child limit =>
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using Storage.word_bits (9#64) input.2.1
  | container fields =>
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using Storage.word_bits (10#64) input.2.1
  | progressiveContainer active fields =>
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using Storage.word_bits (11#64) input.2.1
  | compatibleUnion variants =>
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using Storage.word_bits (12#64) input.2.1

theorem Saved.dispatch {s t : ArmState} (saved : Saved s t) (tag : SszNative.Codec.DescTag) :
    Saved s (block (dispatchOps tag) t) := by
  refine ⟨(dispatch_register t tag 31#5 (by decide)).trans saved.sp, ?_, ?_, ?_⟩
  all_goals
    rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (dispatch_memory t tag))]
  · exact saved.link
  · exact saved.first
  · exact saved.second

theorem finish_register (s : ArmState) (result : Bool) (reg : BitVec 5)
    (different : reg ≠ 0#5 ∧ reg ≠ 19#5 ∧ reg ≠ 20#5 ∧ reg ≠ 30#5 ∧ reg ≠ 31#5) :
    r (.GPR reg) (finish s result) = r (.GPR reg) s := by
  rcases different with ⟨h0, h19, h20, h30, h31⟩
  cases result <;> simp [finish, returnOps, block, Op.effect, next, put,
    loadPair, restore, state_simp_rules, h0, h19, h20, h30, h31]

/-- No child is visited on these seven primitive and three variable composite
paths. Their metadata remains wholly unconstrained by this predicate. -/
def Immediate : Desc → Prop
  | .vector _ _ | .container _ | .progressiveContainer _ _ => False
  | _ => True

theorem immediate_stack (desc : Desc) (immediate : Immediate desc) :
    isFixedStack desc = 32 := by
  cases desc <;> simp_all [Immediate, isFixedStack]

theorem immediate_target (desc : Desc) (immediate : Immediate desc) :
    dispatchTarget desc.tag = if SszNative.FixedSize.isFixed desc then 188#64 else 172#64 := by
  cases desc with
  | primitive shape => cases shape <;> rfl
  | vector child count | container fields | progressiveContainer active fields =>
    exact False.elim immediate
  | _ => rfl

end SszArm.Codec.Fixed.IsFixed
