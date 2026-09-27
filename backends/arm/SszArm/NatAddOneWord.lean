import SszArm.NatAddOneWordState
import SszNatAdd

namespace SszArm.NatAdd

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Both source-level one-word branches execute the same architectural ADD/S
and carry materialization; no allocation occurs until the carry is known. -/
theorem one_word_sum (s : ArmState) (base : BitVec 64) (path : SumPath)
    (a b : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 path.start)
    (h2 : r (.GPR 2#5) s = a) (h4 : r (.GPR 4#5) s = b)
    (h8 : path = .normalized → r (.GPR 8#5) s = 0#64) :
    let ops := path.ops (sumOverflow a b)
    let t := block base ops s
    run ops.length s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 9#5) t = a + b ∧
      r (.GPR 8#5) t = (if 2^64 ≤ a.toNat + b.toNat then 1#64 else 0#64) ∧
      read_pc t = base + (if 2^64 ≤ a.toNat + b.toNat then 1112#64 else 1004#64) := by
  exact ⟨block_run base _ s hc he ha (one_word_follows s base path a b hp h2 h4 h8),
    one_word_frame s base path _, one_word_fields s base path a b h2 h4 h8⟩

/-- The two physical payload words agree with the exact shared u128 path. -/
theorem one_word_value (left right : SszNative.NatOperand)
    (leftSmall : left.wordCount ≤ 1) (rightSmall : right.wordCount ≤ 1) :
    (SszNative.NatAdd.lowWord left + SszNative.NatAdd.lowWord right).toNat =
      (left.value + right.value) % 2^64 ∧
      (2^64 ≤ (SszNative.NatAdd.lowWord left).toNat + (SszNative.NatAdd.lowWord right).toNat ↔
        2^64 ≤ left.value + right.value) := by
  simp only [BitVec.toNat_add, SszNative.NatAdd.lowWord_value left leftSmall,
    SszNative.NatAdd.lowWord_value right rightSmall, and_self]

end SszArm.NatAdd
