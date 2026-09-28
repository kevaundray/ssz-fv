import SszArm.NatAddDispatch
import SszArm.NatAddPostTransport
import SszArm.NatAddZeroCorrect
import SszArm.NatAddSmallCorrect
import SszArm.NatAddLargeCorrect

namespace SszArm.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Complete entry-through-RET refinement of the bound private ARM Nat.add.
The premises name only the actual instruction image, original physical operands,
arena/output/lowering ownership and initial architectural state. No execution or
helper-correctness premise is hidden in Owned. The exact shared algorithm keeps
its borrowed representations, unsigned reservation failures and every allocated
limb, including its redundant final zero. -/
theorem add_correct (s : ArmState) (base : BitVec 64)
    (left right : SszNative.NatOperand) (owned : Owned s left right)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 entry) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  have start : read_pc s = base := by simpa [entry] using hp
  by_cases leftZero : left.wordCount = 0
  · exact zero_correct s base left right owned hc he ha start (Or.inl leftZero)
  by_cases rightZero : right.wordCount = 0
  · exact zero_correct s base left right owned hc he ha start (Or.inr rightZero)
  obtain ⟨fuel, u, execution, dispatched⟩ :=
    nonzero_entry s base left right owned hc he ha start leftZero rightZero
  have stateOwned : Owned u left right := owned.transport dispatched.frame dispatched.out
  apply Post.prepend owned dispatched.frame dispatched.out fuel execution
  rcases dispatched.route with immediate | counted
  · exact immediate_correct u base left right stateOwned (scan_code dispatched.frame hc)
      (dispatched.frame.error.trans he) (dispatched.frame.aligned ha) immediate.1
      leftZero rightZero immediate.2.1 immediate.2.2
  · obtain ⟨pc, leftCount, rightCount, representation⟩ := counted
    by_cases oneWord : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1
    · exact one_word_correct u base left right stateOwned (scan_code dispatched.frame hc)
        (dispatched.frame.error.trans he) (dispatched.frame.aligned ha)
        (by simpa only [oneWord, and_self, ↓reduceIte] using pc)
        leftZero rightZero oneWord representation
    · exact large_correct u base left right stateOwned (scan_code dispatched.frame hc)
        (dispatched.frame.error.trans he) (dispatched.frame.aligned ha)
        (by simpa only [oneWord, ↓reduceIte] using pc)
        leftZero rightZero oneWord leftCount rightCount

/-- Successful native addition stores a representation of the unbounded sum.
Scratch failure remains explicit in the complete outcome; arithmetic is inherited
from the shared, proved carry algorithm rather than a replacement ISA model. -/
theorem add_correct_arithmetic (s : ArmState) (base : BitVec 64)
    (left right result : SszNative.NatOperand) (owned : Owned s left right)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 entry)
    (success : (outcome s left right).result = .ok result) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right ∧
      SszNative.NatArithmetic.operandAt (UintCodec.widthLoad t)
        (r (.GPR 0#5) s).toNat result ∧
      UintCodec.widthLoad t ((r (.GPR 0#5) s).toNat + 64) 4 = some 0 ∧
      result.value = left.value + right.value := by
  obtain ⟨fuel, t, execution, post⟩ := add_correct s base left right owned hc he ha hp
  exact ⟨fuel, t, execution, post, post.arithmetic success⟩

end SszArm.NatAdd
