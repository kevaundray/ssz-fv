import SszArm.NatAddBlocks
import SszArm.NatCompareOrder

namespace SszArm.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def rightRoundState (s : ArmState) (base word : BitVec 64) : ArmState :=
  block base [.p348, .p352, .p356]
    (loadResult (block base [.p308, .p312] s) base .trimRight word)

/-- Pure observations of the right width scan, independent of image binding and
execution. Its all-ones sentinel is handled by the architectural increment Z flag. -/
theorem right_round_fields (s : ArmState) (base word : BitVec 64) (n : Nat)
    (count : r (.GPR 11#5) s = BitVec.ofNat 64 n) :
    let t := rightRoundState s base word
    r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 n ∧
      r (.GPR 11#5) t = BitVec.ofNat 64 n - 1#64 ∧
      read_pc t = base + (if word = 0#64 then 308#64 else 360#64) := by
  by_cases zero : word = 0#64 <;>
    simp [rightRoundState, loadResult, LoadKind.start, LoadKind.dst,
      LoadKind.tmp, block, Op.effect, put, next, NatCompare.saved,
      state_simp_rules, count, zero]

end SszArm.NatAdd
