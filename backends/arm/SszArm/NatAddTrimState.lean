import SszArm.NatAddBlocks

namespace SszArm.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def leftRoundState (s : ArmState) (base word : BitVec 64) : ArmState :=
  block base [.p52, .p56]
    (loadResult (block base [.p12, .p16] s) base .trimLeft word)

/-- Opaque register observations of one width-scan round. The actual execution
proof does not simplify its code-image, memory and run hypotheses together. -/
theorem left_round_fields (s : ArmState) (base word : BitVec 64) (n : Nat)
    (count : r (.GPR 10#5) s = BitVec.ofNat 64 (n + 1)) :
    let t := leftRoundState s base word
    r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 (n + 1) ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 n ∧
      read_pc t = base + (if word = 0#64 then 12#64 else 60#64) := by
  by_cases zero : word = 0#64 <;>
    simp [leftRoundState, loadResult, LoadKind.start, LoadKind.dst,
      LoadKind.tmp, block, Op.effect, put, next, NatCompare.saved,
      state_simp_rules, count, zero, BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem trim_predecessor_address (pointer : BitVec 64) (n : Nat) :
    pointer - 8#64 + (BitVec.ofNat 64 (n + 1) <<< 3) =
      pointer + (BitVec.ofNat 64 n <<< 3) := by
  bv_omega

end SszArm.NatAdd
