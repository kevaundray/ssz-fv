import SszArm.NatDivisionFastSmall
import SszArm.NatDivisionFastExhausted
import SszArm.NatDivisionFastReserved

namespace SszArm.NatDivision

open Delimited (MemoryFrame)

/-- Exhaustive fast-path refinement: a one-word result, a committed two-word
result, or checked scratch exhaustion. No native outcome is assumed. -/
theorem fast_correct (original s : ArmState) (base : BitVec 64) (site : FastSite)
    (operand : SszNative.NatOperand) (owned : Owned original operand)
    (saved : Saved original s) (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (divisor : r (.GPR 20#5) s = r (.GPR 3#5) original)
    (arena : r (.GPR 21#5) s = r (.GPR 4#5) original)
    (hc : JointCodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 site.start)
    (count : operand.wordCount ≤ 2)
    (input : Udivti3.numerator (fastPrepared site s base) = operand.value)
    (before : MemoryFrame (localWrites original) original s) :
    ∃ fuel, Post original (run fuel s) operand := by
  by_cases small : operand.value / (r (.GPR 3#5) original).toNat < 2^64
  · exact fast_small_post original s base site operand owned saved out divisor hc he ha hp count input small before
  · cases reserved : SszNative.Arena.reserve (arenaOf original).base (arenaOf original).capacity
      (arenaOf original).used 2 with
    | none =>
      exact fast_exhausted_post original s base site operand owned saved out divisor arena hc he ha hp
        count input small reserved before
    | some reservation =>
      exact fast_reserved_post original s base site operand reservation owned saved out divisor arena hc he ha hp
        count input small reserved before

end SszArm.NatDivision
