import SszArm.NatDivisionFastSource
import SszArm.NatDivisionSmallPost

namespace SszArm.NatDivision

open Delimited (MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Any fast operand whose mathematical quotient is one word executes through
RET without touching the arena. This includes noncanonical physical Large inputs. -/
theorem fast_small_post (original s : ArmState) (base : BitVec 64) (site : FastSite)
    (operand : SszNative.NatOperand) (owned : Owned original operand)
    (saved : Saved original s) (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (divisor : r (.GPR 20#5) s = r (.GPR 3#5) original)
    (hc : JointCodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 site.start)
    (count : operand.wordCount ≤ 2)
    (input : Udivti3.numerator (fastPrepared site s base) = operand.value)
    (small : operand.value / (r (.GPR 3#5) original).toNat < 2^64)
    (before : MemoryFrame (localWrites original) original s) :
    ∃ fuel, Post original (run fuel s) operand := by
  have domain : 2 ≤ (r (.GPR 20#5) s).toNat := by rw [divisor]; exact owned.divisor
  let t := fastResult site s base
  have executed := fast_run site s base hc he ha hp (by omega)
  have arithmetic := fast_arithmetic site s base operand count domain input
  rw [divisor] at arithmetic
  have highZero : r (.GPR 1#5) t = 0#64 := by
    apply (high_zero_iff (r (.GPR 0#5) t) (r (.GPR 1#5) t)).2
    rw [arithmetic.1]
    exact small
  have quotient : Udivti3.join (r (.GPR 0#5) t) 0#64 =
      operand.value / (r (.GPR 3#5) original).toNat := by
    simpa only [Udivti3.numerator, highZero] using arithmetic.1
  let remainder := SszNative.NatDivision.wideRemainder operand (r (.GPR 3#5) original)
  have source : outcome original operand = SszNative.NatArithmetic.unchanged
      (arenaOf original).used (.ok (.small (r (.GPR 0#5) t), remainder)) :=
    source_wide_small operand (r (.GPR 3#5) original) (r (.GPR 0#5) t) remainder
      (arenaOf original).base (arenaOf original).capacity (arenaOf original).used
      owned.divisor count quotient rfl
  have pc : read_pc t = base + 644#64 := by
    simpa only [highZero, ↓reduceIte] using fast_pc_result site s base
  have memory : MemoryFrame (localWrites original) s t := by
    intro a _
    exact congrArg (fun bytes => bytes a) (fast_memory site s base)
  have code : CodeAt t base := by simpa only [t, CodeAt, fast_program] using hc.1
  have error : read_err t = .None := (fast_error site s base).trans he
  have aligned : CheckSPAlignment t := by
    simpa only [CheckSPAlignment, t, fast_sp] using ha
  have output : r (.GPR 19#5) t = r (.GPR 0#5) original :=
    (fast_gpr site s base 19#5 (by decide) (by decide) (by decide)).trans out
  have post := small_result_post original t base operand remainder owned
    (fast_saved site original s base saved) output code error aligned pc source arithmetic.2 (before.trans memory)
  refine ⟨fastFuel site s base + 27, ?_⟩
  rw [run_plus, executed]
  exact post

end SszArm.NatDivision
