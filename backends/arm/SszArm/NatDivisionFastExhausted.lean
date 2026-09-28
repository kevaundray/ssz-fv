import SszArm.NatDivisionFastSource
import SszArm.NatDivisionExhausted

namespace SszArm.NatDivision

open Delimited (MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- A two-word quotient with insufficient checked scratch executes the real
fast BL, every reservation guard selected by the input, and the failure RET. -/
theorem fast_exhausted_post (original s : ArmState) (base : BitVec 64) (site : FastSite)
    (operand : SszNative.NatOperand) (owned : Owned original operand)
    (saved : Saved original s) (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (divisor : r (.GPR 20#5) s = r (.GPR 3#5) original)
    (arena : r (.GPR 21#5) s = r (.GPR 4#5) original)
    (hc : JointCodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 site.start)
    (count : operand.wordCount ≤ 2)
    (input : Udivti3.numerator (fastPrepared site s base) = operand.value)
    (wide : ¬ operand.value / (r (.GPR 3#5) original).toNat < 2^64)
    (reserve : SszNative.Arena.reserve (arenaOf original).base (arenaOf original).capacity
      (arenaOf original).used 2 = none)
    (before : MemoryFrame (localWrites original) original s) :
    ∃ fuel, Post original (run fuel s) operand := by
  have domain : 2 ≤ (r (.GPR 20#5) s).toNat := by rw [divisor]; exact owned.divisor
  let t := fastResult site s base
  have executed := fast_run site s base hc he ha hp (by omega)
  have arithmetic := fast_arithmetic site s base operand count domain input
  rw [divisor] at arithmetic
  have high : r (.GPR 1#5) (fastResult site s base) ≠ 0#64 := by
    intro zero
    have bound := (high_zero_iff (r (.GPR 0#5) t) (r (.GPR 1#5) t)).1 zero
    change Udivti3.numerator (fastResult site s base) < 2^64 at bound
    rw [arithmetic.1] at bound
    exact wide bound
  have source := source_wide_exhausted operand (r (.GPR 3#5) original)
    (r (.GPR 0#5) t) (r (.GPR 1#5) t) (arenaOf original).base
    (arenaOf original).capacity (arenaOf original).used owned.divisor count arithmetic.1 high reserve
  have failed : (outcome original operand).result = .error .scratchExhausted := by
    rw [outcome, source]
    rfl
  have pc : read_pc t = base + 684#64 := by
    simpa only [high, ↓reduceIte] using fast_pc_result site s base
  have memory : MemoryFrame (localWrites original) s t := by
    intro a _
    exact congrArg (fun bytes => bytes a) (fast_memory site s base)
  have code : CodeAt t base := by simpa only [t, CodeAt, fast_program] using hc.1
  have error : read_err t = .None := (fast_error site s base).trans he
  have aligned : CheckSPAlignment t := by
    simpa only [CheckSPAlignment, state_simp_rules, t, fast_sp] using ha
  have output : r (.GPR 19#5) t = r (.GPR 0#5) original :=
    (fast_gpr site s base 19#5 (by decide) (by decide) (by decide)).trans out
  have allocator : r (.GPR 21#5) t = r (.GPR 4#5) original :=
    (fast_gpr site s base 21#5 (by decide) (by decide) (by decide)).trans arena
  obtain ⟨fuel, post⟩ := wide_exhausted_post original t base operand owned
    (fast_saved site original s base saved) output allocator code error aligned pc failed reserve (before.trans memory)
  refine ⟨fastFuel site s base + fuel, ?_⟩
  rw [run_plus, executed]
  exact post

end SszArm.NatDivision
