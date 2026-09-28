import SszArm.NatDivisionClassify
import SszArm.NatDivisionFastFrame
import SszArm.NatDivisionSmallPost
import SszArm.NatDivisionSource

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Complete actual entry-through-RET theorem for the Small branch, used as one
case of the unrestricted operand theorem. Divisor size is otherwise unrestricted. -/
theorem small_correct (s : ArmState) (base word : BitVec 64)
    (owned : Owned s (.small word)) (code : JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel, Post s (run fuel s) (.small word) := by
  obtain ⟨entryFuel, c, entryRun, classified⟩ :=
    classify_run s base (.small word) owned code.1 error aligned pc
  have cc : JointCodeAt c base := by
    simpa only [JointCodeAt, CodeAt, Udivti3.CodeAt, SszArm.CodeAt, classified.program] using code
  have cp : read_pc c = base + BitVec.ofNat 64 FastSite.small.start := by
    simpa [SszNative.NatOperand.pointer, FastSite.start] using classified.branch
  have cd : 0 < (r (.GPR 20#5) c).toNat := by rw [classified.divisor]; have := owned.divisor; omega
  let t := fastResult .small c base
  have runFast := fast_run .small c base cc classified.error classified.aligned cp cd
  have c1 : r (.GPR 1#5) c = 0#64 := classified.pointer
  have c2 : r (.GPR 2#5) c = word := classified.payload
  have prepared : Udivti3.numerator (fastPrepared .small c base) = word.toNat := by
    simp [fastPrepared, FastSite.setup, block, Op.effect, put, next,
      Udivti3.numerator, Udivti3.join, state_simp_rules, c1, c2]
  have quotient : Udivti3.numerator t = word.toNat / (r (.GPR 3#5) s).toNat := by
    simpa only [t, prepared, classified.divisor] using fast_quotient .small c base cd
  have quotientBound : Udivti3.numerator t < 2^64 := by
    rw [quotient]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) word.isLt
  have highZero : r (.GPR 1#5) t = 0#64 :=
    (high_zero_iff (r (.GPR 0#5) t) (r (.GPR 1#5) t)).2 quotientBound
  have dividedHigh : r (.GPR 1#5) (fastDivided .small c base) = 0#64 := by
    have keep := fast_finish_register .small (fastDivided .small c base) base 1#5
    exact keep.symm.trans highZero
  have tp : read_pc t = base + 644#64 := by
    simpa only [t, dividedHigh, ↓reduceIte] using fast_pc .small c base
  have lowOriginal : r (.GPR 22#5) t = word := by
    change r (.GPR 22#5) (fastResult .small c base) = word
    rw [fastResult, fast_finish_register]
    change r (.GPR 22#5) (callResult CallSite.small (fastPrepared .small c base) base) = word
    rw [call_gpr _ _ _ 22#5 (by decide) (by decide)]
    simp [fastPrepared, FastSite.setup, block, Op.effect, put, next, state_simp_rules, c2]
  have divisor : r (.GPR 20#5) t = r (.GPR 3#5) s :=
    (fast_gpr .small c base 20#5 (by decide) (by decide) (by decide)).trans classified.divisor
  have out : r (.GPR 19#5) t = r (.GPR 0#5) s :=
    (fast_gpr .small c base 19#5 (by decide) (by decide) (by decide)).trans classified.out
  have count : (SszNative.NatOperand.small word).wordCount ≤ 2 := by
    have h := SszNative.Limbs.sigWords_le_length [word]
    change SszNative.Limbs.sigWords [word] ≤ 2
    simp only [List.length_cons, List.length_nil] at h
    omega
  have value : (SszNative.NatOperand.small word).value = word.toNat := by
    simp [SszNative.NatOperand.value, SszNative.NatOperand.words, SszNative.Limbs.value]
  have mathematical : Udivti3.join (r (.GPR 0#5) t) 0#64 =
      (SszNative.NatOperand.small word).value / (r (.GPR 3#5) s).toNat := by
    change Udivti3.join (r (.GPR 0#5) t) (r (.GPR 1#5) t) =
      word.toNat / (r (.GPR 3#5) s).toNat at quotient
    rw [highZero] at quotient
    simpa only [value] using quotient
  let remainder := SszNative.NatDivision.wideRemainder (.small word) (r (.GPR 3#5) s)
  have source : outcome s (.small word) = SszNative.NatArithmetic.unchanged
      (arenaOf s).used (.ok (.small (r (.GPR 0#5) t), remainder)) :=
    source_wide_small (.small word) (r (.GPR 3#5) s) (r (.GPR 0#5) t) remainder
      (arenaOf s).base (arenaOf s).capacity (arenaOf s).used owned.divisor count mathematical rfl
  have rem : r (.GPR 22#5) t - r (.GPR 0#5) t * r (.GPR 20#5) t = remainder := by
    rw [lowOriginal, divisor]
    apply wide_remainder_low (.small word) (r (.GPR 3#5) s) word 0#64 _ 0#64 count owned.divisor_nonzero
    · simpa [Udivti3.join, value]
    · exact mathematical
  have after : Delimited.MemoryFrame (localWrites s) c t := by
    intro a _
    exact congrArg (fun memory => memory a) (fast_memory .small c base)
  have tc : CodeAt t base := by simpa only [t, CodeAt, fast_program] using cc.1
  have te : read_err t = .None := (fast_error .small c base).trans classified.error
  have ta : CheckSPAlignment t := by
    simpa only [CheckSPAlignment, state_simp_rules, t, fast_sp] using classified.aligned
  have post := small_result_post s t base (.small word) remainder owned
    (fast_saved .small s c base classified.saved) out tc te ta tp source rem
    (classified.frame.trans after)
  refine ⟨entryFuel + fastFuel .small c base + 27, ?_⟩
  rw [run_plus, run_plus, entryRun, runFast]
  exact post

end SszArm.NatDivision
