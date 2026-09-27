import SszArm.NatDivisionExec
import SszArm.NatDivisionArithmetic

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

inductive FastSite where
  | small | wide | low | zero
  deriving DecidableEq

def FastSite.call : FastSite → CallSite
  | .small => .small
  | .wide => .wide
  | .low => .low
  | .zero => .zero

def FastSite.start : FastSite → Nat
  | .small => 300
  | .wide => 344
  | .low => 620
  | .zero => 656

def FastSite.setup : FastSite → List Op
  | .small => [.p300, .p304, .p308, .p312]
  | .wide => [.p344, .p348, .p352, .p356]
  | .low => [.p620, .p624, .p628, .p632]
  | .zero => [.p656, .p660, .p664, .p668, .p672]

def fastPrepared (site : FastSite) (s : ArmState) (base : BitVec 64) : ArmState :=
  block base site.setup s

def FastSite.finish (site : FastSite) (s : ArmState) : List Op :=
  match site with
  | .small => if r (.GPR 1#5) s = 0#64 then [.p320] else [.p320, .p324]
  | .wide => if r (.GPR 1#5) s = 0#64 then [.p364] else [.p364, .p368]
  | .low => [.p640]
  | .zero => [.p680]

def fastDivided (site : FastSite) (s : ArmState) (base : BitVec 64) : ArmState :=
  callResult site.call (fastPrepared site s base) base

def fastResult (site : FastSite) (s : ArmState) (base : BitVec 64) : ArmState :=
  let divided := fastDivided site s base
  block base (site.finish divided) divided

def fastFuel (site : FastSite) (s : ArmState) (base : BitVec 64) : Nat :=
  site.setup.length + callFuel site.call (fastPrepared site s base) base +
    (site.finish (fastDivided site s base)).length

theorem fast_setup_run (site : FastSite) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 site.start) :
    run site.setup.length s = fastPrepared site s base := by
  apply block_run base site.setup s hc he ha
  have hpc : r .PC s = base + BitVec.ofNat 64 site.start := hp
  cases site <;>
    simp (config := {decide := true, instances := true})
      [FastSite.setup, FastSite.start, Follows, Op.row, Op.effect, put, next,
       state_simp_rules, hpc, BitVec.add_assoc]

theorem fast_setup_pc (site : FastSite) (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + BitVec.ofNat 64 site.start) :
    read_pc (fastPrepared site s base) = base + BitVec.ofNat 64 site.call.offset := by
  have hpc : r .PC s = base + BitVec.ofNat 64 site.start := hp
  cases site <;>
    simp [fastPrepared, block, FastSite.setup, FastSite.start, FastSite.call,
      CallSite.offset, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]

theorem fast_setup_divisor (site : FastSite) (s : ArmState) (base : BitVec 64) :
    Udivti3.divisor (fastPrepared site s base) = (r (.GPR 20#5) s).toNat := by
  cases site <;>
    simp [fastPrepared, block, FastSite.setup, Udivti3.divisor, Udivti3.join,
      Op.effect, put, next, state_simp_rules]

theorem fast_finish_run (site : FastSite) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (site.call.offset + 4)) :
    run (site.finish s).length s = block base (site.finish s) s := by
  apply block_run base (site.finish s) s hc he ha
  have hpc : r .PC s = base + BitVec.ofNat 64 (site.call.offset + 4) := hp
  cases site <;> by_cases hz : r (.GPR 1#5) s = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [FastSite.finish, FastSite.call, CallSite.offset, Follows, Op.row,
       Op.effect, state_simp_rules, hpc, hz]

/-- Includes the true runtime call and its return before testing the high
quotient word. The branch is decided by the proved quotient, not a semantic
helper assumption. -/
theorem fast_run (site : FastSite) (s : ArmState) (base : BitVec 64)
    (hc : JointCodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 site.start)
    (hd : 0 < (r (.GPR 20#5) s).toNat) :
    run (fastFuel site s base) s = fastResult site s base := by
  let q := fastPrepared site s base
  have cq : JointCodeAt q base := by
    simpa only [q, fastPrepared, JointCodeAt, CodeAt, Udivti3.CodeAt,
      SszArm.CodeAt, block_program] using hc
  have eq : read_err q = .None := (block_error _ _ _).trans he
  have aq : CheckSPAlignment q := block_aligned _ _ _ ha
  have pq := fast_setup_pc site s base hp
  have dq : 0 < Udivti3.divisor q := by
    simpa only [q, fast_setup_divisor] using hd
  have dividedRun := call_run site.call q base cq eq pq dq
  have cd : CodeAt (fastDivided site s base) base := by
    simpa only [fastDivided, CodeAt, call_program] using cq.1
  have ed : read_err (fastDivided site s base) = .None := (call_err _ _ _).trans eq
  have ad : CheckSPAlignment (fastDivided site s base) := by
    simpa only [q, CheckSPAlignment, state_simp_rules, fastDivided, call_sp] using aq
  have pd := call_return site.call q base dq
  rw [fastFuel, run_plus, run_plus, fast_setup_run site s base hc.1 he ha hp, dividedRun]
  exact fast_finish_run site (fastDivided site s base) base cd ed ad pd

theorem fast_pc (site : FastSite) (s : ArmState) (base : BitVec 64) :
    read_pc (fastResult site s base) =
      if r (.GPR 1#5) (fastDivided site s base) = 0#64 then base + 644#64 else base + 684#64 := by
  by_cases hz : r (.GPR 1#5) (fastDivided site s base) = 0#64 <;> cases site <;>
    simp [fastResult, FastSite.finish, block, Op.effect, state_simp_rules, hz]

theorem fast_quotient (site : FastSite) (s : ArmState) (base : BitVec 64)
    (hd : 0 < (r (.GPR 20#5) s).toNat) :
    Udivti3.numerator (fastResult site s base) =
      Udivti3.numerator (fastPrepared site s base) / (r (.GPR 20#5) s).toNat := by
  have dq : 0 < Udivti3.divisor (fastPrepared site s base) := by
    rw [fast_setup_divisor]; exact hd
  have h := call_quotient site.call (fastPrepared site s base) base dq
  rw [fast_setup_divisor] at h
  have keep : Udivti3.numerator (fastResult site s base) =
      Udivti3.numerator (fastDivided site s base) := by
    by_cases hz : r (.GPR 1#5) (fastDivided site s base) = 0#64 <;> cases site <;>
      simp [fastResult, FastSite.finish, block, Op.effect, Udivti3.numerator,
        state_simp_rules, hz]
  exact keep.trans h

@[simp] theorem fast_memory (site : FastSite) (s : ArmState) (base : BitVec 64) :
    (fastResult site s base).mem = s.mem := by
  have finish : (fastResult site s base).mem = (fastDivided site s base).mem := by
    by_cases hz : r (.GPR 1#5) (fastDivided site s base) = 0#64 <;> cases site <;>
      simp [fastResult, FastSite.finish, block, Op.effect, state_simp_rules, hz]
  rw [finish, fastDivided, call_memory]
  cases site <;> simp [fastPrepared, block, FastSite.setup, Op.effect, put, next, state_simp_rules]

@[simp] theorem fast_program (site : FastSite) (s : ArmState) (base : BitVec 64) :
    (fastResult site s base).program = s.program := by
  simp only [fastResult, block_program, fastDivided, call_program, fastPrepared]

@[simp] theorem fast_error (site : FastSite) (s : ArmState) (base : BitVec 64) :
    read_err (fastResult site s base) = read_err s := by
  simp only [fastResult, block_error, fastDivided, call_err, fastPrepared]

end SszArm.NatDivision
