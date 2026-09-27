import SszArm.NatAddLargeLoopOperands

namespace SszArm.NatAdd.LargeLoop

open SszNative
open Delimited (Span)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def addsOps (right : BitVec 64) (carry : Nat) : List Op :=
  [.p1604, .p1608] ++
    (if (AddWithCarry (BitVec.ofNat 64 carry) right 0#1).2.c = 1#1
     then [.p1620] else [.p1612, .p1616]) ++ [.p1624]

def addsResult (s : ArmState) (base left right : BitVec 64) (carry : Nat) : ArmState :=
  write_pstate (AddWithCarry (BitVec.ofNat 64 carry + right) left 0#1).2
    (w .PC (base + 1628#64)
      (w (.GPR 16#5) ((BitVec.ofNat 64 carry + right) + left)
        (w (.GPR 17#5) (carryWord (BitVec.ofNat 64 carry) right)
          (w (.GPR 12#5) (BitVec.ofNat 64 carry + right) s))))

/-- Both actual ADDS instructions and the intervening carry materialization.
The carry flag used by the later store tail is the second addition's flag. -/
theorem adds_run (s : ArmState) (base left right : BitVec 64) (carry : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1604#64)
    (h12 : r (.GPR 12#5) s = BitVec.ofNat 64 carry)
    (h16 : r (.GPR 16#5) s = left) (h17 : r (.GPR 17#5) s = right) :
    run (addsOps right carry).length s = addsResult s base left right carry := by
  have hpc : r .PC s = base + 1604#64 := hp
  have follows : Follows base (addsOps right carry) s := by
    by_cases first : (AddWithCarry (BitVec.ofNat 64 carry) right 0#1).2.c = 1#1 <;>
      simp [addsOps, first, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hpc, h12, h16, h17, BitVec.add_assoc]
  rw [block_run base _ s hc he ha follows]
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f with
    | GPR reg =>
      by_cases h12' : reg = 12#5 <;> by_cases h16' : reg = 16#5 <;>
        by_cases h17' : reg = 17#5 <;> (try subst reg) <;>
        by_cases first : (AddWithCarry (BitVec.ofNat 64 carry) right 0#1).2.c = 1#1 <;>
        simp_all (config := {decide := true})
          [addsOps, addsResult, carryWord, block, Op.effect, put, next,
            state_simp_rules, BitVec.add_assoc]
    | PC =>
      by_cases first : (AddWithCarry (BitVec.ofNat 64 carry) right 0#1).2.c = 1#1 <;>
        simp_all [addsOps, addsResult, block, Op.effect, put, next,
          state_simp_rules, BitVec.add_assoc]
    | SFP reg =>
      by_cases first : (AddWithCarry (BitVec.ofNat 64 carry) right 0#1).2.c = 1#1 <;>
        simp_all [addsOps, addsResult, block, Op.effect, put, next, state_simp_rules]
    | FLAG flag =>
      by_cases first : (AddWithCarry (BitVec.ofNat 64 carry) right 0#1).2.c = 1#1 <;>
        simp_all [addsOps, addsResult, block, Op.effect, put, next, state_simp_rules]
    | ERR =>
      by_cases first : (AddWithCarry (BitVec.ofNat 64 carry) right 0#1).2.c = 1#1 <;>
        simp_all [addsOps, addsResult, block, Op.effect, put, next, state_simp_rules]
  · by_cases first : (AddWithCarry (BitVec.ofNat 64 carry) right 0#1).2.c = 1#1 <;>
      simp_all [addsOps, addsResult, block, Op.effect, put, next, state_simp_rules]
  · intro n addr
    by_cases first : (AddWithCarry (BitVec.ofNat 64 carry) right 0#1).2.c = 1#1 <;>
      simp_all [addsOps, addsResult, block, Op.effect, put, next, state_simp_rules]

theorem adds_frame (s : ArmState) (base left right : BitVec 64) (carry : Nat)
    (writes : List Span) : LoopFrame writes s (addsResult s base left right carry) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [addsResult, state_simp_rules]
  · simp [addsResult, state_simp_rules]
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all) [addsResult, state_simp_rules]
  · intro reg; simp [addsResult, state_simp_rules]
  · intro a ha; simp [addsResult, state_simp_rules]

def tailOps (overflow : Bool) : List Op :=
  [.p1660] ++ (if overflow then [.p1672] else [.p1664, .p1668]) ++
    [.p1676, .p1680, .p1684, .p1688]

/-- The actual tail aggregates carry, advances the index, decrements the
unsigned remaining count, and branches to PC2044 only after the last write. -/
theorem tail_run (s : ArmState) (base : BitVec 64) (index remaining carry : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1660#64)
    (hi : index + 1 < 2^64) (hn : 0 < remaining) (hb : remaining < 2^64)
    (h14 : r (.GPR 14#5) s = BitVec.ofNat 64 remaining)
    (h15 : r (.GPR 15#5) s = BitVec.ofNat 64 index)
    (hcarry : (if r (.FLAG .C) s = 1#1 then r (.GPR 17#5) s + 1#64
      else r (.GPR 17#5) s) = BitVec.ofNat 64 carry) (writes : List Span) :
    let ops := tailOps (decide (r (.FLAG .C) s = 1#1))
    let t := block base ops s
    run ops.length s = t ∧ LoopFrame writes s t ∧
      read_pc t = base + (if remaining = 1 then 2044#64 else 1692#64) ∧
      r (.GPR 12#5) t = BitVec.ofNat 64 carry ∧
      r (.GPR 14#5) t = BitVec.ofNat 64 (remaining - 1) ∧
      r (.GPR 15#5) t = BitVec.ofNat 64 (index + 1) ∧
      r (.GPR 13#5) t = r (.GPR 13#5) s ∧ t.mem = s.mem := by
  have hpc : r .PC s = base + 1660#64 := hp
  have follows : Follows base (tailOps (decide (r (.FLAG .C) s = 1#1))) s := by
    by_cases overflow : r (.FLAG .C) s = 1#1 <;>
      simp [tailOps, overflow, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hpc, BitVec.add_assoc]
  refine ⟨block_run base _ s hc he ha follows, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply pure_frame
    intro op member
    by_cases overflow : r (.FLAG .C) s = 1#1 <;>
      simp_all [tailOps, pureOps]
  · have eqone : BitVec.ofNat 64 remaining = 1#64 ↔ remaining = 1 := by
      constructor <;> intro h <;> bv_omega
    by_cases overflow : r (.FLAG .C) s = 1#1 <;>
      simp [tailOps, overflow, block, Op.effect, put, next, state_simp_rules,
        h14, Udivti3.cmp_one_zero, eqone]
  · by_cases overflow : r (.FLAG .C) s = 1#1 <;>
      simpa [tailOps, overflow, block, Op.effect, put, next, state_simp_rules] using hcarry
  · by_cases overflow : r (.FLAG .C) s = 1#1 <;>
      simp [tailOps, overflow, block, Op.effect, put, next, state_simp_rules, h14]
    all_goals bv_omega
  · by_cases overflow : r (.FLAG .C) s = 1#1 <;>
      simp [tailOps, overflow, block, Op.effect, put, next, state_simp_rules,
        h15, BitVec.ofNat_add]
  · by_cases overflow : r (.FLAG .C) s = 1#1 <;>
      simp [tailOps, overflow, block, Op.effect, put, next, state_simp_rules]
  · by_cases overflow : r (.FLAG .C) s = 1#1 <;>
      simp [tailOps, overflow, block, Op.effect, put, next, state_simp_rules]

end SszArm.NatAdd.LargeLoop
