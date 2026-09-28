import SszArm.NatAddSmallLoopArithmetic

namespace SszArm.NatAdd.SmallLoop

open UintCodec
open NatCompare (Source Words saved)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def readState (s : ArmState) (base : BitVec 64)
    (right : List (BitVec 64)) (index : Nat) : ArmState :=
  let guard := block base [.p1980, .p1984] s
  if index < right.length then
    loadResult guard base .loopRightSmall (right[index]?.getD 0#64)
  else block base [.p1988, .p1992] guard

def readFuel (right : List (BitVec 64)) (index : Nat) : Nat :=
  if index < right.length then 10 else 4

/-- The unsigned bounds check executes the indexed load only for physical input
words. Its two-instruction zero alternative has no lowering-slot access. -/
theorem right_read (s : ArmState) (base pointer : BitVec 64)
    (right : List (BitVec 64)) (index : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1980#64)
    (h3 : r (.GPR 3#5) s = pointer)
    (h4 : r (.GPR 4#5) s = BitVec.ofNat 64 right.length)
    (h14 : r (.GPR 14#5) s = BitVec.ofNat 64 index)
    (hi : index < 2^64) (hs : Source s pointer right) (hm : Words s pointer right) :
    run (readFuel right index) s = readState s base right index ∧
      read_pc (readState s base right index) = base + 1912#64 ∧
      r (.GPR 15#5) (readState s base right index) = right[index]?.getD 0#64 := by
  have hr : right.length < 2^64 := by have := hs.2.1; omega
  have hg := right_guard index right hi hr
  let g := block base [.p1980, .p1984] s
  have hpc : r .PC s = base + 1980#64 := hp
  have runGuard : run 2 s = g := block_run base [.p1980, .p1984] s hc he ha (by
    simp [Follows, Op.row, Op.effect, Udivti3.compare, Udivti3.next,
      next, state_simp_rules, hpc, BitVec.add_assoc])
  have frameGuard : NatCompare.Frame s g := by
    constructor
    · simp [g]
    · simp [g]
    · intro reg hreg
      simp [g, block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules]
    · intro reg
      simp [g, block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules]
    · intro a ha
      simp [g, block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules]
  have g3 : r (.GPR 3#5) g = pointer := (frameGuard.registers _ (by decide)).trans h3
  have g14 : r (.GPR 14#5) g = BitVec.ofNat 64 index :=
    (frameGuard.registers _ (by decide)).trans h14
  by_cases present : index < right.length
  · have gp : read_pc g = base + 1880#64 := by
      simp [g, block, Op.effect, Udivti3.compare, Udivti3.next,
        state_simp_rules, h14, h4, hg, present]
    have source := frameGuard.source pointer right hs
    have words := frameGuard.words pointer right hs hm
    have loaded := NatCompare.limb_load g pointer right index 9#5 present source words
    have load := load_run g base (right[index]?.getD 0#64) .loopRightSmall
      (scan_code frameGuard hc) (frameGuard.error.trans he) (frameGuard.aligned ha)
      gp source.1 (by simpa [LoadKind.ptr, LoadKind.index, LoadKind.tmp, g3, g14] using loaded)
    refine ⟨?_, ?_, ?_⟩
    · simp only [readFuel, present, ↓reduceIte]
      rw [show 10 = 2 + 8 by decide, run_plus, runGuard, load]
      simp only [readState, present, ↓reduceIte, g]
    · simp [readState, present, loadResult, LoadKind.start, state_simp_rules]
    · simp [readState, present, loadResult, LoadKind.dst, state_simp_rules]
  · have gp : read_pc g = base + 1988#64 := by
      simp [g, block, Op.effect, Udivti3.compare, Udivti3.next,
        state_simp_rules, h14, h4, hg, present]
    have gpc : r .PC g = base + 1988#64 := gp
    have runZero : run 2 g = block base [.p1988, .p1992] g :=
      block_run base [.p1988, .p1992] g (scan_code frameGuard hc)
        (frameGuard.error.trans he) (frameGuard.aligned ha) (by
          simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, gpc, BitVec.add_assoc])
    refine ⟨?_, ?_, ?_⟩
    · simp only [readFuel, present, ↓reduceIte]
      rw [show 4 = 2 + 2 by decide, run_plus, runGuard, runZero]
      simp only [readState, present, ↓reduceIte, g]
    · simp [readState, present, block, Op.effect, put, next, state_simp_rules]
    · simp [readState, present, block, Op.effect, put, next, state_simp_rules]

def tailOps (carry : Bool) : List Op :=
  if carry then [.p1952, .p1964, .p1968, .p1972, .p1976]
  else [.p1952, .p1956, .p1960, .p1968, .p1972, .p1976]

def tailState (s : ArmState) (base : BitVec 64) : ArmState :=
  block base (tailOps (decide (r (.FLAG .C) s = 1#1))) s

/-- Both real carry-materialization branches, followed by the remaining-count
SUBS, index move and back edge. The zero remaining state exits at +2044. -/
theorem tail_run (s : ArmState) (base : BitVec 64) (remaining : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1952#64)
    (h13 : r (.GPR 13#5) s = BitVec.ofNat 64 (remaining + 1))
    (hr : remaining + 1 < 2^64) :
    run (tailOps (decide (r (.FLAG .C) s = 1#1))).length s = tailState s base ∧
      r (.GPR 12#5) (tailState s base) =
        (if r (.FLAG .C) s = 1#1 then 1#64 else 0#64) ∧
      r (.GPR 13#5) (tailState s base) = BitVec.ofNat 64 remaining ∧
      r (.GPR 14#5) (tailState s base) = r (.GPR 16#5) s ∧
      read_pc (tailState s base) =
        base + (if remaining = 0 then 2044#64 else 1980#64) := by
  have hz : BitVec.ofNat 64 (remaining + 1) = 1#64 ↔ remaining = 0 := by bv_omega
  have dec : BitVec.ofNat 64 (remaining + 1) - 1#64 = BitVec.ofNat 64 remaining := by
    bv_omega
  have hpc : r .PC s = base + 1952#64 := hp
  have follow : Follows base (tailOps (decide (r (.FLAG .C) s = 1#1))) s := by
    by_cases carry : r (.FLAG .C) s = 1#1 <;>
      simp [tailOps, carry, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hpc, BitVec.add_assoc]
  refine ⟨block_run base _ s hc he ha follow, ?_, ?_, ?_, ?_⟩
  · by_cases carry : r (.FLAG .C) s = 1#1 <;>
      simp [tailState, tailOps, carry, block, Op.effect, put, next, state_simp_rules]
  · by_cases carry : r (.FLAG .C) s = 1#1 <;>
      simp [tailState, tailOps, carry, block, Op.effect, put, next,
        state_simp_rules, h13, dec]
  · by_cases carry : r (.FLAG .C) s = 1#1 <;>
      simp [tailState, tailOps, carry, block, Op.effect, put, next, state_simp_rules]
  · by_cases carry : r (.FLAG .C) s = 1#1 <;> by_cases last : remaining = 0 <;>
      simp [tailState, tailOps, carry, block, Op.effect, put, next,
        state_simp_rules, h13, hz, last]

end SszArm.NatAdd.SmallLoop
