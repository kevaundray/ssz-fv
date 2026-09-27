import SszArm.NatCompareTrim
import SszArm.ByteViewListBlocks

namespace SszArm.NatCompare

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def rightEntry (pointer : BitVec 64) : Nat := if pointer = 0#64 then 192 else 64

def leftSmallOps (payload : BitVec 64) : List Op :=
  [.p0, .p172, .p176] ++ if payload = 0#64 then [.p180, .p184] else [.p188]

theorem left_width (s : ArmState) (base : BitVec 64) (xs : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base)
    (hi : Operand s (r (.GPR 0#5) s) (r (.GPR 1#5) s) xs) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 (sigWords xs) ∧
      read_pc t = base + BitVec.ofNat 64 (rightEntry (r (.GPR 0#5) s)) := by
  have hpc : r .PC s = base := hp
  by_cases hz : r (.GPR 0#5) s = 0#64
  · have hxs := hi.small hz
    let ops := leftSmallOps (r (.GPR 1#5) s)
    let t := block base ops s
    have hfollow : Follows base ops s := by
      by_cases hzero : r (.GPR 1#5) s = 0#64 <;>
        simp [ops, leftSmallOps, Follows, Op.row, Op.effect, put, next,
          Udivti3.compare, Udivti3.next, state_simp_rules, hpc, hz, hzero,
          BitVec.add_assoc, Udivti3.cmp_zero]
    refine ⟨ops.length, t, block_run base ops s hc he ha hfollow,
      readonly_frame base ops s ?_, block_zero base ops s ?_, ?_, ?_⟩
    · dsimp only [ops, leftSmallOps]; split <;> decide
    · dsimp only [ops, leftSmallOps]; split <;> decide
    all_goals
      by_cases hzero : r (.GPR 1#5) s = 0#64 <;>
        simp [t, ops, leftSmallOps, block, Op.effect, put, next,
          Udivti3.compare, Udivti3.next, state_simp_rules, hpc, hz, hzero,
          BitVec.add_assoc, sigWords, significantCount, hxs, rightEntry]
  · obtain ⟨hcount, hs, hm⟩ := hi.large hz
    let ops : List Op := [.p0, .p4, .p8]
    let u := block base ops s
    have hu : run 3 s = u := block_run base ops s hc he ha (by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
        hpc, hz, BitVec.add_assoc])
    have huf : Frame s u := readonly_frame base ops s (by decide)
    have hup : read_pc u = base + 12#64 := by
      simp [u, ops, block, Op.effect, put, next, state_simp_rules, hpc, hz, BitVec.add_assoc]
    have hu8 : r (.GPR 8#5) u = r (.GPR 0#5) s - 8#64 := by
      simp [u, ops, block, Op.effect, put, next, state_simp_rules]
    have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 xs.length := by
      simp [u, ops, block, Op.effect, put, next, state_simp_rules, ← hcount]
    obtain ⟨fuel, t, ht, htf, ht0, htp, ht9⟩ := trim base (r (.GPR 0#5) s) xs false
      xs.length u (Nat.le_refl _) (huf.code hc) (huf.error.trans he) (huf.aligned ha)
      hup hu8 hu9 (huf.source _ _ hs) (huf.words _ _ hs hm)
    refine ⟨3 + fuel, t, ?_, huf.trans htf,
      ht0.trans (block_zero base ops s (by decide)), ?_, ?_⟩
    · rw [run_plus, hu, ht]
    · simpa only [sigWords, Bool.false_eq_true, ↓reduceIte] using ht9
    · simpa only [trimExit, rightEntry, hz, Bool.false_eq_true, ↓reduceIte] using htp

inductive LengthKind where
  | large | small | empty
  deriving DecidableEq

def LengthKind.start : LengthKind → Nat
  | .large => 128 | .small => 216 | .empty => 264

def rightKind (pointer : BitVec 64) (count : Nat) : LengthKind :=
  if pointer = 0#64 then .small else if count = 0 then .empty else .large

def rightGuard (pointer : BitVec 64) : Op := if pointer = 0#64 then .p192 else .p64

def rightSmallOps (left payload : BitVec 64) : List Op :=
  [rightGuard left, .p196, .p200] ++ if payload = 0#64 then [.p204, .p208] else [.p212]

theorem right_width (s : ArmState) (base : BitVec 64) (ys : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (rightEntry (r (.GPR 0#5) s)))
    (hi : Operand s (r (.GPR 2#5) s) (r (.GPR 3#5) s) ys) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      read_pc t = base + BitVec.ofNat 64 (rightKind (r (.GPR 2#5) s) (sigWords ys)).start ∧
      (rightKind (r (.GPR 2#5) s) (sigWords ys) ≠ .empty →
        r (.GPR 8#5) t = BitVec.ofNat 64 (sigWords ys)) := by
  have hpc : r .PC s = base + BitVec.ofNat 64 (rightEntry (r (.GPR 0#5) s)) := hp
  by_cases hz : r (.GPR 2#5) s = 0#64
  · have hys := hi.small hz
    let ops := rightSmallOps (r (.GPR 0#5) s) (r (.GPR 3#5) s)
    let t := block base ops s
    have hfollow : Follows base ops s := by
      by_cases hl : r (.GPR 0#5) s = 0#64 <;> by_cases hzero : r (.GPR 3#5) s = 0#64 <;>
        simp [ops, rightSmallOps, rightGuard, rightEntry, Follows, Op.row, Op.effect,
          put, next, Udivti3.compare, Udivti3.next, state_simp_rules,
          hpc, hz, hl, hzero, BitVec.add_assoc, Udivti3.cmp_zero]
    refine ⟨ops.length, t, block_run base ops s hc he ha hfollow,
      readonly_frame base ops s ?_, block_zero base ops s ?_, ?_, ?_, ?_⟩
    · dsimp only [ops, rightSmallOps, rightGuard]; split <;> split <;> decide
    · dsimp only [ops, rightSmallOps, rightGuard]; split <;> split <;> decide
    all_goals
      by_cases hl : r (.GPR 0#5) s = 0#64 <;> by_cases hzero : r (.GPR 3#5) s = 0#64 <;>
        simp [t, ops, rightSmallOps, rightGuard, rightEntry, block, Op.effect,
          put, next, Udivti3.compare, Udivti3.next, state_simp_rules,
          hpc, hz, hl, hzero, BitVec.add_assoc, sigWords, significantCount,
          hys, rightKind, LengthKind.start]
  · obtain ⟨hcount, hs, hm⟩ := hi.large hz
    let ops : List Op := [rightGuard (r (.GPR 0#5) s), .p68, .p72]
    let u := block base ops s
    have hu : run 3 s = u := block_run base ops s hc he ha (by
      by_cases hl : r (.GPR 0#5) s = 0#64 <;>
        simp [ops, rightGuard, rightEntry, Follows, Op.row, Op.effect, put,
          next, state_simp_rules, hpc, hz, hl, BitVec.add_assoc])
    have huf : Frame s u := readonly_frame base ops s (by dsimp only [ops, rightGuard]; split <;> decide)
    have hup : read_pc u = base + 76#64 := by
      by_cases hl : r (.GPR 0#5) s = 0#64 <;>
        simp [u, ops, rightGuard, rightEntry, block, Op.effect, put, next,
          state_simp_rules, hpc, hz, hl, BitVec.add_assoc]
    have hu8 : r (.GPR 8#5) u = r (.GPR 2#5) s - 8#64 := by
      by_cases hl : r (.GPR 0#5) s = 0#64 <;>
        simp [u, ops, rightGuard, block, Op.effect, put, next, state_simp_rules, hl]
    have hu10 : r (.GPR 10#5) u = BitVec.ofNat 64 ys.length := by
      by_cases hl : r (.GPR 0#5) s = 0#64 <;>
        simp [u, ops, rightGuard, block, Op.effect, put, next, state_simp_rules, hl, ← hcount]
    have hu9 : r (.GPR 9#5) u = r (.GPR 9#5) s := by
      by_cases hl : r (.GPR 0#5) s = 0#64 <;>
        simp [u, ops, rightGuard, block, Op.effect, put, next, state_simp_rules, hl]
    obtain ⟨fuel, t, ht, htf, ht0, htp, htregs⟩ := trim base (r (.GPR 2#5) s) ys true
      ys.length u (Nat.le_refl _) (huf.code hc) (huf.error.trans he) (huf.aligned ha)
      hup hu8 hu10 (huf.source _ _ hs) (huf.words _ _ hs hm)
    simp only [Bool.true_eq, ↓reduceIte] at htregs
    refine ⟨3 + fuel, t, ?_, huf.trans htf,
      ht0.trans (block_zero base ops s (by dsimp only [ops, rightGuard]; split <;> decide)),
      htregs.1.trans hu9, ?_, ?_⟩
    · rw [run_plus, hu, ht]
    · by_cases hzero : significantCount ys ys.length = 0 <;>
        simpa [trimExit, rightKind, hz, hzero, LengthKind.start, sigWords] using htp
    · intro hne
      have hzero : sigWords ys ≠ 0 := by intro h; simp [rightKind, hz, h] at hne
      exact htregs.2 hzero

end SszArm.NatCompare
