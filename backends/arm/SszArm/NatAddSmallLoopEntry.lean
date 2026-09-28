import SszArm.NatAddSmallLoop

namespace SszArm.NatAdd.SmallLoop

open UintCodec SszNative
open NatCompare (Source Words)
open Delimited (Protected)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The complete Small-left loop from its three real initialization instructions.
The first output word was stored by the allocation path. Every subsequent word,
including the extra carry word, is executed by the +1980 carry loop. X10 remains
the allocation base expected by the +2044 normalization prelude. -/
theorem entry_run (s : ArmState) (base pointer sp output small : BitVec 64)
    (right : List (BitVec 64)) (count : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1868#64)
    (h1 : r (.GPR 1#5) s = 0#64) (h2 : r (.GPR 2#5) s = small)
    (h3 : r (.GPR 3#5) s = pointer) (nonnull : pointer ≠ 0#64)
    (h4 : r (.GPR 4#5) s = BitVec.ofNat 64 right.length)
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 count)
    (h9 : r (.GPR 9#5) s = output)
    (h12 : r (.GPR 12#5) s =
      BitVec.ofNat 64 (LimbAdd.step small (right.head?.getD 0#64) 0).2)
    (hsp : r (.GPR 31#5) s = sp)
    (layout : Layout sp output (count + 1)) (positive : 0 < count)
    (source : Source s pointer right) (words : Words s pointer right)
    (owned : Protected (writes sp output 1 count) pointer.toNat (8 * right.length))
    (first : read_mem_bytes 8 output s = (LimbAdd.step small (right.head?.getD 0#64) 0).1) :
    ∃ fuel t, run fuel s = t ∧
      LoopFrame (writes sp output 1 count) s t ∧
      read_pc t = base + 2044#64 ∧
      r (.GPR 1#5) t = 0#64 ∧ r (.GPR 2#5) t = small ∧
      r (.GPR 3#5) t = pointer ∧
      r (.GPR 4#5) t = BitVec.ofNat 64 right.length ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 count ∧
      r (.GPR 9#5) t = output ∧ r (.GPR 10#5) t = r (.GPR 10#5) s ∧
      r (.GPR 13#5) t = 0#64 ∧
      r (.GPR 14#5) t = BitVec.ofNat 64 (count + 1) ∧
      Words t output (LimbAdd.loop (count + 1) [small] right 0).1 ∧
      Words t pointer right := by
  let regions := writes sp output 1 count
  let v := block base [.p1868, .p1872, .p1876] s
  have hpc : r .PC s = base + 1868#64 := hp
  have runEntry : run 3 s = v := block_run base [.p1868, .p1872, .p1876] s hc he ha (by
    simp [Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, BitVec.add_assoc])
  have entryFrame : LoopFrame regions s v := readonly_frame base _ s regions (by decide)
  have vInv : Invariant v base 1 count
      (LimbAdd.step small (right.head?.getD 0#64) 0).2 := by
    constructor
    · simp [v, block, Op.effect, put, next, state_simp_rules, Nat.ne_of_gt positive]
    · simpa [v, block, Op.effect, put, next, state_simp_rules] using h12
    · simp [v, block, Op.effect, put, next, state_simp_rules, h8]
    · simp [v, block, Op.effect, put, next, state_simp_rules]
    · exact LimbAdd.step_carry_le _ _ 0 (by omega)
  obtain ⟨fuel, t, runLoop, loopFrame, finalInv, suffix⟩ :=
    loop_run count base pointer sp output right (count + 1) v 1
      (LimbAdd.step small (right.head?.getD 0#64) 0).2
      (entryFrame.code hc) (entryFrame.error.trans he) (entryFrame.aligned ha)
      ((entryFrame.registers _ (by decide)).trans h3)
      ((entryFrame.registers _ (by decide)).trans h4)
      ((entryFrame.registers _ (by decide)).trans h9) (entryFrame.sp.trans hsp)
      layout (by omega) vInv (entryFrame.source _ _ source)
      (entryFrame.words _ _ source words owned) owned
  have frame := entryFrame.trans loopFrame
  have firstPhysical : output.toNat + 8 ≤ 2^64 := by have := layout.physical; omega
  have firstOwned : Protected regions output.toNat 8 := by
    right
    intro span member
    simp only [regions, writes, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · have := layout.separate
      have := layout.stack
      omega
    · left
      omega
  have firstFinal := (frame.memory.read output 8 firstPhysical firstOwned).trans first
  have recurrence : LimbAdd.loop (count + 1) [small] right 0 =
      let next := LimbAdd.step small (right.head?.getD 0#64) 0
      let rest := LimbAdd.loop count [] (right.drop 1) next.2
      (next.1 :: rest.1, rest.2) := by
    simp [LimbAdd.loop, List.drop_one]
  refine ⟨3 + fuel, t, ?_, frame, ?_,
    (frame.registers _ (by decide)).trans h1,
    (frame.registers _ (by decide)).trans h2,
    (frame.registers _ (by decide)).trans h3,
    (frame.registers _ (by decide)).trans h4,
    (frame.registers _ (by decide)).trans h8,
    (frame.registers _ (by decide)).trans h9,
    frame.registers _ (by decide), finalInv.remaining, ?_, ?_,
    frame.words _ _ source words owned⟩
  · rw [run_plus, runEntry, runLoop]
  · simpa using finalInv.pc
  · simpa only [Nat.add_comm 1 count] using finalInv.index
  · intro j
    have length := LimbAdd.loop_length (count + 1) [small] right 0
    have bound : j.val < count + 1 := by simpa only [length] using j.isLt
    have expected : read_mem_bytes 8 (address output j.val) t =
        (LimbAdd.loop (count + 1) [small] right 0).1[j.val]?.getD 0#64 := by
      cases hindex : j.val with
      | zero => simpa [address, recurrence, hindex] using firstFinal
      | succ k =>
        have hk : k < count := by omega
        have h := suffix k hk
        simpa only [hindex, recurrence, List.getElem?_cons_succ,
          Nat.add_comm 1 k] using h
    simpa [address, List.getElem?_eq_getElem j.isLt] using expected

end SszArm.NatAdd.SmallLoop
