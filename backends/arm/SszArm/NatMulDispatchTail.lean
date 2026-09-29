import SszArm.NatMulDispatchTailStages

namespace SszArm.NatMul

open SszNative.Limbs

/-- +384 selects the original low left word, then swaps the original raw
right pair into X1/X2. It does not normalize or shorten that right operand. -/
theorem left_one_prepare (s : ArmState) (base : BitVec 64) (left : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 384#64)
    (ho : NatCompare.Operand s (r (.GPR 1#5) s) (r (.GPR 2#5) s) left)
    (one : sigWords left = 1) (raw : r (.GPR 8#5) s = r (.GPR 2#5) s) :
    ∃ fuel t, run fuel s = t ∧ DispatchFrame s t ∧
      read_pc t = base + 232#64 ∧
      r (.GPR 1#5) t = r (.GPR 3#5) s ∧
      r (.GPR 2#5) t = r (.GPR 4#5) s ∧
      r (.GPR 3#5) t = left[0]?.getD 0#64 := by
  have low : if r (.GPR 1#5) s = 0#64 then r (.GPR 8#5) s = left[0]?.getD 0#64
      else r (.GPR 8#5) s ≠ 0#64 ∧
        read_mem_bytes 8 (r (.GPR 1#5) s) s = left[0]?.getD 0#64 := by
    by_cases small : r (.GPR 1#5) s = 0#64
    · simp [small, ho.small small, raw]
    · obtain ⟨length, source, memory⟩ := ho.large small
      have positive : 0 < left.length := by have := sigWords_le_length left; omega
      have nonzero : r (.GPR 8#5) s ≠ 0#64 := by
        intro zero
        rw [raw] at zero
        simp [zero] at length
        omega
      have load := memory ⟨0, positive⟩
      simpa [small, List.getElem?_eq_getElem positive] using And.intro nonzero load
  let ops := leftSelectOps (r (.GPR 1#5) s)
  let u := block base ops s
  have selectRun : run ops.length s = u := block_run base ops s hc he ha
    (left_select_follows s base (left[0]?.getD 0#64) hp low)
  have selectFrame : ScanFrame s u := scan_pure_frame base ops s (by
    by_cases small : r (.GPR 1#5) s = 0#64 <;>
      simp only [ops, leftSelectOps, small, ↓reduceIte] <;> decide)
  obtain ⟨selected, pc⟩ : r (.GPR 8#5) u = left[0]?.getD 0#64 ∧
      read_pc u = base + 396#64 := left_select_values s base _ low
  let t := block base [.p396, .p400, .p404, .p408] u
  have swapRun : run 4 u = t := block_run base [.p396, .p400, .p404, .p408] u
    (selectFrame.code hc) (selectFrame.error.trans he) (selectFrame.aligned ha)
    (left_swap_follows u base pc)
  obtain ⟨finalPC, final1, final2, final3⟩ := left_swap_values u base
  refine ⟨ops.length + 4, t, ?_,
    selectFrame.dispatch.trans (dispatch_pure_frame base [.p396, .p400, .p404, .p408] u (by decide)),
    finalPC, final1.trans (selectFrame.registers 3#5 (by decide)),
    final2.trans (selectFrame.registers 4#5 (by decide)), final3.trans selected⟩
  rw [run_plus, selectRun, swapRun]

/-- The left-one test is reached only after the right-one test has failed. -/
theorem dispatch_left_count (s : ArmState) (base : BitVec 64)
    (left right : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 376#64)
    (ho : NatCompare.Operand s (r (.GPR 1#5) s) (r (.GPR 2#5) s) left)
    (leftNonzero : sigWords left ≠ 0) (rightNonzero : sigWords right ≠ 0)
    (rightNotOne : sigWords right ≠ 1)
    (h21 : r (.GPR 21#5) s = BitVec.ofNat 64 (sigWords left))
    (h22 : r (.GPR 22#5) s = BitVec.ofNat 64 (sigWords right))
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 (sigWords right - 1))
    (raw : r (.GPR 8#5) s = r (.GPR 2#5) s) :
    ∃ fuel t, run fuel s = t ∧ DispatchFrame s t ∧ DispatchExit s t base left right := by
  have bound : sigWords left < 2^64 :=
    Nat.lt_of_le_of_lt (sigWords_le_length left) ho.length_bound
  have countOne : (r (.GPR 21#5) s = 1#64) ↔ sigWords left = 1 := by
    rw [h21]
    constructor <;> intro h <;> bv_omega
  let u := block base [.p376, .p380] s
  have hu : run 2 s = u := block_run base [.p376, .p380] s hc he ha
    (count_branch_follows s base true hp)
  have huf : ScanFrame s u := scan_pure_frame base [.p376, .p380] s (by decide)
  have keep : ∀ reg : BitVec 5, r (.GPR reg) u = r (.GPR reg) s :=
    count_branch_registers s base true
  have currentPC : read_pc u = base + (if r (.GPR 21#5) s = 1#64 then 384#64 else 412#64) :=
    count_branch_pc s base true
  have hup : read_pc u = base + (if sigWords left = 1 then 384#64 else 412#64) := by
    simpa only [countOne] using currentPC
  by_cases one : sigWords left = 1
  · have hou : NatCompare.Operand u (r (.GPR 1#5) u) (r (.GPR 2#5) u) left := by
      simpa only [huf.registers 1#5 (by decide), huf.registers 2#5 (by decide)] using
        huf.operand _ _ _ ho
    have rawu : r (.GPR 8#5) u = r (.GPR 2#5) u := by
      rw [keep 8#5, keep 2#5, raw]
    obtain ⟨fuel, t, ht, htf, htp, ht1, ht2, ht3⟩ := left_one_prepare u base left
      (huf.code hc) (huf.error.trans he) (huf.aligned ha) (by simpa [one] using hup) hou one rawu
    refine ⟨2 + fuel, t, ?_, huf.dispatch.trans htf, ?_⟩
    · rw [run_plus, hu, ht]
    · apply DispatchExit.prepend huf
      simpa [DispatchExit, leftNonzero, rightNonzero, rightNotOne, one] using
        And.intro htp (And.intro ht1 (And.intro ht2 ht3))
  · refine ⟨2, u, hu, huf.dispatch, ?_⟩
    simp only [DispatchExit, leftNonzero, rightNonzero, rightNotOne, one,
      false_or, ↓reduceIte]
    exact ⟨by simpa only [one, ↓reduceIte] using hup, huf.raw,
      (keep 21#5).trans h21, (keep 22#5).trans h22,
      (keep 8#5).trans raw, (keep 9#5).trans h9⟩

/-- The right-one route's final MOV, before any prologue restore. -/
theorem right_one_prepare (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 228#64) :
    let t := block base [.p228] s
    run 1 s = t ∧ DispatchFrame s t ∧ read_pc t = base + 232#64 ∧
      r (.GPR 1#5) t = r (.GPR 1#5) s ∧ r (.GPR 2#5) t = r (.GPR 2#5) s ∧
      r (.GPR 3#5) t = r (.GPR 4#5) s := by
  exact ⟨block_run base [.p228] s hc he ha ⟨hp, trivial⟩,
    dispatch_pure_frame base [.p228] s (by decide), right_prepare_values s base hp⟩

end SszArm.NatMul
