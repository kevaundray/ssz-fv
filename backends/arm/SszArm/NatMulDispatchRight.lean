import SszArm.NatMulDispatchTail

namespace SszArm.NatMul

open SszNative.Limbs

/-- Exact +212/+216/+220 routing: left zero is tested before right one;
right one is tested before the left-one branch at +376. -/
theorem dispatch_right_count (s : ArmState) (base : BitVec 64)
    (left right : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 212#64)
    (hl : NatCompare.Operand s (r (.GPR 1#5) s) (r (.GPR 2#5) s) left)
    (hr : NatCompare.Operand s (r (.GPR 3#5) s) (r (.GPR 4#5) s) right)
    (large : r (.GPR 3#5) s ≠ 0#64) (rightNonzero : sigWords right ≠ 0)
    (h21 : r (.GPR 21#5) s = BitVec.ofNat 64 (sigWords left))
    (h22 : r (.GPR 22#5) s = BitVec.ofNat 64 (sigWords right))
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 (sigWords right - 1))
    (raw : r (.GPR 8#5) s = r (.GPR 2#5) s) :
    ∃ fuel t, run fuel s = t ∧ DispatchFrame s t ∧ DispatchExit s t base left right := by
  have leftBound : sigWords left < 2^64 :=
    Nat.lt_of_le_of_lt (sigWords_le_length left) hl.length_bound
  have rightBound : sigWords right < 2^64 :=
    Nat.lt_of_le_of_lt (sigWords_le_length right) hr.length_bound
  have hpc : r .PC s = base + 212#64 := hp
  by_cases zero : sigWords left = 0
  · let t := block base [.p212] s
    have ht : run 1 s = t := block_run base _ s hc he ha (by simp [Follows, Op.row, hpc])
    have htf : ScanFrame s t := scan_pure_frame base _ s (by decide)
    refine ⟨1, t, ht, htf.dispatch, ?_⟩
    simp only [DispatchExit, zero, true_or, ↓reduceIte]
    exact ⟨by simp [t, block, Op.effect, state_simp_rules, h21, zero], htf.raw⟩
  · have countNonzero : r (.GPR 21#5) s ≠ 0#64 := by rw [h21]; bv_omega
    have flag : ((AddWithCarry (r (.GPR 22#5) s) (~~~(1#64)) 1#1).2.z = 1#1) ↔
        sigWords right = 1 := by
      rw [Udivti3.cmp_zero, h22]
      constructor <;> intro h <;> bv_omega
    let u := block base [.p212, .p216, .p220] s
    have hu : run 3 s = u := block_run base _ s hc he ha (by
      simp [Follows, Op.row, Op.effect, Udivti3.compare, Udivti3.next,
        state_simp_rules, hpc, countNonzero, BitVec.add_assoc])
    have huf : ScanFrame s u := scan_pure_frame base _ s (by decide)
    have hup : read_pc u = base + (if sigWords right = 1 then 224#64 else 376#64) := by
      by_cases one : sigWords right = 1 <;>
        simp [u, block, Op.effect, Udivti3.compare, Udivti3.next,
          state_simp_rules, flag, one]
    have hlu : NatCompare.Operand u (r (.GPR 1#5) u) (r (.GPR 2#5) u) left := by
      simpa only [huf.registers 1#5 (by decide), huf.registers 2#5 (by decide)] using
        huf.operand _ _ _ hl
    have hru : NatCompare.Operand u (r (.GPR 3#5) u) (r (.GPR 4#5) u) right := by
      simpa only [huf.registers 3#5 (by decide), huf.registers 4#5 (by decide)] using
        huf.operand _ _ _ hr
    by_cases one : sigWords right = 1
    · have largeu : r (.GPR 3#5) u ≠ 0#64 := by
        simpa only [huf.registers 3#5 (by decide)] using large
      have positive : 0 < right.length := by have := sigWords_le_length right; omega
      have load : read_mem_bytes 8 (r (.GPR 3#5) u) u = right[0]?.getD 0#64 := by
        have memory := (hru.large largeu).2.2
        simpa [List.getElem?_eq_getElem positive] using memory ⟨0, positive⟩
      let t := block base [.p224] u
      have upc : r .PC u = base + 224#64 := by simpa [one] using hup
      have ht : run 1 u = t := block_run base _ u
        (huf.code hc) (huf.error.trans he) (huf.aligned ha) (by simp [Follows, Op.row, upc])
      refine ⟨3 + 1, t, ?_, huf.dispatch.trans (dispatch_pure_frame base _ u (by decide)), ?_⟩
      · rw [run_plus, hu, ht]
      · apply DispatchExit.prepend huf
        simp [DispatchExit, zero, rightNonzero, one, t, block, Op.effect, put, next,
          state_simp_rules, upc, load, BitVec.add_assoc]
    · have hu21 : r (.GPR 21#5) u = BitVec.ofNat 64 (sigWords left) := by
        simpa [u, block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules] using h21
      have hu22 : r (.GPR 22#5) u = BitVec.ofNat 64 (sigWords right) := by
        simpa [u, block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules] using h22
      have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 (sigWords right - 1) := by
        simpa [u, block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules] using h9
      have rawu : r (.GPR 8#5) u = r (.GPR 2#5) u := by
        simpa [u, block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules] using raw
      obtain ⟨fuel, t, ht, htf, exit⟩ := dispatch_left_count u base left right
        (huf.code hc) (huf.error.trans he) (huf.aligned ha) (by simpa [one] using hup)
        hlu zero rightNonzero one hu21 hu22 hu9 rawu
      refine ⟨3 + fuel, t, ?_, huf.dispatch.trans htf, DispatchExit.prepend huf exit⟩
      rw [run_plus, hu, ht]

/-- The complete borrowed-right phase retains the complete raw source span,
including redundant limbs and empty Large representations. -/
theorem right_dispatch (s : ArmState) (base : BitVec 64)
    (left right : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 160#64)
    (hl : NatCompare.Operand s (r (.GPR 1#5) s) (r (.GPR 2#5) s) left)
    (hr : NatCompare.Operand s (r (.GPR 3#5) s) (r (.GPR 4#5) s) right)
    (large : r (.GPR 3#5) s ≠ 0#64)
    (h21 : r (.GPR 21#5) s = BitVec.ofNat 64 (sigWords left))
    (raw : r (.GPR 8#5) s = r (.GPR 2#5) s) :
    ∃ fuel t, run fuel s = t ∧ DispatchFrame s t ∧ DispatchExit s t base left right := by
  obtain ⟨length, source, memory⟩ := hr.large large
  have payload : r (.GPR 4#5) s = BitVec.ofNat 64 right.length := by
    rw [← length, BitVec.ofNat_toNat]
  obtain ⟨fuel, u, hu, huf, hu8, hu21, hu22, hu9, hup⟩ := right_large_scan s base
    (r (.GPR 3#5) s) right hc he ha hp rfl payload source memory
  by_cases zero : sigWords right = 0
  · refine ⟨fuel, u, hu, huf.dispatch, ?_⟩
    simp only [DispatchExit, zero, or_true, ↓reduceIte]
    exact ⟨by simpa [zero] using hup, huf.raw⟩
  · have hlu : NatCompare.Operand u (r (.GPR 1#5) u) (r (.GPR 2#5) u) left := by
      simpa only [huf.registers 1#5 (by decide), huf.registers 2#5 (by decide)] using
        huf.operand _ _ _ hl
    have hru : NatCompare.Operand u (r (.GPR 3#5) u) (r (.GPR 4#5) u) right := by
      simpa only [huf.registers 3#5 (by decide), huf.registers 4#5 (by decide)] using
        huf.operand _ _ _ hr
    have largeu : r (.GPR 3#5) u ≠ 0#64 := by
      simpa only [huf.registers 3#5 (by decide)] using large
    have rawu : r (.GPR 8#5) u = r (.GPR 2#5) u := by
      rw [hu8, huf.registers 2#5 (by decide), raw]
    obtain ⟨rest, t, ht, htf, exit⟩ := dispatch_right_count u base left right
      (huf.code hc) (huf.error.trans he) (huf.aligned ha) (by simpa [zero] using hup)
      hlu hru largeu zero (hu21.trans h21) (hu22 zero) (hu9 zero) rawu
    refine ⟨fuel + rest, t, ?_, huf.dispatch.trans htf, DispatchExit.prepend huf exit⟩
    rw [run_plus, hu, ht]

end SszArm.NatMul
