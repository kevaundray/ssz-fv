import SszArm.NatMulDispatchRightStages

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
  by_cases zero : sigWords left = 0
  · let t := block base [.p212] s
    have ht : run 1 s = t := block_run base [.p212] s hc he ha ⟨hp, trivial⟩
    have htf : ScanFrame s t := scan_pure_frame base [.p212] s (by decide)
    have pc : read_pc t = base + (if r (.GPR 21#5) s = 0#64 then 264#64 else 216#64) :=
      left_zero_guard_pc s base
    refine ⟨1, t, ht, htf.dispatch, ?_⟩
    simp only [DispatchExit, zero, true_or, ↓reduceIte]
    arm_word_nf at pc h21
    exact ⟨by simpa only [h21, zero, ↓reduceIte] using pc, htf.raw⟩
  · have countNonzero : r (.GPR 21#5) s ≠ 0#64 := by rw [h21]; bv_omega
    have countOne : (r (.GPR 22#5) s = 1#64) ↔ sigWords right = 1 := by
      rw [h22]
      constructor <;> intro h <;> bv_omega
    let u := block base [.p212, .p216, .p220] s
    have hu : run 3 s = u := block_run base [.p212, .p216, .p220] s hc he ha
      (right_count_follows s base hp countNonzero)
    have huf : ScanFrame s u := scan_pure_frame base [.p212, .p216, .p220] s (by decide)
    have keep : ∀ reg : BitVec 5, r (.GPR reg) u = r (.GPR reg) s :=
      right_count_registers s base
    have currentPC : read_pc u = base + (if r (.GPR 22#5) s = 1#64 then 224#64 else 376#64) :=
      right_count_pc s base
    have hup : read_pc u = base + (if sigWords right = 1 then 224#64 else 376#64) := by
      simpa only [countOne] using currentPC
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
      have upc : read_pc u = base + 224#64 := by simpa only [one, ↓reduceIte] using hup
      have ht : run 1 u = t := block_run base [.p224] u
        (huf.code hc) (huf.error.trans he) (huf.aligned ha) ⟨upc, trivial⟩
      obtain ⟨finalPC, final1, final2, final3, final4⟩ := right_one_load_values u base upc
      refine ⟨3 + 1, t, ?_, huf.dispatch.trans (dispatch_pure_frame base [.p224] u (by decide)), ?_⟩
      · rw [run_plus, hu, ht]
      · apply DispatchExit.prepend huf
        simp only [DispatchExit, zero, one, false_or, ↓reduceIte]
        exact ⟨finalPC, final1, final2, final3, final4.trans load⟩
    · have hu21 : r (.GPR 21#5) u = BitVec.ofNat 64 (sigWords left) := (keep 21#5).trans h21
      have hu22 : r (.GPR 22#5) u = BitVec.ofNat 64 (sigWords right) := (keep 22#5).trans h22
      have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 (sigWords right - 1) := (keep 9#5).trans h9
      have rawu : r (.GPR 8#5) u = r (.GPR 2#5) u := by
        rw [keep 8#5, keep 2#5, raw]
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
    rw [← length]
    arm_word_nf
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
