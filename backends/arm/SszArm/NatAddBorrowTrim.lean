import SszArm.NatAddRightTrim
import SszArm.NatAddBorrowTrimState

namespace SszArm.NatAdd

open UintCodec SszNative.Limbs
open NatCompare (Source Words saved)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The zero-operand branches rescan the original borrowed representation. -/
theorem borrow_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat) (right : Bool)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (borrowHead right))
    (hptr : r (.GPR (borrowPointer right)) s = pointer)
    (hn : n < words.length)
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 n)
    (hs : Source s pointer words) (hm : Words s pointer words) :
    let t := borrowRoundState s base (words[n]?.getD 0#64) right
    run 13 s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 n ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 n - 1#64 ∧
      read_pc t = base + BitVec.ofNat 64
        (if words[n]?.getD 0#64 = 0#64 then borrowHead right else borrowExit right (n+1)) := by
  have notLast : BitVec.ofNat 64 n + 1#64 ≠ 0#64 := by have := hs.2.1; bv_omega
  let u := block base (borrowGuard right) s
  have hpc : r .PC s = base + BitVec.ofNat 64 (borrowHead right) := hp
  have follow : Follows base (borrowGuard right) s := by
    cases right <;> simp [borrowGuard, borrowHead, Follows, Op.row, Op.effect,
      next, state_simp_rules, hpc, h9, BitVec.add_assoc]
  have hu : run 2 s = u := by
    have hx := block_run base (borrowGuard right) s hc he ha follow
    cases right <;> simpa [u, borrowGuard] using hx
  have huf : NatCompare.Frame s u := scan_frame base _ _ (by cases right <;> decide)
  have hup : read_pc u = base + BitVec.ofNat 64 (borrowKind right).start := by
    cases right <;> simp [u, borrowGuard, borrowKind, LoadKind.start, block,
      Op.effect, next, state_simp_rules, h9, notLast]
  have hus : Source u pointer words := huf.source _ _ hs
  have hum : Words u pointer words := huf.words _ _ hs hm
  have hload : read_mem_bytes 8
      (r (.GPR (borrowKind right).ptr) u + (r (.GPR (borrowKind right).index) u <<< 3))
      (saved u (borrowKind right).tmp) = words[n]?.getD 0#64 := by
    obtain ⟨pointerReg, indexReg⟩ := borrow_guard_inputs s base right
    change r (.GPR (borrowKind right).ptr) u =
      r (.GPR (borrowPointer right)) s at pointerReg
    change r (.GPR (borrowKind right).index) u = r (.GPR 9#5) s at indexReg
    have temporary : (borrowKind right).tmp = 11#5 := by cases right <;> rfl
    rw [pointerReg, indexReg, hptr, h9, temporary]
    exact NatCompare.limb_load u pointer words n 11#5 hn hus hum
  let v := loadResult u base (borrowKind right) (words[n]?.getD 0#64)
  have hv : run 8 u = v := load_run u base _ (borrowKind right) (scan_code huf hc)
    (huf.error.trans he) (huf.aligned ha) hup hus.1 hload
  have hvf : NatCompare.Frame s v := huf.trans
    (load_compare_frame u base _ (borrowKind right) hus.1 (by cases right <;> decide))
  have tailFollow : Follows base (borrowTail right) v := by
    cases right <;> simp [v, borrowTail, borrowKind, loadResult, LoadKind.start,
      Follows, Op.row, Op.effect, put, next, state_simp_rules, BitVec.add_assoc]
  have ht := block_run base (borrowTail right) v (scan_code hvf hc)
    (hvf.error.trans he) (hvf.aligned ha) tailFollow
  have htf : NatCompare.Frame v (block base (borrowTail right) v) :=
    scan_frame base _ _ (by cases right <;> decide)
  refine ⟨?_, hvf.trans htf, borrow_round_fields s base _ right n h9⟩
  · rw [show 13 = 2 + 8 + 3 by decide, run_plus, run_plus, hu, hv]
    cases right <;> exact ht

theorem borrow_trim (base pointer : BitVec 64) (words : List (BitVec 64)) (right : Bool) :
    ∀ n (s : ArmState), n ≤ words.length →
    CodeAt s base → read_err s = .None → CheckSPAlignment s →
    read_pc s = base + BitVec.ofNat 64 (borrowHead right) →
    r (.GPR (borrowPointer right)) s = pointer →
    r (.GPR 9#5) s = BitVec.ofNat 64 n - 1#64 →
    Source s pointer words → Words s pointer words →
    ∃ fuel t, run fuel s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      (significantCount words n ≠ 0 →
        r (.GPR 8#5) t = BitVec.ofNat 64 (significantCount words n - 1)) ∧
      read_pc t = base + BitVec.ofNat 64 (borrowExit right (significantCount words n)) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp hptr h9 hs hm
    let ops : List Op := borrowGuard right ++ if right then [.p468] else []
    let t := block base ops s
    have hpc : r .PC s = base + BitVec.ofNat 64 (borrowHead right) := hp
    have follow : Follows base ops s := by
      cases right <;> simp [ops, borrowGuard, borrowHead, Follows, Op.row,
        Op.effect, next, state_simp_rules, hpc, h9, BitVec.add_assoc]
    refine ⟨ops.length, t, block_run base ops s hc he ha follow,
      scan_frame base ops s (by cases right <;> decide),
      scan_zero base ops s (by cases right <;> decide), ?_, ?_⟩
    · simp [significantCount]
    · cases right <;> simp [t, ops, borrowGuard, borrowExit, block,
        Op.effect, next, state_simp_rules, h9, significantCount]
  | succ n ih =>
    intro s hn hc he ha hp hptr h9 hs hm
    have h9' : r (.GPR 9#5) s = BitVec.ofNat 64 n := by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_sub_cancel] using h9
    obtain ⟨hv, hvf, hv0, hv8, hv9, hvp⟩ :=
      borrow_round s base pointer words n right hc he ha hp hptr (by omega) h9' hs hm
    let v := borrowRoundState s base (words[n]?.getD 0#64) right
    change run 13 s = v at hv
    change NatCompare.Frame s v at hvf
    change r (.GPR 0#5) v = r (.GPR 0#5) s at hv0
    change r (.GPR 8#5) v = BitVec.ofNat 64 n at hv8
    change r (.GPR 9#5) v = BitVec.ofNat 64 n - 1#64 at hv9
    change read_pc v = base + BitVec.ofNat 64
      (if words[n]?.getD 0#64 = 0#64 then borrowHead right else borrowExit right (n+1)) at hvp
    have hsucc : significantCount words (n + 1) =
        if words[n]?.getD 0#64 = 0#64 then significantCount words n else n + 1 := rfl
    by_cases zero : words[n]?.getD 0#64 = 0#64
    · have hvp' : read_pc v = base + BitVec.ofNat 64 (borrowHead right) := by
        simpa only [zero, ↓reduceIte] using hvp
      have hvptr : r (.GPR (borrowPointer right)) v = pointer := by
        exact (hvf.registers _ (by cases right <;> decide)).trans hptr
      obtain ⟨fuel, t, ht, htf, ht0, ht8, htp⟩ := ih v (by omega)
        (scan_code hvf hc) (hvf.error.trans he) (hvf.aligned ha) hvp' hvptr hv9
        (hvf.source _ _ hs) (hvf.words _ _ hs hm)
      refine ⟨13 + fuel, t, ?_, hvf.trans htf, ht0.trans hv0, ?_, ?_⟩
      · rw [run_plus, hv, ht]
      · simpa only [hsucc, zero, ↓reduceIte] using ht8
      · simpa only [hsucc, zero, ↓reduceIte] using htp
    · refine ⟨13, v, hv, hvf, hv0, ?_, ?_⟩
      · simpa only [hsucc, zero, ↓reduceIte, Nat.add_sub_cancel] using fun _ => hv8
      · simpa only [hsucc, zero, ↓reduceIte] using hvp

end SszArm.NatAdd
