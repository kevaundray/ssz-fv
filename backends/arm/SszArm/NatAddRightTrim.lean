import SszArm.NatAddTrim

namespace SszArm.NatAdd

open UintCodec SszNative.Limbs
open NatCompare (Source Words saved)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def rightRoundState (s : ArmState) (base word : BitVec 64) : ArmState :=
  block base [.p348, .p352, .p356]
    (loadResult (block base [.p308, .p312] s) base .trimRight word)

/-- The right scan uses an all-ones sentinel, not a signed-length test. -/
theorem right_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 308#64)
    (h3 : r (.GPR 3#5) s = pointer)
    (hn : n < words.length)
    (h11 : r (.GPR 11#5) s = BitVec.ofNat 64 n)
    (hs : Source s pointer words) (hm : Words s pointer words) :
    let t := rightRoundState s base (words[n]?.getD 0#64)
    run 13 s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 n ∧
      r (.GPR 11#5) t = BitVec.ofNat 64 n - 1#64 ∧
      read_pc t = base + (if words[n]?.getD 0#64 = 0#64 then 308#64 else 360#64) := by
  have notLast : BitVec.ofNat 64 n + 1#64 ≠ 0#64 := by have := hs.2.1; bv_omega
  let u := block base [.p308, .p312] s
  have hpc : r .PC s = base + 308#64 := hp
  have hu : run 2 s = u := block_run base [.p308, .p312] s hc he ha (by
    simp [Follows, Op.row, Op.effect, next, state_simp_rules, hpc,
      h11, notLast, BitVec.add_assoc])
  have huf : NatCompare.Frame s u := scan_frame base _ s (by decide)
  have hup : read_pc u = base + 316#64 := by
    simp [u, block, Op.effect, next, state_simp_rules, h11, notLast]
  have hus : Source u pointer words := huf.source _ _ hs
  have hum : Words u pointer words := huf.words _ _ hs hm
  have hload : read_mem_bytes 8
      (r (.GPR LoadKind.trimRight.ptr) u + (r (.GPR LoadKind.trimRight.index) u <<< 3))
      (saved u LoadKind.trimRight.tmp) = words[n]?.getD 0#64 := by
    have hl := NatCompare.limb_load u pointer words n 9#5 hn hus hum
    simpa [u, block, Op.effect, next, state_simp_rules, h3, h11,
      LoadKind.ptr, LoadKind.index, LoadKind.tmp] using hl
  let v := loadResult u base .trimRight (words[n]?.getD 0#64)
  have hv : run 8 u = v := load_run u base _ .trimRight (scan_code huf hc)
    (huf.error.trans he) (huf.aligned ha) hup hus.1 hload
  have hvf : NatCompare.Frame s v := huf.trans
    (load_compare_frame u base _ .trimRight hus.1 (by decide))
  have follow : Follows base [.p348, .p352, .p356] v := by
    simp [v, loadResult, LoadKind.start, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, BitVec.add_assoc]
  have ht := block_run base [.p348, .p352, .p356] v (scan_code hvf hc)
    (hvf.error.trans he) (hvf.aligned ha) follow
  have htf : NatCompare.Frame v (block base [.p348, .p352, .p356] v) :=
    scan_frame base _ _ (by decide)
  refine ⟨?_, hvf.trans htf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 13 = 2 + 8 + 3 by decide, run_plus, run_plus, hu, hv]
    exact ht
  all_goals
    by_cases zero : words[n]?.getD 0#64 = 0#64 <;>
      simp_all (config := {decide := true, instances := true})
        [rightRoundState, u, v, loadResult, LoadKind.start, LoadKind.dst,
          LoadKind.tmp, block, Op.effect, put, next, saved, state_simp_rules]

/-- Complete right significant-count scan without canonical-input assumptions. -/
theorem right_trim (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
    CodeAt s base → read_err s = .None → CheckSPAlignment s →
    read_pc s = base + 308#64 →
    r (.GPR 3#5) s = pointer →
    r (.GPR 11#5) s = BitVec.ofNat 64 n - 1#64 →
    Source s pointer words → Words s pointer words →
    ∃ fuel t, run fuel s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      (significantCount words n ≠ 0 →
        r (.GPR 10#5) t = BitVec.ofNat 64 (significantCount words n - 1)) ∧
      read_pc t = base + (if significantCount words n = 0 then 408#64 else 360#64) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h3 h11 hs hm
    let ops : List Op := [.p308, .p312]
    let t := block base ops s
    have hpc : r .PC s = base + 308#64 := hp
    have follow : Follows base ops s := by
      simp [ops, Follows, Op.row, Op.effect, next, state_simp_rules,
        hpc, h11, BitVec.add_assoc]
    refine ⟨2, t, block_run base ops s hc he ha follow,
      scan_frame base ops s (by decide), scan_zero base ops s (by decide), ?_, ?_, ?_, ?_⟩
    all_goals simp [t, ops, block, Op.effect, next, state_simp_rules, h11, significantCount]
  | succ n ih =>
    intro s hn hc he ha hp h3 h11 hs hm
    have h11' : r (.GPR 11#5) s = BitVec.ofNat 64 n := by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_sub_cancel] using h11
    obtain ⟨hv, hvf, hv0, hv8, hv9, hv10, hv11, hvp⟩ :=
      right_round s base pointer words n hc he ha hp h3 (by omega) h11' hs hm
    let v := rightRoundState s base (words[n]?.getD 0#64)
    change run 13 s = v at hv
    change NatCompare.Frame s v at hvf
    change r (.GPR 0#5) v = r (.GPR 0#5) s at hv0
    change r (.GPR 8#5) v = r (.GPR 8#5) s at hv8
    change r (.GPR 9#5) v = r (.GPR 9#5) s at hv9
    change r (.GPR 10#5) v = BitVec.ofNat 64 n at hv10
    change r (.GPR 11#5) v = BitVec.ofNat 64 n - 1#64 at hv11
    change read_pc v = base + (if words[n]?.getD 0#64 = 0#64 then 308#64 else 360#64) at hvp
    have hsucc : significantCount words (n + 1) =
        if words[n]?.getD 0#64 = 0#64 then significantCount words n else n + 1 := rfl
    by_cases zero : words[n]?.getD 0#64 = 0#64
    · have hvp' : read_pc v = base + 308#64 := by simpa only [zero, ↓reduceIte] using hvp
      obtain ⟨fuel, t, ht, htf, ht0, ht8, ht9, ht10, htp⟩ := ih v (by omega)
        (scan_code hvf hc) (hvf.error.trans he) (hvf.aligned ha) hvp'
        ((hvf.registers 3#5 (by decide)).trans h3) hv11
        (hvf.source _ _ hs) (hvf.words _ _ hs hm)
      refine ⟨13 + fuel, t, ?_, hvf.trans htf, ht0.trans hv0, ht8.trans hv8,
        ht9.trans hv9, ?_, ?_⟩
      · rw [run_plus, hv, ht]
      · simpa only [hsucc, zero, ↓reduceIte] using ht10
      · simpa only [hsucc, zero, ↓reduceIte] using htp
    · refine ⟨13, v, hv, hvf, hv0, hv8, hv9, ?_, ?_⟩
      · simpa only [hsucc, zero, ↓reduceIte, Nat.add_sub_cancel] using fun _ => hv10
      · simpa [hsucc, zero] using hvp

end SszArm.NatAdd
