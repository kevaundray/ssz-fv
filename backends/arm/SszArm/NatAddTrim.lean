import SszArm.NatAddTrimState

namespace SszArm.NatAdd

open UintCodec SszNative.Limbs
open NatCompare (Source Words saved)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- One descending scan round of the actual input representation. -/
theorem left_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 12#64)
    (h8 : r (.GPR 8#5) s = pointer - 8#64)
    (hn : n < words.length)
    (h10 : r (.GPR 10#5) s = BitVec.ofNat 64 (n + 1))
    (hs : Source s pointer words) (hm : Words s pointer words) :
    let t := leftRoundState s base (words[n]?.getD 0#64)
    run 12 s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 (n + 1) ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 n ∧
      read_pc t = base + (if words[n]?.getD 0#64 = 0#64 then 12#64 else 60#64) := by
  have hlen : words.length < 2^64 := by have := hs.2.1; omega
  have nonzero : BitVec.ofNat 64 (n + 1) ≠ 0#64 := by bv_omega
  let u := block base [.p12, .p16] s
  have hpc : r .PC s = base + 12#64 := hp
  have hu : run 2 s = u := block_run base [.p12, .p16] s hc he ha (by
    simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc,
      h10, BitVec.add_assoc])
  have huf : NatCompare.Frame s u := scan_frame base _ s (by decide)
  have hup : read_pc u = base + 20#64 := by
    simp [u, block, Op.effect, put, next, state_simp_rules, h10, nonzero]
  have hu8 : r (.GPR 8#5) u = pointer - 8#64 := by
    simpa [u, block, Op.effect, put, next, state_simp_rules] using h8
  have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 (n + 1) := by
    simp [u, block, Op.effect, put, next, state_simp_rules, h10]
  have hus : Source u pointer words := huf.source _ _ hs
  have hum : Words u pointer words := huf.words _ _ hs hm
  have haddress : pointer - 8#64 + (BitVec.ofNat 64 (n + 1) <<< 3) =
      pointer + (BitVec.ofNat 64 n <<< 3) := trim_predecessor_address pointer n
  have hload : read_mem_bytes 8
      (r (.GPR LoadKind.trimLeft.ptr) u + (r (.GPR LoadKind.trimLeft.index) u <<< 3))
      (saved u LoadKind.trimLeft.tmp) = words[n]?.getD 0#64 := by
    simp only [LoadKind.ptr, LoadKind.index, hu8, hu9, haddress]
    exact NatCompare.limb_load u pointer words n _ hn hus hum
  let v := loadResult u base .trimLeft (words[n]?.getD 0#64)
  have hv : run 8 u = v := load_run u base _ .trimLeft (scan_code huf hc)
    (huf.error.trans he) (huf.aligned ha) hup hus.1 hload
  have hvf : NatCompare.Frame s v := huf.trans
    (load_compare_frame u base _ .trimLeft hus.1 (by decide))
  have follow : Follows base [.p52, .p56] v := by
    simp [v, loadResult, LoadKind.start, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, BitVec.add_assoc]
  have ht := block_run base [.p52, .p56] v (scan_code hvf hc)
    (hvf.error.trans he) (hvf.aligned ha) follow
  have htf : NatCompare.Frame v (block base [.p52, .p56] v) :=
    scan_frame base _ _ (by decide)
  refine ⟨?_, hvf.trans htf, left_round_fields s base _ n h10⟩
  · rw [show 12 = 2 + 8 + 2 by decide, run_plus, run_plus, hu, hv]
    exact ht

/-- The left significant-count loop, with empty and redundant-zero Large inputs.
The original payload is never replaced by the significant count. -/
theorem left_trim (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
    CodeAt s base → read_err s = .None → CheckSPAlignment s →
    read_pc s = base + 12#64 →
    r (.GPR 8#5) s = pointer - 8#64 →
    r (.GPR 10#5) s = BitVec.ofNat 64 n →
    Source s pointer words → Words s pointer words →
    ∃ fuel t, run fuel s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 (significantCount words n) ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 (significantCount words n) ∧
      read_pc t = base + (if significantCount words n = 0 then 92#64 else 64#64) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h8 h10 hs hm
    let ops : List Op := [.p12, .p16, .p88]
    let t := block base ops s
    have hpc : r .PC s = base + 12#64 := hp
    have follow : Follows base ops s := by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
        hpc, h10, BitVec.add_assoc]
    refine ⟨3, t, block_run base ops s hc he ha follow,
      scan_frame base ops s (by decide), scan_zero base ops s (by decide), ?_, ?_, ?_⟩
    all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules,
      h10, significantCount, BitVec.add_assoc]
  | succ n ih =>
    intro s hn hc he ha hp h8 h10 hs hm
    obtain ⟨hv, hvf, hv0, hv8, hv9, hv10, hvp⟩ :=
      left_round s base pointer words n hc he ha hp h8 (by omega) h10 hs hm
    let v := leftRoundState s base (words[n]?.getD 0#64)
    change run 12 s = v at hv
    change NatCompare.Frame s v at hvf
    change r (.GPR 0#5) v = r (.GPR 0#5) s at hv0
    change r (.GPR 8#5) v = r (.GPR 8#5) s at hv8
    change r (.GPR 9#5) v = BitVec.ofNat 64 (n + 1) at hv9
    change r (.GPR 10#5) v = BitVec.ofNat 64 n at hv10
    change read_pc v = base + (if words[n]?.getD 0#64 = 0#64 then 12#64 else 60#64) at hvp
    have hsucc : significantCount words (n + 1) =
        if words[n]?.getD 0#64 = 0#64 then significantCount words n else n + 1 := rfl
    by_cases zero : words[n]?.getD 0#64 = 0#64
    · have hvp' : read_pc v = base + 12#64 := by simpa only [zero, ↓reduceIte] using hvp
      obtain ⟨fuel, t, ht, htf, ht0, ht8, ht9, htp⟩ := ih v (by omega)
        (scan_code hvf hc) (hvf.error.trans he) (hvf.aligned ha) hvp'
        (hv8.trans h8) hv10 (hvf.source _ _ hs) (hvf.words _ _ hs hm)
      refine ⟨12 + fuel, t, ?_, hvf.trans htf, ht0.trans hv0, ?_, ?_, ?_⟩
      · rw [run_plus, hv, ht]
      · simpa only [hsucc, zero, ↓reduceIte] using ht8
      · simpa only [hsucc, zero, ↓reduceIte] using ht9
      · simpa only [hsucc, zero, ↓reduceIte] using htp
    · let t := Op.p60.effect base v
      have hlast : read_pc v = base + 60#64 := by simpa only [zero, ↓reduceIte] using hvp
      have hlastPC : r .PC v = base + 60#64 := hlast
      have ht : run 1 v = t := by
        change stepi v = t
        exact step v base .p60 (scan_code hvf hc) hlast (hvf.error.trans he) (hvf.aligned ha)
      have htf : NatCompare.Frame v t := scan_frame base [.p60] v (by decide)
      refine ⟨13, t, ?_, hvf.trans htf, ?_, ?_, ?_, ?_⟩
      · rw [show 13 = 12 + 1 by decide, run_plus, hv, ht]
      · exact (scan_zero base [.p60] v (by decide)).trans hv0
      · simp [t, Op.effect, put, next, state_simp_rules, hv10, hsucc, zero,
          BitVec.ofNat_add]
      · simp [t, Op.effect, put, next, state_simp_rules, hv9, hsucc, zero]
      · simp [t, Op.effect, put, next, state_simp_rules, hlastPC, read_pc,
          hsucc, zero, BitVec.add_assoc]

end SszArm.NatAdd
