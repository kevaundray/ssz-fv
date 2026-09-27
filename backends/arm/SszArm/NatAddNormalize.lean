import SszArm.NatAddNormalizeScan

namespace SszArm.NatAdd.Normalize

open UintCodec SszNative SszNative.Limbs
open NatCompare (Words)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem Frame.compare {s t : ArmState} (frame : Frame s t) : NatCompare.Frame s t := by
  refine ⟨frame.program, frame.error, ?_, frame.vectors, ?_⟩
  · intro reg hr
    apply frame.registers reg
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
    tauto
  · intro a ha
    exact congrFun frame.memory a

/-- Once a nonzero high word is found, the actual CMP/CSEL pair produces precisely
native fromWords' Small-or-Large ABI pair. The following pair store belongs to
the shared return tail. -/
theorem select_run (s : ArmState) (base pointer : BitVec 64) (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 2068#64)
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 (sigWords words))
    (h9 : r (.GPR 9#5) s = pointer)
    (h11 : r (.GPR 11#5) s = words[0]?.getD 0#64)
    (nonzero : sigWords words ≠ 0) (bound : words.length < 2^64) :
    let t := block base [.p2068, .p2072, .p2076] s
    run 3 s = t ∧ NatCompare.Frame s t ∧ t.mem = s.mem ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧ read_pc t = base + 2080#64 ∧
      r (.GPR 9#5) t = (NatOperand.fromWords pointer words).pointer ∧
      r (.GPR 8#5) t = (NatOperand.fromWords pointer words).payload := by
  have countBound := sigWords_le_length words
  have compare : (AddWithCarry (BitVec.ofNat 64 (sigWords words)) (~~~(1#64)) 1#1).2.z = 1#1 ↔
      sigWords words ≤ 1 := by
    rw [Udivti3.cmp_zero]
    bv_omega
  have hpc : r .PC s = base + 2068#64 := hp
  have follows : Follows base [.p2068, .p2072, .p2076] s := by
    simp [Follows, Op.row, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, hpc, BitVec.add_assoc]
  refine ⟨block_run base _ s hc he ha follows, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · simp
    · simp
    · intro reg hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (disch := simp_all) [block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules]
    · intro reg
      simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
    · intro a ha
      simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  · simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  · simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
  · simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, hpc, BitVec.add_assoc]
  · simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, h8, h9, compare, NatOperand.fromWords_pointer]
  · simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, h8, h11, compare, NatOperand.fromWords_payload]

/-- The complete output normalization prelude and backward scan. The nonzero
path hands the exact canonical fromWords pair to +2080; the all-zero path hands
control to +2128. No output bytes or input bytes are changed by this phase. -/
theorem normalize_run (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (count : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 2044#64)
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 count)
    (h9 : r (.GPR 9#5) s = pointer) (h10 : r (.GPR 10#5) s = pointer)
    (h11 : r (.GPR 11#5) s = words[0]?.getD 0#64)
    (length : words.length = count + 1) (bound : words.length + 1 < 2^64)
    (hm : Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ NatCompare.Frame s t ∧ t.mem = s.mem ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      read_pc t = base + (if sigWords words = 0 then 2128#64 else 2080#64) ∧
      (sigWords words ≠ 0 →
        r (.GPR 9#5) t = (NatOperand.fromWords pointer words).pointer ∧
        r (.GPR 8#5) t = (NatOperand.fromWords pointer words).payload) ∧
      Words t pointer words := by
  let v := block base [.p2044, .p2048] s
  have hpc : r .PC s = base + 2044#64 := hp
  have runPrelude : run 2 s = v := block_run base _ s hc he ha (by
    simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc])
  have vf : Frame s v := scan_frame base _ s (by decide)
  have vp : read_pc v = base + 2052#64 := by
    simp [v, block, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  have v8 : r (.GPR 8#5) v = BitVec.ofNat 64 (words.length + 1) := by
    simp [v, block, Op.effect, put, next, state_simp_rules, h8, length, BitVec.ofNat_add]
  have v10 : r (.GPR 10#5) v = pointer + BitVec.ofNat 64 (8 * words.length) - 8#64 := by
    simp only [v, block, List.foldl_cons, List.foldl_nil, Op.effect, put, next,
      state_simp_rules, h8, h10, length]
    bv_omega
  obtain ⟨fuel, u, runScan, scanFrame, count8, scanPC⟩ := scan_run base pointer words bound
    words.length v (by omega) (vf.code hc) (vf.error.trans he) (vf.aligned ha)
    vp v8 v10 (vf.words _ _ hm)
  have frame := vf.trans scanFrame
  change r (.GPR 8#5) u = BitVec.ofNat 64 (sigWords words) at count8
  change read_pc u = base + (if sigWords words = 0 then 2128#64 else 2068#64) at scanPC
  by_cases zero : sigWords words = 0
  · refine ⟨2 + fuel, u, ?_, frame.compare, frame.memory,
      frame.registers _ (by decide), ?_, fun h => False.elim (h zero), frame.words _ _ hm⟩
    · rw [run_plus, runPrelude, runScan]
    · simpa only [zero, ↓reduceIte] using scanPC
  · have up : read_pc u = base + 2068#64 := by simpa only [zero, ↓reduceIte] using scanPC
    obtain ⟨runSelect, selectFrame, selectMemory, select0, selectPC, select9, select8⟩ :=
      select_run u base pointer words (frame.code hc) (frame.error.trans he)
        (frame.aligned ha) up count8 ((frame.registers _ (by decide)).trans h9)
        ((frame.registers _ (by decide)).trans h11) zero (by omega)
    let t := block base [.p2068, .p2072, .p2076] u
    refine ⟨2 + fuel + 3, t, ?_, frame.compare.trans selectFrame,
      selectMemory.trans frame.memory,
      select0.trans (frame.registers _ (by decide)), ?_, fun _ => ⟨select9, select8⟩, ?_⟩
    · rw [run_plus, run_plus, runPrelude, runScan, runSelect]
    · simpa only [zero, ↓reduceIte] using selectPC
    · intro i
      rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp (selectMemory.trans frame.memory)]
      exact hm i

end SszArm.NatAdd.Normalize
