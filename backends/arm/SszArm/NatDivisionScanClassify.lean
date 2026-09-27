import SszArm.NatDivisionScanInitial
import SszArm.NatDivisionScanPhysical

namespace SszArm.NatDivision

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The classifier stops at the existing fast-call setup entries or at the
large allocation guard. The wide path has not yet loaded its high word. -/
def LargeClassified (base : BitVec 64) (words : List (BitVec 64)) (t : ArmState) : Prop :=
  if sigWords words < 3 then
    if words.length = 0 then read_pc t = base + 656#64
    else r (.GPR 22#5) t = words[0]?.getD 0#64 ∧
      read_pc t = (if words.length < 2 then base + 620#64 else base + 344#64)
  else read_pc t = base + 168#64 ∧
    r (.GPR 8#5) t = BitVec.ofNat 64 (sigWords words) ∧
    r (.GPR 22#5) t = BitVec.ofNat 64 (sigWords words + 1) ∧
    r (.GPR 23#5) t = BitVec.ofNat 64 (8 * (sigWords words - 1)) ∧
    r (.GPR 24#5) t = 8#64

private theorem classification_frame (s : ArmState) (base : BitVec 64) (op : Op)
    (hop : op ∈ [.p32, .p328, .p332, .p336, .p340]) : ScanFrame s (op.effect base s) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor
    · exact Op.program _ _ _
    · exact Op.error _ _ _
    · intro reg hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (disch := simp_all) [Op.effect, put, next, state_simp_rules]
    · intro reg; exact Op.sfp _ _ _ _
    · intro a ha; simp [Op.effect, put, next, state_simp_rules]

private theorem fast_classification (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 332#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (hn : 0 < words.length) (hs : NatCompare.Source s pointer words)
    (hm : NatCompare.Words s pointer words) :
    ∃ t, run 3 s = t ∧ ScanFrame s t ∧
      r (.GPR 22#5) t = words[0]?.getD 0#64 ∧
      read_pc t = (if words.length < 2 then base + 620#64 else base + 344#64) := by
  have hb : words.length < 2^64 := by have := hs.2.1; omega
  have hword : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
    have h := hm ⟨0, hn⟩
    simpa [List.getElem?_eq_getElem hn] using h
  let ops : List Op := [.p332, .p336, .p340]
  let t := block base ops s
  have hpc : r .PC s = base + 332#64 := hp
  have hf : Follows base ops s := by
    simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  have hframe : ScanFrame s t :=
    (classification_frame s base .p332 (by decide)).trans
      ((classification_frame (Op.p332.effect base s) base .p336 (by decide)).trans
        (classification_frame (Op.p336.effect base (Op.p332.effect base s)) base .p340 (by decide)))
  have hcarry : (AddWithCarry (BitVec.ofNat 64 words.length) (~~~2#64) 1#1).2.c = 1#1 ↔
      2 ≤ words.length := by
    rw [Udivti3.cmp_carry]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  change (AddWithCarry (BitVec.ofNat 64 words.length) 18446744073709551613#64 1#1).2.c = 1#1 ↔
    2 ≤ words.length at hcarry
  refine ⟨t, block_run base ops s hc he ha hf, hframe, ?_, ?_⟩
  · simp [t, ops, block, Op.effect, put, next, state_simp_rules, h1, hword]
  · by_cases hl : words.length < 2
    · simp [t, ops, block, Op.effect, put, next, state_simp_rules, h2, hcarry,
        hl, show ¬ 2 ≤ words.length by omega]
    · simp [t, ops, block, Op.effect, put, next, state_simp_rules, h2, hcarry,
        hl, show 2 ≤ words.length by omega]

/-- All physical Large representations, including empty and redundant-zero
ones, are classified by both real native scans. -/
theorem classify_large (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 36#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ LargeClassified base words t := by
  obtain ⟨fuel, u, hu, huf, hup, hu8⟩ := initial_scan s base pointer words
    hc he ha hp h1 h2 hs hm
  have hus := huf.source pointer words hs
  have hum := huf.words pointer words hs hm
  have hu1 := (huf.registers 1#5 (by decide)).trans h1
  have hu2 := (huf.registers 2#5 (by decide)).trans h2
  by_cases hsmall : sigWords words < 3
  · by_cases hempty : words.length = 0
    · have hz : sigWords words = 0 := by have := sigWords_le_length words; omega
      have hup' : read_pc u = base + 328#64 := by simpa [hz] using hup
      let t := Op.p328.effect base u
      have ht : run 1 u = t := by
        change stepi u = t
        exact step u base .p328 (huf.code hc) hup' (huf.error.trans he) (huf.aligned ha)
      refine ⟨fuel + 1, t, ?_, huf.trans (classification_frame u base .p328 (by decide)), ?_⟩
      · rw [run_plus, hu, ht]
      · simp [LargeClassified, hsmall, hempty, t, Op.effect, state_simp_rules, hu2]
    · have hpositive : 0 < words.length := by omega
      have hbound : words.length < 2^64 := by have := hs.2.1; omega
      have hnonzero : BitVec.ofNat 64 words.length ≠ 0#64 := by bv_omega
      have start : ∃ extra v, run extra u = v ∧ ScanFrame u v ∧ read_pc v = base + 332#64 := by
        by_cases hz : sigWords words = 0
        · have hup' : read_pc u = base + 328#64 := by simpa [hz] using hup
          let v := Op.p328.effect base u
          have hv : run 1 u = v := by
            change stepi u = v
            exact step u base .p328 (huf.code hc) hup' (huf.error.trans he) (huf.aligned ha)
          refine ⟨1, v, hv, classification_frame u base .p328 (by decide), ?_⟩
          simp [v, Op.effect, state_simp_rules, hu2, hnonzero]
        · exact ⟨0, u, rfl, ScanFrame.refl u, by simpa [hz, hsmall] using hup⟩
      obtain ⟨extra, v, hv, hvf, hvp⟩ := start
      have hsf := huf.trans hvf
      obtain ⟨t, ht, htf, ht22, htp⟩ := fast_classification v base pointer words
        (hsf.code hc) (hsf.error.trans he) (hsf.aligned ha) hvp
        ((hsf.registers 1#5 (by decide)).trans h1)
        ((hsf.registers 2#5 (by decide)).trans h2) hpositive
        (hsf.source _ _ hs) (hsf.words _ _ hs hm)
      refine ⟨fuel + extra + 3, t, ?_, hsf.trans htf, ?_⟩
      · rw [run_plus, run_plus, hu, hv, ht]
      · simpa [LargeClassified, hsmall, hempty] using And.intro ht22 htp
  · have hz : sigWords words ≠ 0 := by omega
    have hup' : read_pc u = base + 104#64 := by simpa [hz, hsmall] using hup
    obtain ⟨extra, t, ht, htf, ht8, ht22, ht23, ht24, htp⟩ :=
      physical_scan_entry u base pointer words (huf.code hc) (huf.error.trans he)
        (huf.aligned ha) hup' hu1 hu2 hus hum
    refine ⟨fuel + extra, t, ?_, huf.trans htf, ?_⟩
    · rw [run_plus, hu, ht]
    · simp only [LargeClassified, hsmall, ↓reduceIte]
      exact ⟨by simpa only [show significantCount words words.length ≠ 0 from hz, ↓reduceIte] using htp,
        ht8, ht22, ht23 hz, ht24⟩

/-- The complete post-prologue classifier. The operand relation retains the
original pointer/payload and physical limb list; Small is a singleton word.
All essential input, divisor, output, arena, stack and link registers survive. -/
theorem classify_operand (s : ArmState) (base : BitVec 64) (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 32#64)
    (input : NatCompare.Operand s (r (.GPR 1#5) s) (r (.GPR 2#5) s) words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
      (if r (.GPR 1#5) s = 0#64 then read_pc t = base + 300#64
       else LargeClassified base words t) := by
  let u := Op.p32.effect base s
  have hu : run 1 s = u := by
    change stepi s = u
    exact step s base .p32 hc hp he ha
  have huf := classification_frame s base .p32 (by decide)
  by_cases hz : r (.GPR 1#5) s = 0#64
  · refine ⟨1, u, hu, huf, ?_⟩
    simp [hz, u, Op.effect, state_simp_rules]
  · obtain ⟨hlen, hs, hm⟩ := input.large hz
    have h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length := by
      rw [← hlen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hup : read_pc u = base + 36#64 := by simp [u, Op.effect, state_simp_rules, hz]
    obtain ⟨fuel, t, ht, htf, classified⟩ := classify_large u base (r (.GPR 1#5) s) words
      (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup
      (huf.registers 1#5 (by decide)) ((huf.registers 2#5 (by decide)).trans h2)
      (huf.source _ _ hs) (huf.words _ _ hs hm)
    refine ⟨1 + fuel, t, ?_, huf.trans htf, ?_⟩
    · rw [run_plus, hu, ht]
    · simpa [hz] using classified

end SszArm.NatDivision
