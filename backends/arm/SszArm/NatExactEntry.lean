import SszArm.NatExactScan

namespace SszArm.NatExact

open UintCodec (widthLoad)
open Delimited (Protected MemoryFrame)
open SszNative SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The comparison has selected its actual native continuation. -/
def Ready (s : ArmState) (base : BitVec 64) (expected : NatOperand) : Prop :=
  if NatNarrow.runExact expected (r (.GPR 2#5) s) then
    read_pc s = base + 272#64 ∧ r (.GPR 8#5) s = 0#64
  else read_pc s = base + 124#64

theorem frame_owned {s t : ArmState} {expected : NatOperand}
    (owned : Owned s expected) (frame : SszArm.NatNarrow.Frame s t) : Owned t expected := by
  have r0 := frame.registers 0#5 (by decide)
  have r1 := frame.registers 1#5 (by decide)
  have writes : localWrites t = localWrites s := by simp only [localWrites, r0, frame.sp]
  have mem := frame.memoryFrame (localWrites s) (by simp [localWrites]) owned.stackBound
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r1]
    refine ⟨?_, ?_, NatDivision.operand_at_preserved mem expected
      owned.expectedAt.2.2 owned.operandOwned⟩
    · rw [mem.load _ 8 (by have := owned.expectedBound; omega)
        (by simpa only [Nat.add_zero] using owned.expectedOwned.subspan 0 8 (by decide))]
      exact owned.expectedAt.1
    · rw [mem.load _ 8 (by have := owned.expectedBound; omega)
        (owned.expectedOwned.subspan 8 8 (by decide))]
      exact owned.expectedAt.2.1
  · simpa only [r1] using owned.expectedBound
  · simpa only [writes, r1] using owned.expectedOwned
  · simpa only [writes] using owned.operandOwned
  · simpa only [r0] using owned.outputBound
  · simpa only [frame.sp] using owned.stackBound
  · simpa only [r0, frame.sp] using owned.outputStack

theorem comparison_zero (expected : NatOperand) (actual low high : BitVec 64)
    (fits : expected.wordCount ≤ 2)
    (first : low = expected.words[0]?.getD 0)
    (second : high = expected.words[1]?.getD 0) :
    ((low ^^^ actual) ||| high = 0#64) ↔ NatNarrow.runExact expected actual = true := by
  have native := SszNative.NatDivision.wideValue_native expected fits
  rw [← first, ← second] at native
  have joined : SszNative.NatDivision.wideValue expected = high ++ low := by
    rw [native]
    change (low.setWidth 128 ||| (high.setWidth 128 <<< (64 : Nat))) = high ++ low
    have h := BitVec.setWidth_append_eq_shiftLeft_setWidth_or
      (b := high) (b' := low) (w'' := 128)
    simpa only [BitVec.setWidth_eq, BitVec.or_comm] using h.symm
  have appendNat : (high ++ low).toNat = 2^64 * high.toNat + low.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt high.toNat,
      Nat.shiftLeft_eq, Nat.mul_comm]
  have equal : high ++ low = actual.setWidth 128 ↔ low = actual ∧ high = 0#64 := by
    constructor
    · intro h
      have numbers := congrArg BitVec.toNat h
      rw [appendNat, BitVec.toNat_setWidth_of_le (by decide)] at numbers
      constructor <;> bv_omega
    · rintro ⟨lo, hi⟩
      apply BitVec.eq_of_toNat_eq
      rw [appendNat, BitVec.toNat_setWidth_of_le (by decide), lo, hi]
      simp
  simp only [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff,
    NatNarrow.runExact, NatNarrow.toU128, fits, ↓reduceIte, decide_eq_true_eq, joined, equal]

/-- The final XOR/OR comparison is shared by Small and physically loaded Large. -/
theorem compare_finish (s : ArmState) (base : BitVec 64) (expected : NatOperand)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 112#64)
    (fits : expected.wordCount ≤ 2)
    (first : r (.GPR 8#5) s = expected.words[0]?.getD 0)
    (second : r (.GPR 9#5) s = expected.words[1]?.getD 0) :
    ∃ fuel t, run fuel s = t ∧ SszArm.NatNarrow.Frame s t ∧ Ready t base expected := by
  let ops : List Op := [.p112, .p116, .p120]
  let t := block base ops s
  have zero := comparison_zero expected (r (.GPR 2#5) s) _ _ fits first second
  have hpc : r .PC s = base + 112#64 := hp
  have follows : Follows base ops s := by
    simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  refine ⟨3, t, block_run base ops s hc he ha follows,
    scan_pure_frame base ops s (by decide), ?_⟩
  by_cases accepted : NatNarrow.runExact expected (r (.GPR 2#5) s) = true
  · have z := zero.mpr accepted
    simp [Ready, t, ops, block, Op.effect, put, next, state_simp_rules,
      hpc, z, accepted, BitVec.add_assoc]
  · have z : (r (.GPR 8#5) s ^^^ r (.GPR 2#5) s) ||| r (.GPR 9#5) s ≠ 0#64 :=
      fun h => accepted (zero.mp h)
    simp [Ready, t, ops, block, Op.effect, put, next, state_simp_rules,
      hpc, z, accepted, BitVec.add_assoc]

/-- Loads are bounded by physical length, never by significant length. -/
theorem borrowed_compare (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (owned : Owned s (.large pointer words))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 84#64) (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 words.length)
    (h9 : r (.GPR 9#5) s = pointer) (nonempty : 0 < words.length)
    (fits : (NatOperand.large pointer words).wordCount ≤ 2) :
    ∃ fuel t, run fuel s = t ∧ SszArm.NatNarrow.Frame s t ∧ Ready t base (.large pointer words) := by
  have physical := owned.expectedAt.2.2.2.2.1
  have lengthBound : words.length < 2^64 := by omega
  have stored := owned.large_words
  have first : read_mem_bytes 8 pointer s = words[0]?.getD 0 := by
    simpa [List.getElem?_eq_getElem nonempty] using stored ⟨0, nonempty⟩
  let ops : List Op := [.p84, .p88, .p92] ++
    (if words.length < 2 then [.p104] else [.p96, .p100]) ++ [.p108]
  let u := block base ops s
  have hpc : r .PC s = base + 84#64 := hp
  have low : r (.GPR 8#5) u = words[0]?.getD 0 := by
    by_cases short : words.length < 2 <;>
      simp [u, ops, short, block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
        state_simp_rules, h9, first]
  have high : r (.GPR 9#5) u = words[1]?.getD 0 := by
    by_cases short : words.length < 2
    · have absent : words[1]? = none := List.getElem?_eq_none (by omega)
      simp [u, ops, short, block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
        state_simp_rules, absent]
    · have second : read_mem_bytes 8 (pointer + 8#64) s = words[1]?.getD 0 := by
        simpa [List.getElem?_eq_getElem (show 1 < words.length by omega)] using stored ⟨1, by omega⟩
      simp [u, ops, short, block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
        state_simp_rules, h9, second]
  have carry : (AddWithCarry (BitVec.ofNat 64 words.length) (~~~2#64) 1#1).2.c = 1#1 ↔
      2 ≤ words.length := by
    rw [Udivti3.cmp_carry]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthBound]
  change (AddWithCarry (BitVec.ofNat 64 words.length) 18446744073709551613#64 1#1).2.c = 1#1 ↔
    2 ≤ words.length at carry
  have follows : Follows base ops s := by
    by_cases short : words.length < 2 <;>
      simp [ops, short, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
        Udivti3.next, state_simp_rules, hpc, h8, BitVec.add_assoc, carry] <;> omega
  have uf := scan_pure_frame base ops s (by
    intro op member
    by_cases short : words.length < 2
    · simp only [ops, short, ↓reduceIte, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with ((rfl | rfl | rfl) | rfl) | rfl <;> decide
    · simp only [ops, short, ↓reduceIte, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with ((rfl | rfl | rfl) | (rfl | rfl)) | rfl <;> decide)
  have up : read_pc u = base + 112#64 := by
    by_cases short : words.length < 2
    · have below : ¬ 2 ≤ words.length := by omega
      simp [u, ops, short, block, Op.effect, put, next, Udivti3.compare,
        Udivti3.next, state_simp_rules, hpc, h8, BitVec.add_assoc, carry, below]
    · simp [u, ops, short, block, Op.effect, put, next, Udivti3.compare,
        Udivti3.next, state_simp_rules, hpc, h8, BitVec.add_assoc, carry]
  obtain ⟨fuel, t, execution, tf, ready⟩ := compare_finish u base (.large pointer words)
    (frame_code uf hc) (uf.error.trans he) (uf.aligned ha) up fits low high
  exact ⟨ops.length + fuel, t, by rw [run_plus, block_run base ops s hc he ha follows, execution],
    uf.trans tf, ready⟩

theorem empty_compare (s : ArmState) (base pointer : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 80#64) (h8 : r (.GPR 8#5) s = 0#64) :
    ∃ fuel t, run fuel s = t ∧ SszArm.NatNarrow.Frame s t ∧
      Ready t base (.large pointer []) := by
  let ops : List Op := [.p80, .p280, .p284, .p288] ++
    if r (.GPR 2#5) s = 0#64 then [.p292] else []
  let t := block base ops s
  have hpc : r .PC s = base + 80#64 := hp
  have zero : NatNarrow.runExact (.large pointer []) (r (.GPR 2#5) s) = true ↔
      r (.GPR 2#5) s = 0#64 := by
    rw [NatNarrow.runExact_iff]
    simp only [NatOperand.value, NatOperand.words, Limbs.value]
    constructor <;> intro h <;> bv_omega
  have follows : Follows base ops s := by
    by_cases equal : r (.GPR 2#5) s = 0#64 <;>
      simp [ops, equal, Follows, Op.row, Op.effect, put, next, state_simp_rules,
        hpc, h8, BitVec.add_assoc]
  refine ⟨ops.length, t, block_run base ops s hc he ha follows,
    scan_pure_frame base ops s (by
      intro op member
      by_cases equal : r (.GPR 2#5) s = 0#64 <;> cases op <;> simp_all [ops, scanPureOps]), ?_⟩
  by_cases equal : r (.GPR 2#5) s = 0#64
  · have accepted : NatNarrow.runExact (.large pointer []) 0#64 = true := by
      simpa only [equal] using zero.mpr equal
    simp [Ready, t, ops, equal, accepted, block, Op.effect, put, next,
      state_simp_rules, hpc, h8, BitVec.add_assoc]
  · have rejected : NatNarrow.runExact (.large pointer []) (r (.GPR 2#5) s) ≠ true :=
      fun h => equal (zero.mp h)
    simp [Ready, t, ops, equal, rejected, block, Op.effect, put, next,
      state_simp_rules, hpc, h8, BitVec.add_assoc]

theorem scanned_compare (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (owned : Owned s (.large pointer words))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + (if sigWords words = 0 then 80#64 else 64#64))
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 words.length)
    (h9 : r (.GPR 9#5) s = pointer)
    (h10 : sigWords words ≠ 0 →
      r (.GPR 10#5) s = BitVec.ofNat 64 (sigWords words - 1)) :
    ∃ fuel t, run fuel s = t ∧ SszArm.NatNarrow.Frame s t ∧
      Ready t base (.large pointer words) := by
  have physical := owned.expectedAt.2.2.2.2.1
  have lengthBound : words.length < 2^64 := by omega
  have sigBound := sigWords_le_length words
  by_cases empty : words = []
  · subst words
    exact empty_compare s base pointer hc he ha (by simpa [sigWords, significantCount] using hp)
      (by simpa using h8)
  have nonempty : 0 < words.length := by cases words <;> simp_all
  by_cases zero : sigWords words = 0
  · let ops : List Op := [.p80]
    let u := block base ops s
    have lengthNonzero : BitVec.ofNat 64 words.length ≠ 0#64 := by bv_omega
    have follows : Follows base ops s := by
      simpa [ops, Follows, Op.row, zero] using hp
    have uf := scan_pure_frame base ops s (by decide)
    have up : read_pc u = base + 84#64 := by
      simp [u, ops, block, Op.effect, h8, lengthNonzero, state_simp_rules]
    obtain ⟨fuel, t, execution, tf, ready⟩ := borrowed_compare u base pointer words
      (frame_owned owned uf) (frame_code uf hc) (uf.error.trans he) (uf.aligned ha)
      up (by simpa [u, ops, block, Op.effect, state_simp_rules] using h8)
      (by simpa [u, ops, block, Op.effect, state_simp_rules] using h9) nonempty
      (by change sigWords words ≤ 2; omega)
    exact ⟨ops.length + fuel, t, by rw [run_plus, block_run base ops s hc he ha follows, execution],
      uf.trans tf, ready⟩
  · have remembered := h10 zero
    have count : BitVec.ofNat 64 (sigWords words - 1) + 1#64 =
        BitVec.ofNat 64 (sigWords words) := by bv_omega
    have countBound : sigWords words < 2^64 := by omega
    have carry : (AddWithCarry (BitVec.ofNat 64 (sigWords words)) (~~~3#64) 1#1).2.c = 1#1 ↔
        3 ≤ sigWords words := by
      rw [Udivti3.cmp_carry]
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound]
    change (AddWithCarry (BitVec.ofNat 64 (sigWords words)) 18446744073709551612#64 1#1).2.c = 1#1 ↔
      3 ≤ sigWords words at carry
    let ops : List Op := [.p64, .p68, .p72] ++
      if sigWords words ≤ 2 then [] else [.p76]
    let u := block base ops s
    have hpc : r .PC s = base + 64#64 := by
      change read_pc s = _
      simpa only [zero, ↓reduceIte] using hp
    have follows : Follows base ops s := by
      by_cases fits : sigWords words ≤ 2 <;>
        simp [ops, fits, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
          Udivti3.next, state_simp_rules, hpc, remembered, count, BitVec.add_assoc,
          carry] <;> omega
    have uf := scan_pure_frame base ops s (by
      intro op member
      by_cases fits : sigWords words ≤ 2 <;> cases op <;> simp_all [ops, scanPureOps])
    by_cases fits : sigWords words ≤ 2
    · have up : read_pc u = base + 84#64 := by
        simp [u, ops, fits, block, Op.effect, put, next, Udivti3.compare,
          Udivti3.next, state_simp_rules, hpc, remembered, count, BitVec.add_assoc,
          carry] <;> omega
      obtain ⟨fuel, t, execution, tf, ready⟩ := borrowed_compare u base pointer words
        (frame_owned owned uf) (frame_code uf hc) (uf.error.trans he) (uf.aligned ha)
        up (by simpa [u, ops, fits, block, Op.effect, put, next, Udivti3.compare,
          Udivti3.next, state_simp_rules] using h8)
        (by simpa [u, ops, fits, block, Op.effect, put, next, Udivti3.compare,
          Udivti3.next, state_simp_rules] using h9) nonempty fits
      exact ⟨ops.length + fuel, t,
        by rw [run_plus, block_run base ops s hc he ha follows, execution], uf.trans tf, ready⟩
    · refine ⟨ops.length, u, block_run base ops s hc he ha follows, uf, ?_⟩
      have rejected : NatNarrow.runExact (.large pointer words) (r (.GPR 2#5) u) = false := by
        simp [NatNarrow.runExact, NatNarrow.toU128, NatOperand.wordCount,
          NatOperand.words, fits]
      simp only [Ready, rejected, Bool.false_eq_true, ↓reduceIte]
      simp [u, ops, fits, block, Op.effect, state_simp_rules]

theorem entry_ready (s : ArmState) (base : BitVec 64) (expected : NatOperand)
    (owned : Owned s expected) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ SszArm.NatNarrow.Frame s t ∧ Ready t base expected := by
  have reads := owned.expected_reads
  have hpc : r .PC s = base := hp
  cases expected with
  | small scalar =>
    let ops : List Op := [.p0, .p4]
    let u := block base ops s
    have follows : Follows base ops s := by
      simp [ops, Follows, Op.row, Op.effect, next, state_simp_rules, hpc, BitVec.add_assoc]
    have uf := scan_pure_frame base ops s (by decide)
    have up : read_pc u = base + 112#64 := by
      simp [u, ops, block, Op.effect, next, state_simp_rules, reads.1, NatOperand.pointer]
    obtain ⟨fuel, t, execution, tf, ready⟩ := compare_finish u base (.small scalar)
      (frame_code uf hc) (uf.error.trans he) (uf.aligned ha) up
      (by
        have h := sigWords_le_length [scalar]
        change sigWords [scalar] ≤ 2
        simpa only [List.length_cons, List.length_nil] using
          (Nat.le_trans h (show [scalar].length ≤ 2 by simp)))
      (by simp [u, ops, block, Op.effect, next, state_simp_rules, reads.2,
        NatOperand.words, NatOperand.payload])
      (by simp [u, ops, block, Op.effect, next, state_simp_rules, reads.1,
        NatOperand.words, NatOperand.pointer])
    exact ⟨ops.length + fuel, t, by rw [run_plus, block_run base ops s hc he ha follows, execution],
      uf.trans tf, ready⟩
  | large pointer words =>
    have positive := owned.expectedAt.2.2.1
    have nonzero : pointer ≠ 0#64 := by intro h; simp [h] at positive
    let ops : List Op := [.p0, .p4, .p8]
    let u := block base ops s
    have follows : Follows base ops s := by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
        hpc, reads.1, NatOperand.pointer, nonzero, BitVec.add_assoc]
    have uf := scan_pure_frame base ops s (by decide)
    have u8 : r (.GPR 8#5) u = BitVec.ofNat 64 words.length := by
      simp [u, ops, block, Op.effect, put, next, state_simp_rules, reads.2, NatOperand.payload]
    have u9 : r (.GPR 9#5) u = pointer := by
      simp [u, ops, block, Op.effect, put, next, state_simp_rules, reads.1, NatOperand.pointer]
    have up : read_pc u = base + 12#64 := by
      simp [u, ops, block, Op.effect, put, next, state_simp_rules, hpc,
        reads.1, NatOperand.pointer, nonzero, BitVec.add_assoc]
    have u11 : r (.GPR 11#5) u = BitVec.ofNat 64 words.length - 1#64 := by
      simp [u, ops, block, Op.effect, put, next, state_simp_rules, reads.2, NatOperand.payload]
    obtain ⟨fuel, v, execution, vf, kept, vp, v10⟩ := significant_scan base pointer words
      words.length u (Nat.le_refl _) (frame_code uf hc) (uf.error.trans he) (uf.aligned ha)
      up u9 u11 (uf.source _ _ owned.large_source) (uf.words _ _ owned.large_source owned.large_words)
    obtain ⟨fuel', t, execution', tf, ready⟩ := scanned_compare v base pointer words
      (frame_owned owned (uf.trans vf)) (frame_code (uf.trans vf) hc)
      ((uf.trans vf).error.trans he) ((uf.trans vf).aligned ha)
      (by
        by_cases hz : significantCount words words.length = 0
        · have hsig : sigWords words = 0 := hz
          simpa only [hz, hsig, ↓reduceIte] using vp
        · have hsig : sigWords words ≠ 0 := hz
          simpa only [hz, hsig, ↓reduceIte] using vp)
      ((kept 8#5 (by simp)).trans u8) ((kept 9#5 (by simp)).trans u9) v10
    refine ⟨ops.length + (fuel + fuel'), t, ?_, (uf.trans vf).trans tf, ready⟩
    rw [run_plus, block_run base ops s hc he ha follows, run_plus, execution, execution']

end SszArm.NatExact
