import SszArm.NatMulNormalizeFrame
import SszArm.DelimitedArenaArithmetic

namespace SszArm.NatMul

open UintCodec SszNative.Limbs

def normalizeGuard : List Op := [.p1060, .p1064]
def normalizeTail : List Op := [.p1048, .p1052, .p1056]

def normalizeRound (s : ArmState) (base word : BitVec 64) : ArmState :=
  block base normalizeTail (normalizeLoaded (block base normalizeGuard s) base word)

private theorem normalize_guard_follows (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 1060#64) : Follows base normalizeGuard s := by
  have hpc : r .PC s = base + 1060#64 := pc
  simp [normalizeGuard, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

private theorem normalize_compare_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (Op.p1060.effect base s) = r (.GPR reg) s := by
  have different (flag : PFlag) : StateField.GPR reg ≠ .FLAG flag := by
    intro equal
    cases equal
  simp only [Op.effect, write_pstate, next,
    r_of_w_different (different .V), r_of_w_different (different .C),
    r_of_w_different (different .Z), r_of_w_different (different .N),
    NatCompare.r_gpr_of_w_pc]

private theorem normalize_compare_zero (s : ArmState) (base : BitVec 64) :
    r (.FLAG .Z) (Op.p1060.effect base s) =
      (AddWithCarry (r (.GPR 23#5) s) 1#64 0#1).2.z := by
  simp only [Op.effect, write_pstate,
    r_of_w_different (show StateField.FLAG .Z ≠ .FLAG .V from by decide),
    r_of_w_different (show StateField.FLAG .Z ≠ .FLAG .C from by decide), r_of_w_same]

private theorem normalize_guard_branch_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (Op.p1064.effect base s) = r (.GPR reg) s := by
  simp only [Op.effect, NatCompare.r_gpr_of_w_pc]

private theorem normalize_guard_branch_pc (s : ArmState) (base : BitVec 64) :
    read_pc (Op.p1064.effect base s) =
      if r (.FLAG .Z) s ≠ 1#1 then base + 1016#64 else base + 1068#64 := by
  simp only [Op.effect, read_pc, r_of_w_same]

private theorem normalize_guard_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (block base normalizeGuard s) = r (.GPR reg) s := by
  change r (.GPR reg) (Op.p1064.effect base (Op.p1060.effect base s)) = _
  rw [normalize_guard_branch_gpr, normalize_compare_gpr]

private theorem normalize_guard_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base normalizeGuard s) =
      if r (.GPR 23#5) s + 1#64 = 0#64 then base + 1068#64 else base + 1016#64 := by
  change read_pc (Op.p1064.effect base (Op.p1060.effect base s)) = _
  rw [normalize_guard_branch_pc, normalize_compare_zero]
  simp only [ne_eq, Delimited.add_zero_flag, ite_not]

private theorem normalize_loaded_pc (s : ArmState) (base word : BitVec 64) :
    read_pc (normalizeLoaded s base word) = base + 1048#64 := by
  simp only [normalizeLoaded, read_pc, r_of_w_same]

private theorem normalize_loaded_word (s : ArmState) (base word : BitVec 64) :
    r (.GPR 9#5) (normalizeLoaded s base word) = word := by
  simp only [normalizeLoaded, NatCompare.r_gpr_of_w_pc, r_of_w_same]

private theorem normalize_loaded_register (s : ArmState) (base word : BitVec 64)
    (reg : BitVec 5) (different : reg ≠ 9#5) :
    r (.GPR reg) (normalizeLoaded s base word) = r (.GPR reg) s := by
  have fields : StateField.GPR reg ≠ .GPR 9#5 := by
    intro equal
    exact different (StateField.GPR.inj equal)
  simp only [normalizeLoaded, NatCompare.r_gpr_of_w_pc, r_of_w_different fields,
    NatCompare.saved, r_of_write_mem_bytes]

private theorem normalize_tail_move (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (Op.p1048.effect base s) =
      if reg = 8#5 then r (.GPR 23#5) s else r (.GPR reg) s := by
  simp only [Op.effect, put, next, NatCompare.r_gpr_of_w_pc, NatCompare.r_gpr_of_w_gpr]
  arm_word_nf

private theorem normalize_tail_sub (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (Op.p1052.effect base s) =
      if reg = 23#5 then r (.GPR 23#5) s - 1#64 else r (.GPR reg) s := by
  simp only [Op.effect, put, next, NatCompare.r_gpr_of_w_pc, NatCompare.r_gpr_of_w_gpr]
  arm_word_nf

private theorem normalize_tail_branch_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (Op.p1056.effect base s) = r (.GPR reg) s := by
  simp only [Op.effect, NatCompare.r_gpr_of_w_pc]

private theorem normalize_tail_branch_pc (s : ArmState) (base : BitVec 64) :
    read_pc (Op.p1056.effect base s) =
      if r (.GPR 9#5) s = 0#64 then base + 1060#64 else base + 1276#64 := by
  simp only [Op.effect, read_pc, r_of_w_same, ne_eq, ite_not]

private theorem normalize_tail_keep (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (not8 : reg ≠ 8#5) (not23 : reg ≠ 23#5) :
    r (.GPR reg) (block base normalizeTail s) = r (.GPR reg) s := by
  change r (.GPR reg) (Op.p1056.effect base (Op.p1052.effect base (Op.p1048.effect base s))) = _
  rw [normalize_tail_branch_gpr, normalize_tail_sub]
  simp only [not23, ↓reduceIte, normalize_tail_move, not8]

private theorem normalize_tail_index (s : ArmState) (base : BitVec 64) :
    r (.GPR 23#5) (block base normalizeTail s) = r (.GPR 23#5) s - 1#64 := by
  change r (.GPR 23#5) (Op.p1056.effect base (Op.p1052.effect base (Op.p1048.effect base s))) = _
  rw [normalize_tail_branch_gpr, normalize_tail_sub]
  simp only [↓reduceIte, normalize_tail_move, show (23#5 : BitVec 5) ≠ 8#5 by decide]

private theorem normalize_tail_count (s : ArmState) (base : BitVec 64) :
    r (.GPR 8#5) (block base normalizeTail s) = r (.GPR 23#5) s := by
  change r (.GPR 8#5) (Op.p1056.effect base (Op.p1052.effect base (Op.p1048.effect base s))) = _
  rw [normalize_tail_branch_gpr, normalize_tail_sub]
  simp only [show (8#5 : BitVec 5) ≠ 23#5 by decide, ↓reduceIte, normalize_tail_move]

private theorem normalize_tail_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base normalizeTail s) =
      if r (.GPR 9#5) s = 0#64 then base + 1060#64 else base + 1276#64 := by
  change read_pc (Op.p1056.effect base (Op.p1052.effect base (Op.p1048.effect base s))) = _
  rw [normalize_tail_branch_pc, normalize_tail_sub]
  simp only [show (9#5 : BitVec 5) ≠ 23#5 by decide, ↓reduceIte, normalize_tail_move,
    show (9#5 : BitVec 5) ≠ 8#5 by decide]

private theorem normalize_tail_follows (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 1048#64) : Follows base normalizeTail s := by
  have hpc : r .PC s = base + 1048#64 := pc
  simp [normalizeTail, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem normalize_scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1060#64)
    (h20 : r (.GPR 20#5) s = pointer) (h23 : r (.GPR 23#5) s = BitVec.ofNat 64 n)
    (hn : n < words.length) (hs : NatCompare.Source s pointer words)
    (hm : NatCompare.Words s pointer words) :
    let t := normalizeRound s base (words[n]?.getD 0#64)
    run 13 s = t ∧ NormalizeFrame s t ∧ r (.GPR 20#5) t = pointer ∧
      r (.GPR 23#5) t = BitVec.ofNat 64 n - 1#64 ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 n ∧
      read_pc t = if words[n]?.getD 0#64 = 0#64 then base + 1060#64 else base + 1276#64 := by
  have hbound : words.length < 2^64 := by have := hs.2.1; omega
  have hnonzero : BitVec.ofNat 64 n + 1#64 ≠ 0#64 := by bv_omega
  let u := block base normalizeGuard s
  have hf : Follows base normalizeGuard s := normalize_guard_follows s base hp
  have hu : run 2 s = u := block_run base normalizeGuard s hc he ha hf
  have huf := normalize_pure_frame base normalizeGuard s (by decide)
  have hup : read_pc u = base + 1016#64 := by
    rw [normalize_guard_pc, h23]
    simp only [hnonzero, ↓reduceIte]
  have hu20 : r (.GPR 20#5) u = pointer := by
    exact (normalize_guard_register s base 20#5).trans h20
  have hu23 : r (.GPR 23#5) u = BitVec.ofNat 64 n := by
    exact (normalize_guard_register s base 23#5).trans h23
  have hus := huf.source pointer words hs
  obtain ⟨physical, separate, valueAt⟩ :=
    NatMulWord.scan_limb u pointer words n hn hus (huf.words pointer words hs hm)
  let v := normalizeLoaded u base (words[n]?.getD 0#64)
  have hv : run 8 u = v := normalize_load_run u base _
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hus.1
    (by simpa only [hu20, hu23] using physical)
    (by simpa only [hu20, hu23] using separate)
    (by simpa only [hu20, hu23] using valueAt)
  have hvf : NormalizeFrame s v :=
    huf.trans (normalize_load_frame u base (words[n]?.getD 0#64) hus.1)
  have htail : Follows base normalizeTail v :=
    normalize_tail_follows v base (normalize_loaded_pc u base _)
  have ht : run 3 v = block base normalizeTail v :=
    block_run base normalizeTail v (hvf.code hc) (hvf.error.trans he) (hvf.aligned ha) htail
  refine ⟨?_, hvf.trans (normalize_pure_frame base normalizeTail v (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [show 13 = 2 + 8 + 3 by decide, run_plus, run_plus, hu, hv, ht]
    rfl
  · change r (.GPR 20#5) (block base normalizeTail v) = pointer
    rw [normalize_tail_keep v base 20#5 (by decide) (by decide),
      normalize_loaded_register u base _ 20#5 (by decide)]
    exact hu20
  · change r (.GPR 23#5) (block base normalizeTail v) = BitVec.ofNat 64 n - 1#64
    rw [normalize_tail_index, normalize_loaded_register u base _ 23#5 (by decide), hu23]
  · change r (.GPR 8#5) (block base normalizeTail v) = BitVec.ofNat 64 n
    rw [normalize_tail_count, normalize_loaded_register u base _ 23#5 (by decide), hu23]
  · change read_pc (block base normalizeTail v) = _
    rw [normalize_tail_pc, normalize_loaded_word]

/-- Induction consumes the remaining physical output length. No bound on the
logical multiplication or on its redundant high-zero suffix is imposed. -/
theorem normalize_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 1060#64 → r (.GPR 20#5) s = pointer →
      r (.GPR 23#5) s = BitVec.ofNat 64 n - 1#64 →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ NormalizeFrame s t ∧ r (.GPR 20#5) t = pointer ∧
        read_pc t = (if significantCount words n = 0 then base + 1068#64 else base + 1276#64) ∧
        (significantCount words n ≠ 0 →
          r (.GPR 8#5) t = BitVec.ofNat 64 (significantCount words n - 1)) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h20 h23 hs hm
    let t := block base normalizeGuard s
    have hf : Follows base normalizeGuard s := normalize_guard_follows s base hp
    refine ⟨2, t, block_run base normalizeGuard s hc he ha hf,
      normalize_pure_frame base normalizeGuard s (by decide), ?_, ?_, ?_⟩
    · exact (normalize_guard_register s base 20#5).trans h20
    · change read_pc (block base normalizeGuard s) = _
      rw [normalize_guard_pc, h23]
      arm_word_nf <;> simp only [significantCount, BitVec.sub_add_cancel, ↓reduceIte]
    · intro nonzero
      exact False.elim (nonzero rfl)
  | succ n ih =>
    intro s hn hc he ha hp h20 h23 hs hm
    have h23' : r (.GPR 23#5) s = BitVec.ofNat 64 n := by
      simpa [BitVec.ofNat_add, BitVec.add_sub_cancel] using h23
    obtain ⟨hu, huf, hu20, hu23, hu8, hup⟩ :=
      normalize_scan_round s base pointer words n hc he ha hp h20 h23' (by omega) hs hm
    let u := normalizeRound s base (words[n]?.getD 0#64)
    change run 13 s = u at hu
    change NormalizeFrame s u at huf
    change r (.GPR 20#5) u = pointer at hu20
    change r (.GPR 23#5) u = BitVec.ofNat 64 n - 1#64 at hu23
    change r (.GPR 8#5) u = BitVec.ofNat 64 n at hu8
    change read_pc u = if words[n]?.getD 0#64 = 0#64 then base + 1060#64 else base + 1276#64 at hup
    by_cases hz : words[n]?.getD 0#64 = 0#64
    · obtain ⟨fuel, t, ht, htf, ht20, htp, ht8⟩ := ih u (by omega)
        (huf.code hc) (huf.error.trans he) (huf.aligned ha)
        (by simpa [hz] using hup) hu20 hu23 (huf.source _ _ hs) (huf.words _ _ hs hm)
      refine ⟨13 + fuel, t, ?_, huf.trans htf, ht20, ?_, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, hz] using htp
      · simpa [significantCount, hz] using ht8
    · refine ⟨13, u, hu, huf, hu20, ?_, ?_⟩
      · simpa [significantCount, hz] using hup
      · intro h; simpa [significantCount, hz] using hu8

end SszArm.NatMul
