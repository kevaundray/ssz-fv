import SszArm.NatMulWordNormalizeScan
import SszArm.NatMulWordIdentityNormalize

namespace SszArm.NatMulWord

open UintCodec SszNative.Limbs

private theorem select_compare_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (Op.p1484.effect base s) = r (.GPR reg) s := by
  have different (flag : PFlag) : StateField.GPR reg ≠ .FLAG flag := by
    intro equal
    cases equal
  simp only [Op.effect, Udivti3.compare, Udivti3.next, write_pstate,
    r_of_w_different (different .V), r_of_w_different (different .C),
    r_of_w_different (different .Z), r_of_w_different (different .N),
    NatCompare.r_gpr_of_w_pc]

private theorem select_compare_zero (s : ArmState) (base : BitVec 64) :
    r (.FLAG .Z) (Op.p1484.effect base s) =
      (AddWithCarry (r (.GPR 12#5) s) (~~~1#64) 1#1).2.z := by
  simp only [Op.effect, Udivti3.compare, write_pstate,
    r_of_w_different (show StateField.FLAG .Z ≠ .FLAG .V from by decide),
    r_of_w_different (show StateField.FLAG .Z ≠ .FLAG .C from by decide), r_of_w_same]

private theorem select_payload_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (Op.p1488.effect base s) =
      if reg = 8#5 then
        (if r (.FLAG .Z) s = 1#1 then r (.GPR 11#5) s else r (.GPR 12#5) s)
      else r (.GPR reg) s := by
  simp only [Op.effect, put, next, NatCompare.r_gpr_of_w_gpr,
    NatCompare.r_gpr_of_w_pc] <;> arm_word_nf

private theorem select_payload_zero (s : ArmState) (base : BitVec 64) :
    r (.FLAG .Z) (Op.p1488.effect base s) = r (.FLAG .Z) s := by
  simp only [Op.effect, put, next]
  arm_state_nf

private theorem select_pointer_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (Op.p1492.effect base s) =
      if reg = 9#5 then
        (if r (.FLAG .Z) s = 1#1 then 0#64 else r (.GPR 10#5) s)
      else r (.GPR reg) s := by
  simp only [Op.effect, put, next, NatCompare.r_gpr_of_w_gpr,
    NatCompare.r_gpr_of_w_pc] <;> arm_word_nf

private theorem select_block_pointer (s : ArmState) (base : BitVec 64) :
    r (.GPR 9#5) (block base [.p1484, .p1488, .p1492] s) =
      if r (.GPR 12#5) s = 1#64 then 0#64 else r (.GPR 10#5) s := by
  change r (.GPR 9#5)
    (Op.p1492.effect base (Op.p1488.effect base (Op.p1484.effect base s))) = _
  rw [select_pointer_gpr]
  simp only [↓reduceIte, select_payload_zero, select_compare_zero, Udivti3.cmp_zero,
    select_payload_gpr, show (10#5 : BitVec 5) ≠ 8#5 by decide, select_compare_gpr]

private theorem select_block_payload (s : ArmState) (base : BitVec 64) :
    r (.GPR 8#5) (block base [.p1484, .p1488, .p1492] s) =
      if r (.GPR 12#5) s = 1#64 then r (.GPR 11#5) s else r (.GPR 12#5) s := by
  change r (.GPR 8#5)
    (Op.p1492.effect base (Op.p1488.effect base (Op.p1484.effect base s))) = _
  rw [select_pointer_gpr]
  simp only [show (8#5 : BitVec 5) ≠ 9#5 by decide, ↓reduceIte,
    select_payload_gpr, select_compare_zero, Udivti3.cmp_zero, select_compare_gpr]

private theorem select_block_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 1484#64) : Follows base [.p1484, .p1488, .p1492] s := by
  have hpc : r .PC s = base + 1484#64 := hp
  simp [Follows, Op.row, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]

private theorem select_block_pc (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 1484#64) :
    read_pc (block base [.p1484, .p1488, .p1492] s) = base + 1496#64 := by
  have hpc : r .PC s = base + 1484#64 := hp
  simp [block, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]

private theorem normalize_entry_gpr (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (block base [.p1464] s) =
      if reg = 8#5 then r (.GPR 10#5) s - r (.GPR 8#5) s else r (.GPR reg) s := by
  change r (.GPR reg) (Op.p1464.effect base s) = _
  simp only [Op.effect, put, next, NatCompare.r_gpr_of_w_gpr,
    NatCompare.r_gpr_of_w_pc] <;> arm_word_nf

private theorem normalize_entry_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base [.p1464] s) = read_pc s + 4#64 := by
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next, read_pc]
  arm_state_nf

/-- The native CSEL pair chooses Small only for significant count one. -/
theorem normalize_nonzero_exit (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1484#64)
    (h10 : r (.GPR 10#5) s = pointer)
    (h11 : r (.GPR 11#5) s = words[0]?.getD 0#64)
    (h12 : r (.GPR 12#5) s = BitVec.ofNat 64 (sigWords words))
    (hn : sigWords words ≠ 0) (hs : NatCompare.Source s pointer words) :
    ∃ t, run 3 s = t ∧ NormalizeFrame s t ∧ read_pc t = base + 1496#64 ∧
      r (.GPR 9#5) t = (SszNative.NatOperand.fromWords pointer words).pointer ∧
      r (.GPR 8#5) t = (SszNative.NatOperand.fromWords pointer words).payload := by
  have hbound : sigWords words < 2^64 := by
    have := hs.2.1
    have := sigWords_le_length words
    omega
  let ops : List Op := [.p1484, .p1488, .p1492]
  let t := block base ops s
  have hf : Follows base ops s := select_block_follows s base hp
  refine ⟨t, block_run base ops s hc he ha hf,
    normalize_read_frame base ops s (by decide), select_block_pc s base hp, ?_, ?_⟩
  · change r (.GPR 9#5) (block base [.p1484, .p1488, .p1492] s) = _
    rw [select_block_pointer, h12, h10, SszNative.NatOperand.fromWords_pointer]
    by_cases one : sigWords words = 1
    · simp only [one, Nat.le_refl, ↓reduceIte] <;> arm_word_nf
    · have large : ¬ sigWords words ≤ 1 := by omega
      have unequal : BitVec.ofNat 64 (sigWords words) ≠ 1#64 := by bv_omega
      simp only [unequal, large, ↓reduceIte]
  · change r (.GPR 8#5) (block base [.p1484, .p1488, .p1492] s) = _
    rw [select_block_payload, h12, h11, SszNative.NatOperand.fromWords_payload]
    by_cases one : sigWords words = 1
    · simp only [one, Nat.le_refl, ↓reduceIte] <;> arm_word_nf
    · have large : ¬ sigWords words ≤ 1 := by omega
      have unequal : BitVec.ofNat 64 (sigWords words) ≠ 1#64 := by bv_omega
      simp only [unequal, large, ↓reduceIte]

def normalizePath (words : List (BitVec 64)) : StatusPath :=
  if sigWords words = 0 then .zeroGeneral else .general

/-- The zero route preserves the final loaded zero in X9 (or its entry value
for an empty physical image); the nonzero route spills the selected pointer. -/
def normalizeSpill (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64)) : BitVec 64 :=
  if sigWords words = 0 then
    if words.length = 0 then r (.GPR 9#5) s else 0#64
  else (SszNative.NatOperand.fromWords pointer words).pointer

/-- Entry at the original negative-bias conversion, through the entire backward
scan and exact return-path selection. No loop-iteration bound is supplied. -/
theorem normalize_ready (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1464#64)
    (h8 : r (.GPR 8#5) s = -BitVec.ofNat 64 (8 * (words.length - 1)))
    (h10 : r (.GPR 10#5) s = pointer)
    (h11 : r (.GPR 11#5) s = words[0]?.getD 0#64)
    (h12 : r (.GPR 12#5) s = BitVec.ofNat 64 (words.length + 1))
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ NormalizeFrame s t ∧
      read_pc t = base + BitVec.ofNat 64 (valueStart (normalizePath words)) ∧
      valuePointer (normalizePath words) t = (SszNative.NatOperand.fromWords pointer words).pointer ∧
      valuePayload (normalizePath words) t = (SszNative.NatOperand.fromWords pointer words).payload ∧
      r (.GPR 9#5) t = normalizeSpill s pointer words := by
  let u := block base [.p1464] s
  have hf : Follows base [.p1464] s := ⟨hp, trivial⟩
  have hu : run 1 s = u := block_run base [.p1464] s hc he ha hf
  have huf : NormalizeFrame s u := normalize_read_frame base [.p1464] s (by decide)
  have hup : read_pc u = base + 1468#64 := by
    change read_pc (block base [.p1464] s) = _
    rw [normalize_entry_pc, hp]
    bv_omega
  have hu8 : words.length ≠ 0 → r (.GPR 8#5) u =
      pointer + BitVec.ofNat 64 (8 * (words.length - 1)) := by
    intro positive
    change r (.GPR 8#5) (block base [.p1464] s) = _
    rw [normalize_entry_gpr]
    simp only [↓reduceIte, h8, h10]
    bv_omega
  have hu12 : r (.GPR 12#5) u = BitVec.ofNat 64 (words.length + 1) := by
    change r (.GPR 12#5) (block base [.p1464] s) = _
    rw [normalize_entry_gpr]
    simp only [show (12#5 : BitVec 5) ≠ 8#5 by decide, ↓reduceIte, h12]
  have hu9 : r (.GPR 9#5) u = r (.GPR 9#5) s := by
    change r (.GPR 9#5) (block base [.p1464] s) = _
    rw [normalize_entry_gpr]
    simp only [show (9#5 : BitVec 5) ≠ 8#5 by decide, ↓reduceIte]
  obtain ⟨fuel, v, hv, hvf, hvp, hv12, hv9⟩ := normalize_scan base pointer words words.length u
    (Nat.le_refl _) (huf.code hc) (huf.error.trans he) (huf.aligned ha)
    hup hu8 hu12 (huf.source _ _ hs) (huf.words _ _ hm)
  have hsf := huf.trans hvf
  change read_pc v = (if sigWords words = 0 then base + 1544#64 else base + 1484#64) at hvp
  change r (.GPR 12#5) v = BitVec.ofNat 64 (sigWords words) at hv12
  change sigWords words = 0 → r (.GPR 9#5) v =
    if words.length = 0 then r (.GPR 9#5) u else 0#64 at hv9
  by_cases zero : sigWords words = 0
  · refine ⟨1 + fuel, v, ?_, hsf, ?_, ?_, ?_, ?_⟩
    · rw [run_plus, hu, hv]
    · simpa [normalizePath, zero, valueStart] using hvp
    · simp [normalizePath, zero, valuePointer, normalized_zero pointer words zero,
        SszNative.NatOperand.pointer]
    · simp [normalizePath, zero, valuePayload, normalized_zero pointer words zero,
        SszNative.NatOperand.payload]
    · simpa [normalizeSpill, zero, hu9] using hv9 zero
  · obtain ⟨t, ht, htf, htp, ht9, ht8⟩ := normalize_nonzero_exit v base pointer words
      (hsf.code hc) (hsf.error.trans he) (hsf.aligned ha) (by simpa [zero] using hvp)
      ((hsf.registers _ (by decide)).trans h10) ((hsf.registers _ (by decide)).trans h11)
      hv12 zero (hsf.source _ _ hs)
    refine ⟨1 + fuel + 3, t, ?_, hsf.trans htf, ?_, ?_, ?_, ?_⟩
    · rw [run_plus, run_plus, hu, hv, ht]
    · simpa [normalizePath, zero, valueStart] using htp
    · simpa [normalizePath, zero, valuePointer] using ht9
    · simpa [normalizePath, zero, valuePayload] using ht8
    · simpa [normalizeSpill, zero] using ht9

end SszArm.NatMulWord
