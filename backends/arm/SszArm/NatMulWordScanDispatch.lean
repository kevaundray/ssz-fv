import SszArm.NatMulWordScanTrim
import SszArm.NatMulWordIdentityNormalize
import SszArm.NatMulWordContract

namespace SszArm.NatMulWord

open UintCodec SszNative.Limbs

private def dispatchHead : List Op := [.p0, .p4]

private theorem dispatch_head_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base) : Follows base dispatchHead s := by
  have hpc : r .PC s = base := hp
  simp [dispatchHead, Follows, Op.row, Op.effect, Udivti3.compare, Udivti3.next,
    state_simp_rules, hpc]

private theorem dispatch_head_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (block base dispatchHead s) = r (.GPR reg) s := by
  simp [dispatchHead, block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules]

private theorem dispatch_head_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base dispatchHead s) =
      if r (.GPR 3#5) s = 1#64 then base + 100#64 else base + 8#64 := by
  simp [dispatchHead, block, Op.effect, Udivti3.compare, Udivti3.next, state_simp_rules]

private theorem dispatch_zero_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (block base [.p8] s) = r (.GPR reg) s := by
  simp [block, Op.effect, state_simp_rules]

private theorem dispatch_zero_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base [.p8] s) =
      if r (.GPR 3#5) s = 0#64 then base + 12#64 else base + 228#64 := by
  by_cases zero : r (.GPR 3#5) s = 0#64 <;> simp [block, Op.effect, state_simp_rules, zero]

/-- The original compare/branch dispatch gives factor-one precedence over the
factor-zero and general multiplication paths. -/
theorem word_dispatch (s : ArmState) (base factor : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (h3 : r (.GPR 3#5) s = factor) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
      (∀ reg : BitVec 5, r (.GPR reg) t = r (.GPR reg) s) ∧
      read_pc t = (if factor = 1#64 then base + 100#64
        else if factor = 0#64 then base + 12#64 else base + 228#64) := by
  let u := block base dispatchHead s
  have hu : run 2 s = u := block_run base dispatchHead s hc he ha (dispatch_head_follows s base hp)
  have huf : ScanFrame s u := scan_pure_frame base dispatchHead s (by decide)
  have huk (reg : BitVec 5) : r (.GPR reg) u = r (.GPR reg) s := dispatch_head_register s base reg
  have hup := dispatch_head_pc s base
  by_cases hone : factor = 1#64
  · refine ⟨2, u, hu, huf, huk, ?_⟩
    simpa only [h3, hone, ↓reduceIte] using hup
  · have hu8 : read_pc u = base + 8#64 := by simpa only [h3, if_neg hone] using hup
    let t := block base [.p8] u
    have ht : run 1 u = t := block_run base [.p8] u
      (huf.code hc) (huf.error.trans he) (huf.aligned ha) ⟨hu8, trivial⟩
    refine ⟨2 + 1, t, ?_, huf.trans (scan_pure_frame base [.p8] u (by decide)), ?_, ?_⟩
    · rw [run_plus, hu, ht]
    · intro reg; exact (dispatch_zero_register u base reg).trans (huk reg)
    · have pc := dispatch_zero_pc u base
      simpa only [huk 3#5, h3, if_neg hone] using pc

/-- X8 is exposed exactly, retaining the original xor lowering without imposing
an additional logical size bound or hiding its modular arithmetic. -/
def trimBias (words : List (BitVec 64)) : BitVec 64 :=
  ((BitVec.ofNat 64 words.length <<< 3) ^^^ 18446744073709551608#64) +
    BitVec.ofNat 64 (8 * words.length)

private def trimInitOps : List Op := [.p228, .p232, .p236, .p240, .p244, .p248]

private theorem trim_init_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 228#64) (hn : r (.GPR 1#5) s ≠ 0#64) :
    Follows base trimInitOps s := by
  have hpc : r .PC s = base + 228#64 := hp
  simp [trimInitOps, Follows, Op.row, Op.effect, put, next, state_simp_rules,
    hpc, hn, BitVec.add_assoc]

private theorem trim_init_pc (s : ArmState) (base : BitVec 64)
    (hn : r (.GPR 1#5) s ≠ 0#64) :
    read_pc (block base trimInitOps s) = base + 252#64 := by
  simp [trimInitOps, block, Op.effect, put, next, state_simp_rules, hn, BitVec.add_assoc]

private theorem trim_init_keep (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (h8 : reg ≠ 8#5) (h9 : reg ≠ 9#5) (h10 : reg ≠ 10#5) :
    r (.GPR reg) (block base trimInitOps s) = r (.GPR reg) s := by
  simp [trimInitOps, block, Op.effect, put, next, state_simp_rules, h8, h9, h10]

private theorem trim_init_offset (s : ArmState) (base : BitVec 64) :
    r (.GPR 8#5) (block base trimInitOps s) =
      ((r (.GPR 2#5) s <<< 3) ^^^ 18446744073709551608#64) := by
  simp [trimInitOps, block, Op.effect, put, next, state_simp_rules]

private theorem trim_init_index (s : ArmState) (base : BitVec 64) :
    r (.GPR 9#5) (block base trimInitOps s) = 0#64 := by
  simp [trimInitOps, block, Op.effect, put, next, state_simp_rules]

private theorem trim_init_address (s : ArmState) (base : BitVec 64) :
    r (.GPR 10#5) (block base trimInitOps s) =
      (r (.GPR 2#5) s <<< 3) + r (.GPR 1#5) s - 8#64 := by
  simp [trimInitOps, block, Op.effect, put, next, state_simp_rules]

theorem trim_scan_entry (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 228#64) (hn : pointer ≠ 0#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
      r (.GPR 1#5) t = pointer ∧ r (.GPR 2#5) t = BitVec.ofNat 64 words.length ∧
      r (.GPR 8#5) t = trimBias words - BitVec.ofNat 64 (8 * (sigWords words - 1)) ∧
      read_pc t = (if sigWords words = 0 then base + 920#64 else base + 304#64) ∧
      (sigWords words ≠ 0 → r (.GPR 9#5) t =
        BitVec.ofNat 64 (sigWords words - 1) - BitVec.ofNat 64 words.length) := by
  have shifted : (BitVec.ofNat 64 words.length <<< 3) = BitVec.ofNat 64 (8 * words.length) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 words.length * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * words.length)
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  let u := block base trimInitOps s
  have nonzero : r (.GPR 1#5) s ≠ 0#64 := by rw [h1]; exact hn
  have hu : run 6 s = u := block_run base trimInitOps s hc he ha
    (trim_init_follows s base hp nonzero)
  have huf : ScanFrame s u := scan_pure_frame base trimInitOps s (by decide)
  have hup : read_pc u = base + 252#64 := trim_init_pc s base nonzero
  have hu1 : r (.GPR 1#5) u = pointer :=
    (trim_init_keep s base 1#5 (by decide) (by decide) (by decide)).trans h1
  have hu2 : r (.GPR 2#5) u = BitVec.ofNat 64 words.length :=
    (trim_init_keep s base 2#5 (by decide) (by decide) (by decide)).trans h2
  have hu8 : r (.GPR 8#5) u = trimBias words - BitVec.ofNat 64 (8 * words.length) := by
    rw [trim_init_offset, h2]
    exact (BitVec.add_sub_cancel _ _).symm
  have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 words.length - BitVec.ofNat 64 words.length := by
    rw [trim_init_index, BitVec.sub_self]
  have hu10 : r (.GPR 10#5) u = pointer + BitVec.ofNat 64 (8 * words.length) - 8#64 := by
    rw [trim_init_address, h2, h1, shifted, BitVec.add_comm]
  obtain ⟨fuel, t, ht, htf, ht1, ht2, ht8, ht10, htp, ht9⟩ :=
    trim_scan base pointer (trimBias words) words words.length u (Nat.le_refl _)
      (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hu1 hu2 hu8 hu9 hu10
      (huf.source _ _ hs) (huf.words _ _ hs hm)
  refine ⟨6 + fuel, t, ?_, huf.trans htf, ht1, ht2, ht8, htp, ht9⟩
  rw [run_plus, hu, ht]

private def trimExitOps : List Op := [.p304, .p308, .p312, .p316]

private theorem trim_exit_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 304#64) : Follows base trimExitOps s := by
  have hpc : r .PC s = base + 304#64 := hp
  simp [trimExitOps, Follows, Op.row, Op.effect, put, next, Udivti3.compare,
    Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]

private theorem trim_exit_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base trimExitOps s) =
      if r (.GPR 2#5) s + r (.GPR 9#5) s + 1#64 = 1#64
      then base + 924#64 else base + 320#64 := by
  simp [trimExitOps, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

private theorem trim_exit_keep (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (h9 : reg ≠ 9#5) (h12 : reg ≠ 12#5) :
    r (.GPR reg) (block base trimExitOps s) = r (.GPR reg) s := by
  simp [trimExitOps, block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
    state_simp_rules, h9, h12]

private theorem trim_exit_count (s : ArmState) (base : BitVec 64) :
    r (.GPR 9#5) (block base trimExitOps s) = r (.GPR 2#5) s + r (.GPR 9#5) s + 1#64 := by
  simp [trimExitOps, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

private theorem trim_exit_index (s : ArmState) (base : BitVec 64) :
    r (.GPR 12#5) (block base trimExitOps s) = r (.GPR 2#5) s + r (.GPR 9#5) s := by
  simp [trimExitOps, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

private theorem trim_zero_keep (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (block base [.p920] s) = r (.GPR reg) s := by
  simp [block, Op.effect, state_simp_rules]

private theorem trim_zero_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base [.p920] s) =
      if r (.GPR 2#5) s = 0#64 then base + 928#64 else base + 924#64 := by
  simp [block, Op.effect, state_simp_rules]

private theorem trim_low_keep (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (hne : reg ≠ 2#5) : r (.GPR reg) (block base [.p924] s) = r (.GPR reg) s := by
  simp [block, Op.effect, put, next, state_simp_rules, hne]

private theorem trim_low_payload (s : ArmState) (base : BitVec 64) :
    r (.GPR 2#5) (block base [.p924] s) = read_mem_bytes 8 (r (.GPR 1#5) s) s := by
  simp [block, Op.effect, put, next, state_simp_rules]

private theorem trim_low_pc (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 924#64) : read_pc (block base [.p924] s) = base + 928#64 := by
  have hpc : r .PC s = base + 924#64 := hp
  simp [block, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]

private theorem trim_low_exit (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 924#64) (h1 : r (.GPR 1#5) s = pointer)
    (positive : 0 < words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ t, run 1 s = t ∧ ScanFrame s t ∧ r (.GPR 1#5) t = pointer ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ read_pc t = base + 928#64 ∧
      r (.GPR 2#5) t = words[0]?.getD 0#64 := by
  have word : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
    simpa only [show (BitVec.ofNat 64 0 <<< 3) = 0#64 from rfl, BitVec.add_zero] using
      (scan_limb s pointer words 0 positive hs hm).2.2
  refine ⟨block base [.p924] s, block_run base [.p924] s hc he ha ⟨hp, trivial⟩,
    scan_pure_frame base [.p924] s (by decide),
    (trim_low_keep s base 1#5 (by decide)).trans h1,
    trim_low_keep s base 8#5 (by decide), trim_low_pc s base hp, ?_⟩
  rw [trim_low_payload, h1, word]

/-- The scan's empty/single/multiword exits preserve the raw physical input and
select either original low-word multiplication or the reservation guard. -/
theorem trim_normalize_exit (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = (if sigWords words = 0 then base + 920#64 else base + 304#64))
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (h9 : sigWords words ≠ 0 → r (.GPR 9#5) s =
      BitVec.ofNat 64 (sigWords words - 1) - BitVec.ofNat 64 words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ r (.GPR 1#5) t = pointer ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      (if sigWords words ≤ 1 then
        read_pc t = base + 928#64 ∧ r (.GPR 2#5) t = words[0]?.getD 0#64
       else read_pc t = base + 320#64 ∧ r (.GPR 2#5) t = BitVec.ofNat 64 words.length ∧
        r (.GPR 9#5) t = BitVec.ofNat 64 (sigWords words) ∧
        r (.GPR 12#5) t = BitVec.ofNat 64 (sigWords words - 1)) := by
  have hlength : words.length < 2^64 := by have := hs.2.1; omega
  have hbound : sigWords words < 2^64 := Nat.lt_of_le_of_lt (sigWords_le_length words) hlength
  have lengthNe (nonempty : words ≠ []) : BitVec.ofNat 64 words.length ≠ 0#64 := by
    have positive := List.length_pos_iff.mpr nonempty
    bv_omega
  have countNe (notOne : sigWords words ≠ 1) : BitVec.ofNat 64 (sigWords words) ≠ 1#64 := by
    bv_omega
  by_cases hz : sigWords words = 0
  · have hp920 : read_pc s = base + 920#64 := by simpa only [if_pos hz] using hp
    have small : sigWords words ≤ 1 := by omega
    let u := block base [.p920] s
    have hu : run 1 s = u := block_run base [.p920] s hc he ha ⟨hp920, trivial⟩
    have huf : ScanFrame s u := scan_pure_frame base [.p920] s (by decide)
    have hu1 : r (.GPR 1#5) u = pointer := (trim_zero_keep s base 1#5).trans h1
    have hu8 : r (.GPR 8#5) u = r (.GPR 8#5) s := trim_zero_keep s base 8#5
    have hup := trim_zero_pc s base
    by_cases empty : words = []
    · refine ⟨1, u, hu, huf, hu1, hu8, ?_⟩
      rw [if_pos small]
      constructor
      · simpa only [h2, empty, List.length_nil, ↓reduceIte] using hup
      · have payload := (trim_zero_keep s base 2#5).trans h2
        simp only [empty, List.length_nil, List.getElem?_nil, Option.getD_none] at payload ⊢
        arm_word_nf at payload ⊢
        exact payload
    · have hu924 : read_pc u = base + 924#64 := by
        simpa only [h2, if_neg (lengthNe empty)] using hup
      obtain ⟨t, ht, htf, ht1, ht8, htp, ht2⟩ := trim_low_exit u base pointer words
        (huf.code hc) (huf.error.trans he) (huf.aligned ha) hu924 hu1
        (List.length_pos_iff.mpr empty) (huf.source _ _ hs) (huf.words _ _ hs hm)
      refine ⟨1 + 1, t, ?_, huf.trans htf, ht1, ht8.trans hu8, ?_⟩
      · rw [run_plus, hu, ht]
      · rw [if_pos small]; exact ⟨htp, ht2⟩
  · have hp304 : read_pc s = base + 304#64 := by simpa only [if_neg hz] using hp
    have hcount := h9 hz
    have hadd : BitVec.ofNat 64 (sigWords words - 1) + 1#64 =
        BitVec.ofNat 64 (sigWords words) := by
      arm_word_nf
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel (by omega : 1 ≤ sigWords words)]
    let u := block base trimExitOps s
    have hu : run 4 s = u := block_run base trimExitOps s hc he ha (trim_exit_follows s base hp304)
    have huf : ScanFrame s u := scan_pure_frame base trimExitOps s (by decide)
    have hu1 : r (.GPR 1#5) u = pointer :=
      (trim_exit_keep s base 1#5 (by decide) (by decide)).trans h1
    have hu2 : r (.GPR 2#5) u = BitVec.ofNat 64 words.length :=
      (trim_exit_keep s base 2#5 (by decide) (by decide)).trans h2
    have hu8 : r (.GPR 8#5) u = r (.GPR 8#5) s := trim_exit_keep s base 8#5 (by decide) (by decide)
    have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 (sigWords words) := by
      rw [trim_exit_count, h2, hcount, trim_remaining_sum, hadd]
    have hu12 : r (.GPR 12#5) u = BitVec.ofNat 64 (sigWords words - 1) := by
      rw [trim_exit_index, h2, hcount, trim_remaining_sum]
    have hup : read_pc u =
        if BitVec.ofNat 64 (sigWords words) = 1#64 then base + 924#64 else base + 320#64 := by
      rw [trim_exit_pc, h2, hcount, trim_remaining_sum, hadd]
    by_cases hone : sigWords words = 1
    · have positive : 0 < words.length := by have := sigWords_le_length words; omega
      have small : sigWords words ≤ 1 := by omega
      have hu924 : read_pc u = base + 924#64 := by
        simpa only [hone, BitVec.ofNat_eq_ofNat, ↓reduceIte] using hup
      obtain ⟨t, ht, htf, ht1, ht8, htp, ht2⟩ := trim_low_exit u base pointer words
        (huf.code hc) (huf.error.trans he) (huf.aligned ha) hu924 hu1 positive
        (huf.source _ _ hs) (huf.words _ _ hs hm)
      refine ⟨4 + 1, t, ?_, huf.trans htf, ht1, ht8.trans hu8, ?_⟩
      · rw [run_plus, hu, ht]
      · rw [if_pos small]; exact ⟨htp, ht2⟩
    · have notSmall : ¬ sigWords words ≤ 1 := by omega
      refine ⟨4, u, hu, huf, hu1, hu8, ?_⟩
      rw [if_neg notSmall]
      exact ⟨by simpa only [if_neg (countNe hone)] using hup, hu2, hu9, hu12⟩

end SszArm.NatMulWord
