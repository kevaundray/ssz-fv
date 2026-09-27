import SszArm.ByteViewListCompare

namespace SszArm.ByteView.Bounded

open UintCodec
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem value_zero (words : List (BitVec 64)) (hk : sigWords words = 0) : value words = 0 := by
  apply (trim_eq_nil_iff_value_zero words).mp
  apply List.eq_nil_iff_length_eq_zero.mpr
  simpa only [trim_length] using hk

theorem value_one (words : List (BitVec 64)) (hk : sigWords words = 1) :
    value words = (words[0]?.getD 0#64).toNat := by
  rw [← trim_value, trim_eq_take, hk]
  cases words <;> simp [value]

theorem value_many (words : List (BitVec 64)) (hk : 1 < sigWords words) :
    2^64 ≤ value words := by
  have hn : trim words ≠ [] := by
    intro h
    have hl := trim_length words
    rw [h] at hl
    simp only [List.length_nil] at hl
    omega
  have hb := canonical_ge_pow (trim words) (trim_canonical words) hn
  rw [trim_value, trim_length] at hb
  apply Nat.le_trans _ hb
  apply Nat.pow_le_pow_right (by decide)
  omega

def sameCount (k : Nat) (a : BitVec 64) : Prop :=
  (k = 0 ∧ a = 0#64) ∨ (k = 1 ∧ a ≠ 0#64)

instance (k : Nat) (a : BitVec 64) : Decidable (sameCount k a) :=
  inferInstanceAs (Decidable ((k = 0 ∧ a = 0#64) ∨ (k = 1 ∧ a ≠ 0#64)))

def countOps (k : Nat) (a : BitVec 64) : List Op :=
  if k = 0 then [.p3480, .p3484] ++
    if a = 0#64 then [.p3488, .p3492, .p3500] else [.p3496, .p3500]
  else [.p772, .p776, .p780, .p784, .p792] ++
    if k = 1 ∧ a ≠ 0#64 then [] else [.p796]

/-- Significant-length comparison, stopping before either low-word load or spill. -/
theorem compare_counts (s : ArmState) (base : BitVec 64) (k : Nat)
    (hc : CodeAt s base) (hp : read_pc s = scanExit base k)
    (he : read_err s = .None) (ha : CheckSPAlignment s) (hk : k < 2^64)
    (h10 : r (.GPR 10#5) s = if r (.GPR 3#5) s = 0#64 then 0#64 else 1#64)
    (h11 : k ≠ 0 → r (.GPR 11#5) s = BitVec.ofNat 64 k) :
    ∃ fuel t, run fuel s = t ∧ WidthFrame s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      r (.GPR 10#5) t = (if k = 0 ∧ r (.GPR 3#5) s ≠ 0#64 then 1#64 else 0#64) ∧
      read_pc t = if sameCount k (r (.GPR 3#5) s) then base + 3504#64 else base + 3536#64 := by
  let ops := countOps k (r (.GPR 3#5) s)
  let t := block base ops s
  have hn : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt hk
  have hpc : r .PC s = scanExit base k := hp
  have hfollow : Follows base ops s := by
    by_cases hk0 : k = 0 <;> by_cases hz : r (.GPR 3#5) s = 0#64 <;> by_cases hk1 : k = 1
    all_goals
      try have hreg := h11 hk0
      try have hpos : 1 ≤ k := by omega
      simp (config := {decide := true, instances := true})
        [*, ops, countOps, scanExit, Follows, Op.row, Op.effect, put, next,
         Udivti3.compare, Udivti3.next, state_simp_rules, BitVec.ofNat_eq_ofNat,
         BitVec.add_assoc]
      all_goals
        intro heq
        have heqn := congrArg BitVec.toNat heq
        simp only [hn, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at heqn
        omega
  refine ⟨ops.length, t, block_run base ops s hc he ha hfollow,
    readonly_frame base ops s ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [ops, countOps]; split <;> split <;> decide
  all_goals
    by_cases hk0 : k = 0 <;> by_cases hz : r (.GPR 3#5) s = 0#64 <;> by_cases hk1 : k = 1
    all_goals
      try have hreg := h11 hk0
      try have hpos : 1 ≤ k := by omega
      simp (config := {decide := true, instances := true})
        [*, t, ops, countOps, sameCount, scanExit, block, Op.effect, put, next,
         Udivti3.compare, Udivti3.next, state_simp_rules, BitVec.ofNat_eq_ofNat,
         BitVec.add_assoc]

def lowOps (a low : BitVec 64) : List Op :=
  [.p3504] ++ if a = 0#64 then [] else
    [.p3508, .p3512, .p3516, .p3520] ++ if a = low then [] else compareOps a low

/-- Only a matching, nonzero significant length authorizes the low-limb read. -/
theorem compare_low (s : ArmState) (base low : BitVec 64)
    (hc : CodeAt s base) (hp : read_pc s = base + 3504#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hcount : r (.GPR 3#5) s ≠ 0#64 → r (.GPR 9#5) s ≠ 0#64)
    (hload : r (.GPR 3#5) s ≠ 0#64 → read_mem_bytes 8 (r (.GPR 8#5) s) s = low) :
    ∃ fuel t, run fuel s = t ∧ WidthFrame s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      read_pc t = if (r (.GPR 3#5) s).toNat ≤ low.toNat then base + 4492#64 else base + 3576#64 := by
  let ops := lowOps (r (.GPR 3#5) s) low
  let t := block base ops s
  have hpc : r .PC s = base + 3504#64 := hp
  have hfollow : Follows base ops s := by
    by_cases hz : r (.GPR 3#5) s = 0#64 <;>
      by_cases heq : r (.GPR 3#5) s = low <;>
      by_cases hle : (r (.GPR 3#5) s).toNat ≤ low.toNat
    all_goals
      try have h9 := hcount hz
      try have hl := hload hz
      try simp only [heq] at hz hle
      try omega
      all_goals simp (config := {decide := true, instances := true})
        [*, ops, lowOps, compareOps, Follows, Op.row, Op.effect, put, next,
         Udivti3.compare, Udivti3.next, state_simp_rules, BitVec.ofNat_eq_ofNat,
         Udivti3.cmp_zero, Udivti3.cmp_carry, BitVec.add_assoc]
      try bv_omega
  refine ⟨ops.length, t, block_run base ops s hc he ha hfollow,
    readonly_frame base ops s ?_, ?_, ?_, ?_⟩
  · dsimp only [ops, lowOps, compareOps]; split <;> (try split) <;> (try split) <;> decide
  all_goals
    by_cases hz : r (.GPR 3#5) s = 0#64 <;>
      by_cases heq : r (.GPR 3#5) s = low <;>
      by_cases hle : (r (.GPR 3#5) s).toNat ≤ low.toNat
    all_goals
      try have h9 := hcount hz
      try have hl := hload hz
      try simp only [heq] at hz hle
      try omega
      all_goals simp (config := {decide := true, instances := true})
        [*, t, ops, lowOps, compareOps, block, Op.effect, put, next,
         Udivti3.compare, Udivti3.next, state_simp_rules, BitVec.ofNat_eq_ofNat,
         Udivti3.cmp_zero, Udivti3.cmp_carry, BitVec.add_assoc]
      try bv_omega

/-- The complete Large continuation composes count, low-word and spill blocks. -/
theorem large_compare (s : ArmState) (base pointer : BitVec 64) (words : List (BitVec 64))
    (hc : CodeAt s base) (hp : read_pc s = scanExit base (sigWords words))
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (h8 : r (.GPR 8#5) s = pointer)
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 words.length)
    (h10 : r (.GPR 10#5) s = if r (.GPR 3#5) s = 0#64 then 0#64 else 1#64)
    (h11 : sigWords words ≠ 0 → r (.GPR 11#5) s = BitVec.ofNat 64 (sigWords words))
    (hs : Source s pointer words) (hm : WidthWords s pointer words) :
    ∃ fuel t, run fuel s = t ∧ WidthFrame s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      read_pc t = if (r (.GPR 3#5) s).toNat ≤ value words then base + 4492#64 else base + 3576#64 := by
  have hlen : words.length < 2^64 := by have := hs.2.1; omega
  have hk : sigWords words < 2^64 := Nat.lt_of_le_of_lt (sigWords_le_length words) hlen
  obtain ⟨fuel, t, ht, hf, ht8, ht9, ht10, htp⟩ := compare_counts s base (sigWords words)
    hc hp he ha hk h10 h11
  have ht3 : r (.GPR 3#5) t = r (.GPR 3#5) s := hf.registers 3#5 (by decide)
  by_cases hequal : sameCount (sigWords words) (r (.GPR 3#5) s)
  · have hpc : read_pc t = base + 3504#64 := by simpa only [hequal, ↓reduceIte] using htp
    have hone : r (.GPR 3#5) t ≠ 0#64 → sigWords words = 1 := by
      intro hn
      rcases hequal with ⟨_, hz⟩ | ⟨hk, _⟩
      · exact False.elim (hn (ht3.trans hz))
      · exact hk
    have hcount : r (.GPR 3#5) t ≠ 0#64 → r (.GPR 9#5) t ≠ 0#64 := by
      intro hn
      have hs1 := hone hn
      have hpos : 0 < words.length := by have := sigWords_le_length words; omega
      rw [ht9, h9]
      bv_omega
    have hload : r (.GPR 3#5) t ≠ 0#64 →
        read_mem_bytes 8 (r (.GPR 8#5) t) t = words[0]?.getD 0#64 := by
      intro hn
      have hs1 := hone hn
      have hpos : 0 < words.length := by have := sigWords_le_length words; omega
      rw [ht8, h8]
      simpa [List.getElem?_eq_getElem hpos] using hf.byteWords pointer words hs hm ⟨0, hpos⟩
    obtain ⟨extra, u, hu, huf, hu8, hu9, hup⟩ := compare_low t base (words[0]?.getD 0#64)
      (by simpa only [CodeAt, hf.program] using hc) hpc (hf.error.trans he) (hf.aligned ha)
      hcount hload
    refine ⟨fuel + extra, u, by rw [run_plus, ht, hu], hf.trans huf,
      hu8.trans ht8, hu9.trans ht9, ?_⟩
    by_cases hz : r (.GPR 3#5) t = 0#64
    · have hzs : r (.GPR 3#5) s = 0#64 := ht3.symm.trans hz
      simpa [hz, hzs] using hup
    · have hv := value_one words (hone hz)
      simpa only [ht3, hv] using hup
  · let reject := decide (sigWords words = 0 ∧ r (.GPR 3#5) s ≠ 0#64)
    let u := spillResult t base false reject
    have hpc : read_pc t = base + 3536#64 := by simpa only [hequal, ↓reduceIte] using htp
    have hsp : r (.GPR 31#5) t = r (.GPR 31#5) s := hf.sp
    have hts : 16 ≤ (r (.GPR 31#5) t).toNat := by
      have hss : 16 ≤ (r (.GPR 31#5) s).toNat := hs.1
      simpa only [hsp] using hss
    have hflag : r (.GPR 10#5) t = if reject then 1#64 else 0#64 := by simpa [reject] using ht10
    have hu : run 7 t = u := spill_run t base false reject
      (by simpa only [CodeAt, hf.program] using hc) (hf.error.trans he) (hf.aligned ha)
      hpc hts hflag
    refine ⟨fuel + 7, u, by rw [run_plus, ht, hu], hf.trans (spill_frame t base false reject hts),
      (spill_register t base false reject 8#5).trans ht8,
      (spill_register t base false reject 9#5).trans ht9, ?_⟩
    simp only [u, spill_pc, spillTarget, Bool.false_eq_true, ↓reduceIte]
    by_cases hk0 : sigWords words = 0
    · have hz : r (.GPR 3#5) s ≠ 0#64 := by intro hz; exact hequal (Or.inl ⟨hk0, hz⟩)
      have hv := value_zero words hk0
      simp [reject, hk0, hz, hv]
      bv_omega
    · by_cases hk1 : sigWords words = 1
      · have hz : r (.GPR 3#5) s = 0#64 := by
          by_cases hn : r (.GPR 3#5) s = 0#64
          · exact hn
          · exact False.elim (hequal (Or.inr ⟨hk1, hn⟩))
        simp [reject, hk0, hz]
      · have hv := value_many words (by omega : 1 < sigWords words)
        have hle : (r (.GPR 3#5) s).toNat ≤ value words := by have := (r (.GPR 3#5) s).isLt; omega
        simp [reject, hk0, hle]

end SszArm.ByteView.Bounded
