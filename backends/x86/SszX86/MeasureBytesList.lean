import SszX86.MeasureBytesListOps

namespace SszX86.Measure.Bytes
open Kraken.X64.Parser UintCodec SszNative.Limbs

def list_nz (s : MachineData) : Nat := if s.regs.rax.toBitVec = 0#64 then 0 else 1

theorem list_choice (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c x y : BitVec 64) (fl : StatusFlags) (b : Bool)
    (P : MachineState → Prop)
    (hp : ∀ fl, Eventually (step e) P
      (state s a c (if b then 1#64 else 0#64) x y fl,
        if b then base + 2252 else base + 3050)) :
    Eventually (step e) P
      (state s a c (if b then 1#64 else 0#64) x y fl, base + 1963) := by
  have reject := hc.targets ("measure_u2252", 2252) (by decide)
  cases b
  · measure_bytes_step 283 using hc
    constructor <;> measure_bytes_step 284 using hc
    all_goals simp [StatusFlags.from_result, Effects.All]
    all_goals measure_bytes_step 285 using hc
    all_goals simpa [state] using hp _
  · measure_bytes_step 283 using hc
    constructor <;> measure_bytes_step 284 using hc
    all_goals simpa [reject, StatusFlags.from_result, state, Effects.All] using hp _

theorem list_count_nonzero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c x : BitVec 64) (fl : StatusFlags) (n : Nat)
    (hn : 0 < n) (hb : n < 2^64)
    (P : MachineState → Prop)
    (hp : ∀ si x y fl, Eventually (step e) P
      (state s a c si x y fl,
        if n = list_nz s then base + 1928 else base + 3050)) :
    Eventually (step e) P
      (state s a c (BitVec.ofNat 64 (list_nz s)) x (BitVec.ofNat 64 n) fl, base + 1919) := by
  have target := hc.targets ("measure_u1963", 1963) (by decide)
  measure_bytes_step 272 using hc
  measure_bytes_step 273 using hc
  measure_bytes_step 274 using hc
  by_cases hz : s.regs.rax.toBitVec = 0#64
  · have hnz : BitVec.ofNat 64 n ≠ 0#64 := by bv_omega
    simp [list_nz, hz, StatusFlags.from_result, Nat.mod_eq_of_lt hb, hnz, target, Effects.All]
    apply list_choice e base hc _ _ _ _ _ _ false
    intro fl'
    simpa [list_nz, hz, Nat.ne_of_gt hn, state] using hp 0#64 x (BitVec.ofNat 64 n) fl'
  · by_cases he : n = 1
    · subst n
      simpa [list_nz, hz, StatusFlags.from_result, state, Effects.All] using hp 0#64 x 1#64 _
    · have hnz : BitVec.ofNat 64 n ≠ 1#64 := by bv_omega
      have hnot : ¬ n < 1 := by omega
      simp [list_nz, hz, StatusFlags.from_result, Nat.mod_eq_of_lt hb, hnz, hnot, target, Effects.All]
      apply list_choice e base hc _ _ _ _ _ _ false
      intro fl'
      simpa [list_nz, hz, he, state] using hp 0#64 x (BitVec.ofNat 64 n) fl'

theorem list_count_zero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c x y : BitVec 64) (fl : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ si x y fl, Eventually (step e) P
      (state s a c si x y fl,
        if s.regs.rax.toBitVec = 0#64 then base + 1928 else base + 2252)) :
    Eventually (step e) P
      (state s a c (BitVec.ofNat 64 (list_nz s)) x y fl, base + 1916) := by
  have target := hc.targets ("measure_u1963", 1963) (by decide)
  have zeroSet : (0#56 ++ BitVec.ofNat 8 ((0#64).unsigned != 0).toNat) = 0#64 := by decide
  measure_bytes_step 271 using hc
  constructor <;> measure_bytes_step 272 using hc
  all_goals measure_bytes_step 273 using hc
  all_goals measure_bytes_step 274 using hc
  all_goals
    by_cases hz : s.regs.rax.toBitVec = 0#64
    · simpa [list_nz, hz, StatusFlags.from_result, zeroSet, state, Effects.All]
        using hp 0#64 x 0#64 _
    · simp [list_nz, hz, target, StatusFlags.from_result, Effects.All]
      apply list_choice e base hc _ _ _ _ _ _ true
      intro fl'
      simpa [hz, state] using hp 1#64 x 0#64 fl'

theorem list_equal_count (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a : BitVec 64) (words : List (BitVec 64))
    (si x y : BitVec 64) (fl : StatusFlags)
    (hb : words.length < 2^64)
    (he : sigWords words = list_nz s)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ si x y fl, Eventually (step e) P
      (state s a (BitVec.ofNat 64 words.length) si x y fl,
        if s.regs.rax.toNat ≤ value words then base + 3050 else base + 2252)) :
    Eventually (step e) P
      (state s a (BitVec.ofNat 64 words.length) si x y fl, base + 1928) := by
  have target := hc.targets ("measure_u3050", 3050) (by decide)
  have reject := hc.targets ("measure_u2252", 2252) (by decide)
  have scalarTarget := hc.targets ("measure_u2243", 2243) (by decide)
  measure_bytes_step 275 using hc
  constructor <;> measure_bytes_step 276 using hc
  all_goals
    by_cases hz : s.regs.rax.toBitVec = 0#64
    · have hzero : s.regs.rax.toNat = 0 := by simpa using congrArg BitVec.toNat hz
      simpa [target, StatusFlags.from_result, hz, hzero, state, Effects.All] using hp _ _ _ _
    · simp [StatusFlags.from_result, hz, Effects.All]
      have hs : sigWords words = 1 := by simpa [list_nz, hz] using he
      have hpos : 0 < words.length := by have := sigWords_le_length words; omega
      have hc0 : BitVec.ofNat 64 words.length ≠ 0#64 := by bv_omega
      have hv : value words = (words[0]?.getD 0#64).toNat := by
        rw [← trim_value words, trim_eq_take, hs]
        cases words <;> simp [value]
      measure_bytes_step 277 using hc
      constructor <;> measure_bytes_step 278 using hc
      all_goals simp [StatusFlags.from_result, hc0, Effects.All]
      all_goals measure_bytes_step 279 using hc
      all_goals
        have hload : Mem.loadInt s.dmem a 8 = some ((words[0]?.getD 0#64).toNat : Int) := by
          simpa [List.getElem?_eq_getElem hpos] using hm ⟨0, hpos⟩
        measure_bytes_load hload
        measure_bytes_step 280 using hc
        measure_bytes_step 281 using hc
        by_cases heq : s.regs.rax.toBitVec = words[0]?.getD 0#64
        · simp [StatusFlags.from_result, heq, Effects.All]
          measure_bytes_step 282 using hc
          have hle : s.regs.rax.toNat ≤ value words := by
            rw [hv, ← heq]
            exact Nat.le_refl _
          simpa [hle, state] using hp _ _ _ _
        · simp [scalarTarget, StatusFlags.from_result, heq, Effects.All]
          apply list_scalar e base hc
          intro fl'
          simpa [hv, state] using hp _ _ _ fl'

/-- The nonzero scan edge is a real relative JMP, not a named-label premise. -/
theorem list_scan_exit (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (step e) P (s, base + 1919)) :
    Eventually (step e) P (s, base + 697) := by
  measure_bytes_step 77 using hc
  exact hp

theorem list_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si y limb : BitVec 64) (fl : StatusFlags)
    (n : Nat) (hb : n + 2 < 2^64)
    (hm : Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*n)) 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ fl, Eventually (step e) P
      (state s a c si (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) fl,
        if limb = 0#64 then base + 672 else base + 1919)) :
    Eventually (step e) P
      (state s a c si (BitVec.ofNat 64 (n+2)) y fl, base + 672) := by
  have target := hc.targets ("measure_u672", 672) (by decide)
  have hz : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have hpred : (OfNat.ofNat (n+2) : UInt64) + OfNat.ofNat 18446744073709551615 =
      OfNat.ofNat (n+1) := by
    apply UInt64.toBitVec_inj.1
    change BitVec.ofNat 64 (n+2) + 18446744073709551615#64 = BitVec.ofNat 64 (n+1)
    bv_omega
  have haddr : a + BitVec.ofNat 64 (n+2) * 8#64 + 18446744073709551600#64 =
      a + BitVec.ofNat 64 (8*n) := by
    bv_omega
  have nonzero (h : limb ≠ 0#64) (flags : StatusFlags) :
      Eventually (step e) P
        (state s a c si (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags,
          base + 697) := by
    apply list_scan_exit e base hc
    simpa only [h, ↓reduceIte] using hp flags
  measure_bytes_step 71 using hc
  measure_bytes_step 72 using hc
  simp [StatusFlags.from_result, hz, Effects.All]
  measure_bytes_step 73 using hc
  rw [hpred]
  measure_bytes_step 74 using hc
  rw [haddr]
  measure_bytes_load hm
  measure_bytes_step 75 using hc
  measure_bytes_step 76 using hc
  by_cases h : limb = 0#64
  · simpa [target, StatusFlags.from_result, h, state, Effects.All] using hp _
  · simpa [StatusFlags.from_result, h, state, Effects.All] using nonzero h _

theorem list_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si : BitVec 64) (words : List (BitVec 64))
    (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ y fl,
    (significantCount words n = 0 → ∀ x y fl,
      Eventually (step e) P (state s a c si x y fl, base + 1916)) →
    (∀ k, significantCount words n = k → 0 < k → ∀ x fl,
      Eventually (step e) P (state s a c si x (BitVec.ofNat 64 k) fl, base + 1919)) →
    Eventually (step e) P
      (state s a c si (BitVec.ofNat 64 (n+1)) y fl, base + 672) := by
  intro n
  induction n with
  | zero =>
    intro hn y fl hzero hpos
    have target := hc.targets ("measure_u1916", 1916) (by decide)
    measure_bytes_step 71 using hc
    measure_bytes_step 72 using hc
    simpa [target, StatusFlags.from_result, state, Effects.All] using hzero rfl 1#64 y _
  | succ n ih =>
    intro hn y fl hzero hpos
    have hload := hm ⟨n, by omega⟩
    have hload' : Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hload
    apply list_scan_step e base hc s a c si y (words[n]?.getD 0#64) fl n (by omega) hload' P
    intro fl'
    by_cases hz : words[n]?.getD 0#64 = 0#64
    · simp only [hz, ↓reduceIte]
      apply ih (by omega) _ fl'
      · intro he
        apply hzero
        simpa [significantCount, hz] using he
      · intro k he hk
        apply hpos k
        · simpa [significantCount, hz] using he
        · exact hk
    · simp only [hz, ↓reduceIte]
      exact hpos (n+1) (by simp [significantCount, hz]) (by omega) _ fl'

theorem list_value_zero (words : List (BitVec 64)) (h : sigWords words = 0) :
    value words = 0 := by
  rw [← trim_value words, trim_eq_take, h]
  rfl

theorem list_value_many (s : MachineData) (words : List (BitVec 64)) (h : 1 < sigWords words) :
    s.regs.rax.toNat ≤ value words := by
  have hh := canonical_length_lt (xs := [s.regs.rax.toBitVec])
    (trim_canonical words) (by simpa only [List.length_cons, List.length_nil, trim_length] using h)
  simp only [value, Nat.mul_zero, Nat.add_zero, trim_value] at hh
  exact Nat.le_of_lt hh

theorem list_large (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a y : BitVec 64) (fl : StatusFlags) (words : List (BitVec 64))
    (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ si x y fl, Eventually (step e) P
      (state s a (BitVec.ofNat 64 words.length) si x y fl,
        if s.regs.rax.toNat ≤ value words then base + 3050 else base + 2252)) :
    Eventually (step e) P
      (state s a (BitVec.ofNat 64 words.length) (BitVec.ofNat 64 (list_nz s))
        (BitVec.ofNat 64 (words.length+1)) y fl, base + 672) := by
  apply list_scan e base hc s a (BitVec.ofNat 64 words.length) (BitVec.ofNat 64 (list_nz s))
    words hb hm P words.length (Nat.le_refl _) y fl
  · intro hz x y fl'
    change sigWords words = 0 at hz
    have hv := list_value_zero words hz
    apply list_count_zero e base hc
    intro si x y fl''
    by_cases hs : s.regs.rax.toBitVec = 0#64
    · simp only [hs, ↓reduceIte]
      apply list_equal_count e base hc s a words si x y fl'' (by omega)
        (by simpa [list_nz, hs] using hz) hm P hp
    · have hpos : 0 < s.regs.rax.toNat := by
        have hne : s.regs.rax.toNat ≠ 0 := by
          intro he
          exact hs (BitVec.eq_of_toNat_eq he)
        omega
      simpa only [hs, ↓reduceIte, hv, Nat.not_le_of_gt hpos] using hp si x y fl''
  · intro k hk hpos x fl'
    change sigWords words = k at hk
    have hkle : k ≤ words.length := by rw [← hk]; exact sigWords_le_length words
    apply list_count_nonzero e base hc s a (BitVec.ofNat 64 words.length) x fl' k hpos (by omega)
    intro si x y fl''
    by_cases he : k = list_nz s
    · simp only [he, ↓reduceIte]
      exact list_equal_count e base hc s a words si x y fl'' (by omega) (hk.trans he) hm P hp
    · have hle : s.regs.rax.toNat ≤ value words := by
        by_cases hs : s.regs.rax.toBitVec = 0#64
        · have hzero : s.regs.rax.toNat = 0 := by simpa using congrArg BitVec.toNat hs
          simp [hzero]
        · have hk1 : k ≠ 1 := by simpa [list_nz, hs] using he
          apply list_value_many s words
          omega
      simpa only [he, ↓reduceIte, hle] using hp si x y fl''

end SszX86.Measure.Bytes
