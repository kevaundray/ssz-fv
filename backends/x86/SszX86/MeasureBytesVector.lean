import SszX86.MeasureBytesState

namespace SszX86.Measure.Bytes
open Kraken.X64.Parser UintCodec SszNative.Limbs

theorem vector_pair (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c lo hi t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (state s a c hi ((lo ^^^ s.regs.rax.toBitVec) ||| hi) t flags,
       if ((lo ^^^ s.regs.rax.toBitVec) ||| hi) = 0#64 then base + 3050 else base + 3095)) :
    Eventually (step e) P (state s a c hi lo t flags, base + 3042) := by
  have target := hc.targets ("measure_u3095", 3095) (by decide)
  measure_bytes_step 432 using hc
  constructor <;> measure_bytes_step 433 using hc
  all_goals constructor <;> measure_bytes_step 434 using hc
  all_goals
    by_cases hz : ((lo ^^^ s.regs.rax.toBitVec) ||| hi) = 0#64
    · have he : lo = s.regs.rax.toBitVec ∧ hi = 0#64 := by simpa using hz
      simpa [StatusFlags.from_result, he.1, he.2, state, Effects.All] using hp _
    · have he : lo = s.regs.rax.toBitVec → hi ≠ 0#64 := by
        intro hlo hhi
        exact hz (by simp [hlo, hhi])
      have hw : UInt64.ofBitVec ((lo ^^^ s.regs.rax.toBitVec) ||| hi) =
          (UInt64.ofBitVec lo ^^^ s.regs.rax) ||| UInt64.ofBitVec hi := by
        apply UInt64.toBitVec_inj.1
        simp
      simpa [target, StatusFlags.from_result, he, hz, state, hw, Effects.All] using hp _

theorem vector_small (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si x t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (state s a c 0#64 c t flags, base + 3042)) :
    Eventually (step e) P (state s a c si x t flags, base + 1662) := by
  measure_bytes_step 219 using hc
  constructor <;> measure_bytes_step 220 using hc
  all_goals measure_bytes_step 221 using hc
  all_goals simpa [state] using hp _

theorem vector_empty (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si x t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (state s a c 0#64 0#64 t flags, base + 3042)) :
    Eventually (step e) P (state s a c si x t flags, base + 3038) := by
  measure_bytes_step 430 using hc
  constructor <;> measure_bytes_step 431 using hc
  all_goals constructor
  all_goals simpa [state] using hp _

theorem vector_one_hi (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si x t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (state s a c 0#64 x t flags, base + 3042)) :
    Eventually (step e) P (state s a c si x t flags, base + 2670) := by
  measure_bytes_step 343 using hc
  constructor <;> measure_bytes_step 344 using hc
  all_goals simpa [state] using hp _

/-- Low-word loading uses the *stored* length: a redundant second zero word
is still read when the significant count is only zero or one. -/
theorem vector_low_words (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a si x t : BitVec 64) (flags : StatusFlags)
    (words : List (BitVec 64)) (hn : words ≠ []) (hb : words.length < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8 * i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (state s a (BitVec.ofNat 64 words.length) (words[1]?.getD 0#64)
        (words[0]?.getD 0#64) t flags, base + 3042)) :
    Eventually (step e) P
      (state s a (BitVec.ofNat 64 words.length) si x t flags, base + 1894) := by
  have target := hc.targets ("measure_u2670", 2670) (by decide)
  have hpos : 0 < words.length := by cases words <;> simp_all
  have h0 := hm ⟨0, hpos⟩
  have h0' : Mem.loadInt s.dmem a 8 = some ((words[0]?.getD 0#64).toNat : Int) := by
    simpa [List.getElem?_eq_getElem hpos] using h0
  measure_bytes_step 266 using hc
  measure_bytes_load h0'
  measure_bytes_step 267 using hc
  measure_bytes_step 268 using hc
  by_cases htwo : words.length < 2
  · simp [StatusFlags.from_result, Nat.mod_eq_of_lt hb, htwo, target, Effects.All]
    apply vector_one_hi e base hc
    intro fl
    have h1 : words[1]?.getD 0#64 = 0#64 := by
      rw [List.getElem?_eq_none (by omega)]
      rfl
    simpa [h1] using hp fl
  · simp [StatusFlags.from_result, Nat.mod_eq_of_lt hb, htwo, Effects.All]
    have h1 := hm ⟨1, by omega⟩
    have h1' : Mem.loadInt s.dmem (a + 8#64) 8 = some ((words[1]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show 1 < words.length by omega)] using h1
    measure_bytes_step 269 using hc
    measure_bytes_load h1'
    measure_bytes_step 270 using hc
    simpa [state] using hp _

theorem vector_zero_count (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si x t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (state s a c si x t flags, if c = 0#64 then base + 3038 else base + 1894)) :
    Eventually (step e) P (state s a c si x t flags, base + 1885) := by
  have target := hc.targets ("measure_u3038", 3038) (by decide)
  measure_bytes_step 264 using hc
  constructor <;> measure_bytes_step 265 using hc
  all_goals
    by_cases hz : c = 0#64
    · simpa [target, StatusFlags.from_result, hz, state, Effects.All] using hp _
    · simpa [StatusFlags.from_result, hz, state, Effects.All] using hp _

/-- One descent reads exactly `words[n]`. The index/range assumptions below
are ordinary mapped-memory and no-wrap conditions, not execution hypotheses. -/
theorem vector_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c x t limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (hb : n + 2 < 2^64)
    (hm : Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*n)) 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (hzero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (state s a c (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) t flags, base + 576))
    (hnonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (state s a c (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) t flags,
        if n+1 < 3 then base + 1894 else base + 3095)) :
    Eventually (step e) P
      (state s a c (BitVec.ofNat 64 (n+2)) x t flags, base + 576) := by
  have target1 := hc.targets ("measure_u576", 576) (by decide)
  have target2 := hc.targets ("measure_u1894", 1894) (by decide)
  have hz : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have hsi : (OfNat.ofNat (n+2) : UInt64) + OfNat.ofNat 18446744073709551615 =
      OfNat.ofNat (n+1) := by
    apply UInt64.toBitVec_inj.1
    change BitVec.ofNat 64 (n+2) + 18446744073709551615#64 = BitVec.ofNat 64 (n+1)
    bv_omega
  have haddr : a + BitVec.ofNat 64 (n+2) * 8#64 + 18446744073709551600#64 =
      a + BitVec.ofNat 64 (8*n) := by
    bv_omega
  measure_bytes_step 48 using hc
  measure_bytes_step 49 using hc
  simp [StatusFlags.from_result, hz, Effects.All]
  measure_bytes_step 50 using hc
  rw [hsi]
  measure_bytes_step 51 using hc
  rw [haddr]
  measure_bytes_load hm
  measure_bytes_step 52 using hc
  measure_bytes_step 53 using hc
  by_cases hw : limb = 0#64
  · simpa [target1, StatusFlags.from_result, hw, state, Effects.All] using hzero hw _
  · simp [StatusFlags.from_result, hw, Effects.All]
    measure_bytes_step 54 using hc
    measure_bytes_step 55 using hc
    by_cases hsmall : n+1 < 3
    · simpa [target2, StatusFlags.from_result,
        Nat.mod_eq_of_lt (show n+1 < 2^64 by omega), hsmall, Effects.All, state]
        using hnonzero hw _
    · simp [StatusFlags.from_result, Nat.mod_eq_of_lt (show n+1 < 2^64 by omega),
        hsmall, Effects.All]
      measure_bytes_step 56 using hc
      simpa [hsmall, state] using hnonzero hw _

/-- Complete descending high-limb scan, with the same countdown as
`SszLimbOrder.significantCount`. Zero limbs may be arbitrarily redundant. -/
theorem vector_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c t : BitVec 64) (words : List (BitVec 64))
    (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ x flags,
    (SszNative.Limbs.significantCount words n = 0 → ∀ si x flags,
      Eventually (step e) P (state s a c si x t flags, base + 1885)) →
    (0 < SszNative.Limbs.significantCount words n →
      SszNative.Limbs.significantCount words n ≤ 2 → ∀ si x flags,
      Eventually (step e) P (state s a c si x t flags, base + 1894)) →
    (2 < SszNative.Limbs.significantCount words n → ∀ si x flags,
      Eventually (step e) P (state s a c si x t flags, base + 3095)) →
    Eventually (step e) P (state s a c (BitVec.ofNat 64 (n+1)) x t flags, base + 576) := by
  intro n
  induction n with
  | zero =>
    intro hn x flags hzero hfew hmany
    have target := hc.targets ("measure_u1885", 1885) (by decide)
    measure_bytes_step 48 using hc
    measure_bytes_step 49 using hc
    simpa [target, StatusFlags.from_result, state, Effects.All] using hzero rfl 1#64 x _
  | succ n ih =>
    intro hn x flags hzero hfew hmany
    have hload := hm ⟨n, by omega⟩
    have hload' : Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hload
    apply vector_scan_step e base hc s a c x t (words[n]?.getD 0#64) flags n (by omega) hload' P
    · intro hz fl
      apply ih (by omega) _ fl
      · intro he
        apply hzero
        simpa [SszNative.Limbs.significantCount, hz] using he
      · intro hp he
        apply hfew
        · simpa [SszNative.Limbs.significantCount, hz] using hp
        · simpa [SszNative.Limbs.significantCount, hz] using he
      · intro he
        apply hmany
        simpa [SszNative.Limbs.significantCount, hz] using he
    · intro hz fl
      have hsig : SszNative.Limbs.significantCount words (n+1) = n+1 := by
        simp [SszNative.Limbs.significantCount, hz]
      by_cases hs : n+1 < 3
      · simp only [hs, ↓reduceIte]
        exact hfew (by omega) (by omega) _ _ fl
      · simp only [hs, ↓reduceIte]
        exact hmany (by omega) _ _ fl

/-- The entire Large branch, including the empty-slice path and both low-word
loads after an all-zero scan. No canonicality assumption is imposed. -/
theorem vector_large (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a si x t : BitVec 64) (flags : StatusFlags)
    (words : List (BitVec 64)) (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop)
    (hyes : SszNative.Limbs.value words = s.regs.rax.toNat → ∀ si flags,
      Eventually (step e) P
        (state s a (BitVec.ofNat 64 words.length)
          si 0#64 t flags, base + 3050))
    (hno : SszNative.Limbs.value words ≠ s.regs.rax.toNat → ∀ si x flags,
      Eventually (step e) P
        (state s a (BitVec.ofNat 64 words.length) si x t flags, base + 3095)) :
    Eventually (step e) P
      (state s a (BitVec.ofNat 64 words.length) si x t flags, base + 558) := by
  have pair (hfew : SszNative.Limbs.sigWords words ≤ 2) (fl : StatusFlags) :
      Eventually (step e) P
        (state s a (BitVec.ofNat 64 words.length) (words[1]?.getD 0#64)
          (words[0]?.getD 0#64) t fl, base + 3042) := by
    apply vector_pair e base hc
    intro flags'
    by_cases he : (((words[0]?.getD 0#64) ^^^ s.regs.rax.toBitVec) |||
        words[1]?.getD 0#64) = 0#64
    · simpa only [he, ↓reduceIte] using
        hyes ((width_pair_eq words s.regs.rax.toBitVec hfew).mp he) _ flags'
    · simpa only [he, ↓reduceIte] using
        hno (fun h => he ((width_pair_eq words s.regs.rax.toBitVec hfew).mpr h)) _ _ flags'
  have low (hn : words ≠ []) (hfew : SszNative.Limbs.sigWords words ≤ 2)
      (si x : BitVec 64) (fl : StatusFlags) :
      Eventually (step e) P
        (state s a (BitVec.ofNat 64 words.length) si x t fl, base + 1894) :=
    vector_low_words e base hc s a si x t fl words hn (by omega) hm P (pair hfew)
  have loop (fl : StatusFlags) : Eventually (step e) P
      (state s a (BitVec.ofNat 64 words.length)
        (BitVec.ofNat 64 (words.length+1)) x t fl, base + 576) := by
    apply vector_scan e base hc s a (BitVec.ofNat 64 words.length) t words hb hm P
      words.length (Nat.le_refl _) x fl
    · intro hz si' x' fl'
      apply vector_zero_count e base hc
      intro fl''
      by_cases hn : words = []
      · subst words
        change Eventually (step e) P (state s a 0#64 si' x' t fl'', base + 3038)
        apply vector_empty e base hc
        intro fl'''
        simpa using pair (by simp [SszNative.Limbs.sigWords, SszNative.Limbs.significantCount]) fl'''
      · have hc0 : BitVec.ofNat 64 words.length ≠ 0#64 := by
          intro he
          have hlen := congrArg BitVec.toNat he
          simp only [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show words.length < 2^64 by omega)] at hlen
          have hpos : 0 < words.length := by cases words <;> simp_all
          omega
        simp only [hc0, ↓reduceIte]
        exact low hn (by change SszNative.Limbs.significantCount words words.length ≤ 2; omega)
          si' x' fl''
    · intro hpos hfew si' x' fl'
      have hn : words ≠ [] := by
        intro he
        subst words
        simp [SszNative.Limbs.significantCount] at hpos
      exact low hn hfew si' x' fl'
    · intro hmany si' x' fl'
      exact hno (width_many_ne words s.regs.rax.toBitVec hmany) si' x' fl'
  have hlea : (OfNat.ofNat words.length : UInt64) + OfNat.ofNat 1 =
      OfNat.ofNat (words.length+1) := by
    apply UInt64.toBitVec_inj.1
    change BitVec.ofNat 64 words.length + 1#64 = BitVec.ofNat 64 (words.length+1)
    rw [BitVec.ofNat_add]
  measure_bytes_step 45 using hc
  measure_bytes_step 46 using hc
  measure_bytes_step 47 using hc
  simpa [state, hlea] using loop flags

end SszX86.Measure.Bytes
