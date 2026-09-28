import SszX86.NatToU128Scan
import SszNatNarrow

namespace SszX86.NatToU128
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

structure ReadFrame (s t : MachineData) : Prop where
  memory : t.dmem = s.dmem
  vectors : t.zmms = s.zmms
  registers : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 →
    t.regs.get64 r = s.regs.get64 r

theorem ReadFrame.trans {s t u : MachineData} (first : ReadFrame s t)
    (second : ReadFrame t u) : ReadFrame s u := by
  refine ⟨second.memory.trans first.memory, second.vectors.trans first.vectors, ?_⟩
  intro r ha hc hd hx
  exact (second.registers r ha hc hd hx).trans (first.registers r ha hc hd hx)

theorem status_frame (s : MachineData) (flags : StatusFlags) :
    ReadFrame s {s with status := flags} := ⟨rfl, rfl, by intros; rfl⟩

theorem scan_frame (s : MachineData) (a x : BitVec 64) (flags : StatusFlags) :
    ReadFrame s (scanState s a x flags) := by
  refine ⟨rfl, rfl, ?_⟩
  intro r ha hc hd hx
  cases r <;> simp_all [scanState, Reg64s.get64]

def resultState (s : MachineData) (a c d : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec a, rcx := UInt64.ofBitVec c, rdx := UInt64.ofBitVec d}
    status := flags}

theorem result_frame (s : MachineData) (a c d : BitVec 64) (flags : StatusFlags) :
    ReadFrame s (resultState s a c d flags) := by
  refine ⟨rfl, rfl, ?_⟩
  intro r ha hc hd hx
  cases r <;> simp_all [resultState, Reg64s.get64]

/-- The shared native shift/OR characterization determines both published halves. -/
private theorem wide_parts (operand : NatOperand) (fits : operand.wordCount ≤ 2) :
    (SszNative.NatDivision.wideValue operand).setWidth 64 = operand.words[0]?.getD 0 ∧
      ((SszNative.NatDivision.wideValue operand) >>> (64 : Nat)).setWidth 64 =
        operand.words[1]?.getD 0 := by
  let lo := operand.words[0]?.getD 0
  let hi := operand.words[1]?.getD 0
  have hlo := lo.isLt
  have hhi := hi.isLt
  have shiftBound : hi.toNat <<< 64 < 2^128 := by
    rw [Nat.shiftLeft_eq]
    omega
  have valueNat : (SszNative.NatDivision.wideValue operand).toNat =
      lo.toNat + 2^64 * hi.toNat := by
    rw [SszNative.NatDivision.wideValue_native operand fits]
    change ((lo.setWidth 128 ||| (hi.setWidth 128 <<< (64 : Nat))) : BitVec 128).toNat = _
    simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth_of_le (show 64 ≤ 128 by decide), Nat.mod_eq_of_lt shiftBound]
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlo hi.toNat]
    rw [Nat.shiftLeft_eq]
    omega
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, valueNat]
    change (lo.toNat + 2^64 * hi.toNat) % 2^64 = lo.toNat
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, valueNat]
    change ((lo.toNat + 2^64 * hi.toNat) / 2^64) % 2^64 = hi.toNat
    omega

theorem entry_dispatch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rsi.toBitVec = 0 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 58))
    (large : s.regs.rsi.toBitVec ≠ 0 → ∀ flags, Eventually (step e) P
      (scanState s (s.regs.rdx.toBitVec + 1) s.regs.r8.toBitVec flags, base + 16)) :
    Eventually (step e) P (s, base) := by
  have target := hc.targets ("natToU128_u58", 58) (by decide)
  rw [← show base + Int64.ofNat 0 = base by simp]
  natu128_step 0 using hc
  constructor <;> natu128_step 1 using hc
  all_goals
    by_cases hz : s.regs.rsi.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using small hz _
    · simp [StatusFlags.from_result, hz, Effects.All]
      natu128_step 2 using hc
      simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
      natu128_step 3 using hc
      simpa [scanState] using large hz _

theorem immediate_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (resultState s 0 s.regs.rcx.toBitVec s.regs.rdx.toBitVec flags, base + 96)) :
    Eventually (step e) P (s, base + 58) := by
  natu128_step 17 using hc
  constructor <;> natu128_step 18 using hc
  all_goals simpa [resultState] using next _

theorem empty_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (resultState s 0 s.regs.rcx.toBitVec 0 flags, base + 96)) :
    Eventually (step e) P (s, base + 92) := by
  natu128_step 30 using hc
  constructor <;> natu128_step 31 using hc
  all_goals constructor <;> simpa [resultState] using next _

/-- Physical length, rather than significant width, selects the second load. -/
theorem borrowed_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (lo hi : BitVec 64)
    (hlo : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (lo.toNat : Int))
    (hhi : 2 ≤ s.regs.rdx.toBitVec.toNat →
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (hi.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (resultState s (if s.regs.rdx.toBitVec.toNat < 2 then 0 else hi) lo lo flags,
        base + 96)) :
    Eventually (step e) P (s, base + 67) := by
  have target := hc.targets ("natToU128_u85", 85) (by decide)
  natu128_step 21 using hc
  natu128_load hlo
  natu128_step 22 using hc
  natu128_step 23 using hc
  by_cases short : s.regs.rdx.toBitVec.toNat < 2
  · have branch : s.regs.rdx.toNat < 2 := short
    simp only [branch, target]
    natu128_step 27 using hc
    constructor <;> natu128_step 28 using hc
    all_goals natu128_step 29 using hc
    all_goals simpa [resultState, branch] using next _
  · have branch : ¬s.regs.rdx.toNat < 2 := short
    simp only [branch]
    natu128_step 24 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
    natu128_load (hhi (by omega))
    natu128_step 25 using hc
    natu128_step 26 using hc
    simpa [resultState, branch] using next _

theorem zero_dispatch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (empty : s.regs.rdx.toBitVec = 0 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 92))
    (nonempty : s.regs.rdx.toBitVec ≠ 0 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 67)) :
    Eventually (step e) P (s, base + 62) := by
  have target := hc.targets ("natToU128_u92", 92) (by decide)
  natu128_step 19 using hc
  constructor <;> natu128_step 20 using hc
  all_goals
    by_cases hz : s.regs.rdx.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using empty hz _
    · simpa [StatusFlags.from_result, hz, Effects.All] using nonempty hz _

/-- Failure publishes nothing yet: both zero discriminant halves are prepared. -/
theorem count_dispatch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.r8.toBitVec.toNat < 3 → ∀ flags, Eventually (step e) P
      (resultState s 0 0 s.regs.rdx.toBitVec flags, base + 67))
    (large : 3 ≤ s.regs.r8.toBitVec.toNat → ∀ flags, Eventually (step e) P
      (resultState s 0 0 s.regs.rdx.toBitVec flags, base + 50)) :
    Eventually (step e) P (s, base + 37) := by
  have target := hc.targets ("natToU128_u67", 67) (by decide)
  natu128_step 10 using hc
  constructor <;> natu128_step 11 using hc
  all_goals natu128_step 12 using hc
  all_goals natu128_step 13 using hc
  all_goals
    by_cases hs : s.regs.r8.toNat < 3
    · simpa [StatusFlags.from_result, Udivti3.cf_sub, hs, target, resultState, Effects.All]
        using small hs _
    · have count : 3 ≤ s.regs.r8.toBitVec.toNat := by
        change 3 ≤ s.regs.r8.toNat
        omega
      simpa [StatusFlags.from_result, Udivti3.cf_sub, hs, resultState, Effects.All]
        using large count _

private theorem large_read (s : MachineData) (pointer : BitVec 64) (words : List (BitVec 64))
    (stored : (NatOperand.large pointer words).At (widthLoad s.dmem))
    (i : Nat) (hi : i < words.length) :
    Mem.loadInt s.dmem (pointer + BitVec.ofNat 64 (8*i)) 8 =
      some ((words[i]?.getD 0).toNat : Int) := by
  have h := stored.2.2.2 ⟨i, hi⟩
  change widthLoad s.dmem (pointer.toNat + 8*i) 8 = some words[i].toNat at h
  simpa only [List.getElem?_eq_getElem hi, Option.getD_some, width_address] using
    widthLoad_eq s.dmem _ _ _ h

private theorem length_bits (pointer : BitVec 64) (words : List (BitVec 64))
    (s : MachineData) (stored : (NatOperand.large pointer words).At (widthLoad s.dmem)) :
    (BitVec.ofNat 64 words.length).toNat = words.length := by
  have bound := stored.2.2.1
  exact Nat.mod_eq_of_lt (by omega)

theorem prepare_borrowed_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer : BitVec 64) (words : List (BitVec 64))
    (hp : s.regs.rsi.toBitVec = pointer)
    (hn : s.regs.rdx.toBitVec = BitVec.ofNat 64 words.length)
    (stored : (NatOperand.large pointer words).At (widthLoad s.dmem))
    (nonempty : 0 < words.length) (P : MachineState → Prop)
    (next : ∀ t, ReadFrame s t → t.regs.rax.toBitVec = words[1]?.getD 0 →
      t.regs.rdx.toBitVec = words[0]?.getD 0 → Eventually (step e) P (t, base + 96)) :
    Eventually (step e) P (s, base + 67) := by
  have lengthNat : s.regs.rdx.toBitVec.toNat = words.length := by
    rw [hn, length_bits pointer words s stored]
  apply borrowed_cps e base hc s (words[0]?.getD 0) (words[1]?.getD 0)
  · simpa only [hp, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      large_read s pointer words stored 0 nonempty
  · intro two
    simpa only [hp] using large_read s pointer words stored 1 (by omega)
  intro flags
  apply next
  · exact result_frame s _ _ _ flags
  · change (if s.regs.rdx.toBitVec.toNat < 2 then 0 else words[1]?.getD 0) = words[1]?.getD 0
    by_cases short : s.regs.rdx.toBitVec.toNat < 2
    · rw [ite_eq_left short, List.getElem?_eq_none (by omega)]
      rfl
    · exact ite_eq_right short
  · rfl

theorem prepare_zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer : BitVec 64) (words : List (BitVec 64))
    (hp : s.regs.rsi.toBitVec = pointer)
    (hn : s.regs.rdx.toBitVec = BitVec.ofNat 64 words.length)
    (stored : (NatOperand.large pointer words).At (widthLoad s.dmem))
    (P : MachineState → Prop)
    (next : ∀ t, ReadFrame s t → t.regs.rax.toBitVec = words[1]?.getD 0 →
      t.regs.rdx.toBitVec = words[0]?.getD 0 → Eventually (step e) P (t, base + 96)) :
    Eventually (step e) P (s, base + 62) := by
  have lengthNat : s.regs.rdx.toBitVec.toNat = words.length := by
    rw [hn, length_bits pointer words s stored]
  apply zero_dispatch_cps e base hc s P
  · intro zero flags
    have nil : words = [] := by
      apply List.length_eq_zero_iff.mp
      have hz := congrArg BitVec.toNat zero
      change s.regs.rdx.toBitVec.toNat = 0 at hz
      omega
    apply empty_cps e base hc
    intro flags'
    apply next
    · exact (status_frame s flags).trans (result_frame _ _ _ _ flags')
    · subst words
      rfl
    · subst words
      rfl
  · intro nz flags
    apply prepare_borrowed_cps e base hc _ pointer words
    · exact hp
    · exact hn
    · exact stored
    · by_cases positive : 0 < words.length
      · exact positive
      · have zero : words.length = 0 := by omega
        apply False.elim (nz _)
        rw [hn, zero]
        rfl
    · intro t frame hi lo
      exact next t ((status_frame s flags).trans frame) hi lo

/-- Actual entry through the two pre-publication cuts, with no execution or
result premise. Every read follows from the original physical operand view. -/
theorem prepare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand)
    (pointer : s.regs.rsi.toBitVec = operand.pointer)
    (payload : s.regs.rdx.toBitVec = operand.payload)
    (stored : operand.At (widthLoad s.dmem)) (P : MachineState → Prop)
    (none : NatNarrow.toU128 operand = none → ∀ t, ReadFrame s t →
      t.regs.rax.toBitVec = 0 → t.regs.rcx.toBitVec = 0 →
      Eventually (step e) P (t, base + 50))
    (some : ∀ value, NatNarrow.toU128 operand = some value → ∀ t, ReadFrame s t →
      t.regs.rax.toBitVec = (value >>> (64 : Nat)).setWidth 64 →
      t.regs.rdx.toBitVec = value.setWidth 64 → Eventually (step e) P (t, base + 96)) :
    Eventually (step e) P (s, base) := by
  cases operand with
  | small limb =>
    have pp : s.regs.rsi.toBitVec = 0 := pointer
    have pv : s.regs.rdx.toBitVec = limb := payload
    have fits : (NatOperand.small limb).wordCount ≤ 2 := by
      change Limbs.significantCount [limb] 1 ≤ 2
      have bound := Limbs.significantCount_le [limb] 1
      omega
    have parts := wide_parts (NatOperand.small limb) fits
    apply entry_dispatch_cps e base hc s P
    · intro _ flags
      apply immediate_cps e base hc
      intro flags'
      apply some (SszNative.NatDivision.wideValue (.small limb))
      · simp only [NatNarrow.toU128, fits, ↓reduceIte]
      · exact (status_frame s flags).trans (result_frame _ _ _ _ flags')
      · exact parts.2.symm
      · exact pv.trans parts.1.symm
    · intro nonzero
      exact False.elim (nonzero pp)
  | large p words =>
    have pp : s.regs.rsi.toBitVec = p := pointer
    have pv : s.regs.rdx.toBitVec = BitVec.ofNat 64 words.length := payload
    have hb : words.length + 1 < 2^64 := by
      have bound := stored.2.2.1
      omega
    have pnonzero : p ≠ 0 := by
      intro zero
      have positive := stored.1
      simp [zero] at positive
    have countBound : Limbs.sigWords words < 2^64 :=
      Nat.lt_of_le_of_lt (Limbs.sigWords_le_length words) (by omega)
    have finish : (NatOperand.large p words).wordCount ≤ 2 →
        ∀ t, ReadFrame s t → t.regs.rax.toBitVec = words[1]?.getD 0 →
        t.regs.rdx.toBitVec = words[0]?.getD 0 → Eventually (step e) P (t, base + 96) := by
      intro fits t frame hi lo
      have parts := wide_parts (NatOperand.large p words) fits
      apply some (SszNative.NatDivision.wideValue (.large p words))
      · simp only [NatNarrow.toU128, fits, ↓reduceIte]
      · exact frame
      · exact hi.trans parts.2.symm
      · exact lo.trans parts.1.symm
    apply entry_dispatch_cps e base hc s P
    · intro zero
      exact False.elim (pnonzero (pp.symm.trans zero))
    · intro _ flags
      have plusOne : s.regs.rdx.toBitVec + 1 = BitVec.ofNat 64 (words.length+1) := by
        change s.regs.rdx.toBitVec + 1#64 = BitVec.ofNat 64 (words.length+1)
        rw [pv, BitVec.ofNat_add]
      rw [plusOne]
      apply scan e base hc s words hb
      · intro i
        have h := large_read s p words stored i.val i.isLt
        rw [List.getElem?_eq_getElem i.isLt, Option.getD_some] at h
        change Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
          Option.some (words[i.val].toNat : Int)
        simpa only [pp] using h
      · exact Nat.le_refl _
      · intro zero x flags'
        apply prepare_zero_cps e base hc _ p words
        · exact pp
        · exact pv
        · exact stored
        · intro t frame hi lo
          apply finish
          · change Limbs.significantCount words words.length ≤ 2
            omega
          · exact (scan_frame s _ x flags').trans frame
          · exact hi
          · exact lo
      · intro positive flags'
        apply count_dispatch_cps e base hc
        · intro small flags''
          apply prepare_borrowed_cps e base hc _ p words
          · exact pp
          · exact pv
          · exact stored
          · have bound := Limbs.significantCount_le words words.length
            omega
          · intro t frame hi lo
            apply finish
            · change Limbs.sigWords words ≤ 2
              change (BitVec.ofNat 64 (Limbs.sigWords words)).toNat < 3 at small
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound] at small
              omega
            · exact (scan_frame s _ _ flags').trans ((result_frame _ _ _ _ flags'').trans frame)
            · exact hi
            · exact lo
        · intro big flags''
          have large : ¬(NatOperand.large p words).wordCount ≤ 2 := by
            change 3 ≤ (BitVec.ofNat 64 (Limbs.sigWords words)).toNat at big
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound] at big
            change ¬Limbs.sigWords words ≤ 2
            omega
          apply none
          · simp only [NatNarrow.toU128, large, ↓reduceIte]
          · exact (scan_frame s _ _ flags').trans (result_frame _ _ _ _ flags'')
          · rfl
          · rfl

end SszX86.NatToU128
