import SszX86.NatExactImpl
import SszX86.NatDivisionCore
import SszNatNarrow

namespace SszX86.NatExact
open Kraken.X64.Parser
open SszNative SszNative.Limbs UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

structure ReadFrame (s t : MachineData) : Prop where
  memory : t.dmem = s.dmem
  vectors : t.zmms = s.zmms
  registers : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 →
    t.regs.get64 r = s.regs.get64 r

/-- All preparation states retain the original metadata, actual value, and output pointer. -/
def state (s : MachineData) (c x y z : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := 0
      rcx := UInt64.ofBitVec c
      r8 := UInt64.ofBitVec x
      r9 := UInt64.ofBitVec y
      r10 := UInt64.ofBitVec z}
    status := flags}

theorem state_frame (s : MachineData) (c x y z : BitVec 64) (flags : StatusFlags) :
    ReadFrame s (state s c x y z flags) := by
  refine ⟨rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp_all [state, Reg64s.get64]

macro "natexact_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.NatExact.step_at _ _ $hc
     (SszX86.NatExact.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.NatExact.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.NatExact.program, SszX86.NatExact.directives,
      SszX86.NatExact.labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits, state]))

macro "natexact_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), Delimited.word_cast])

/-- The three physical XOR/OR comparison sites have the same mathematical test. -/
theorem compare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (c x y z : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (yes : ((c ^^^ s.regs.rdx.toBitVec) ||| x) = 0 → ∀ flags,
      Eventually (step e) P
        (state s ((c ^^^ s.regs.rdx.toBitVec) ||| x) x y z flags, base + 171))
    (no : ((c ^^^ s.regs.rdx.toBitVec) ||| x) ≠ 0 → ∀ flags,
      Eventually (step e) P
        (state s ((c ^^^ s.regs.rdx.toBitVec) ||| x) x y z flags, base + 108)) :
    Eventually (step e) P (state s c x y z flags, base + 64) ∧
    Eventually (step e) P (state s c x y z flags, base + 100) ∧
    Eventually (step e) P (state s c x y z flags, base + 180) := by
  have target108 := hc.targets ("natExact_u108", 108) (by decide)
  have target171 := hc.targets ("natExact_u171", 171) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · natexact_step 18 using hc
    constructor <;> natexact_step 19 using hc
    all_goals constructor <;> natexact_step 20 using hc
    all_goals
      by_cases equal : ((c ^^^ s.regs.rdx.toBitVec) ||| x) = 0#64
      · simp [StatusFlags.from_result, equal, Effects.All]
        natexact_step 21 using hc
        simpa only [state, UInt64.ofBitVec_or, UInt64.ofBitVec_xor,
          UInt64.ofBitVec_toBitVec] using yes equal _
      · simpa [StatusFlags.from_result, equal, target108, state, Effects.All] using no equal _
  · natexact_step 31 using hc
    constructor <;> natexact_step 32 using hc
    all_goals constructor <;> natexact_step 33 using hc
    all_goals
      by_cases equal : ((c ^^^ s.regs.rdx.toBitVec) ||| x) = 0#64
      · simp [StatusFlags.from_result, equal, target171, Effects.All]
        simpa only [state, UInt64.ofBitVec_or, UInt64.ofBitVec_xor,
          UInt64.ofBitVec_toBitVec] using yes equal _
      · simpa [StatusFlags.from_result, equal, state, Effects.All] using no equal _
  · natexact_step 49 using hc
    constructor <;> natexact_step 50 using hc
    all_goals constructor <;> natexact_step 51 using hc
    all_goals
      by_cases equal : ((c ^^^ s.regs.rdx.toBitVec) ||| x) = 0#64
      · simp [StatusFlags.from_result, equal, Effects.All]
        natexact_step 52 using hc
        simpa only [state, UInt64.ofBitVec_or, UInt64.ofBitVec_xor,
          UInt64.ofBitVec_toBitVec] using yes equal _
      · simpa [StatusFlags.from_result, equal, target108, state, Effects.All] using no equal _

/-- Exactly the metadata loads and initial pointer dispatch at the real entry. -/
theorem entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64)
    (hp : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (pointer.toNat : Int))
    (hv : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (payload.toNat : Int))
    (P : MachineState → Prop)
    (small : pointer = 0 → ∀ flags, Eventually (step e) P
      (state s payload pointer s.regs.r9.toBitVec s.regs.r10.toBitVec flags, base + 61))
    (large : pointer ≠ 0 → ∀ flags, Eventually (step e) P
      (state s payload pointer (payload + 1) s.regs.r10.toBitVec flags, base + 32)) :
    Eventually (step e) P (s, base) := by
  have target := hc.targets ("natExact_u61", 61) (by decide)
  rw [← Int64.add_zero base]
  natexact_step 0 using hc
  natexact_load hp
  natexact_step 1 using hc
  natexact_load hv
  natexact_step 2 using hc
  constructor <;> natexact_step 3 using hc
  all_goals constructor <;> natexact_step 4 using hc
  all_goals
    by_cases zero : pointer = 0#64
    · simpa [StatusFlags.from_result, zero, target, state, Effects.All] using small zero _
    · simp [StatusFlags.from_result, zero, Effects.All]
      natexact_step 5 using hc
      simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
      natexact_step 6 using hc
      natexact_step 7 using hc
      simpa [state] using large zero _

/-- One countdown iteration reads the exact original limb selected by R9. -/
theorem scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (c d z limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (hb : n + 2 < 2^64)
    (hm : Mem.loadInt s.dmem (d + BitVec.ofNat 64 (8*n)) 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (hz : limb = 0#64 → ∀ flags, Eventually (step e) P
      (state s c d (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 32))
    (hn : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (state s c d (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 53)) :
    Eventually (step e) P (state s c d (BitVec.ofNat 64 (n+2)) z flags, base + 32) := by
  have target := hc.targets ("natExact_u32", 32) (by decide)
  have hne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have hdec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  have haddr : BitVec.ofInt 64 (d.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      d + BitVec.ofNat 64 (8*n) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    rw [show BitVec.ofInt 64 8 = 8#64 by decide,
      show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
    bv_omega
  natexact_step 8 using hc
  natexact_step 9 using hc
  simp [StatusFlags.from_result, hne, Effects.All]
  natexact_step 10 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, hdec]
  natexact_step 11 using hc
  rw [haddr]
  natexact_load hm
  natexact_step 12 using hc
  natexact_step 13 using hc
  by_cases zero : limb = 0#64
  · simpa [StatusFlags.from_result, zero, target, state, Effects.All] using hz zero _
  · simpa [StatusFlags.from_result, zero, state, Effects.All] using hn zero _

/-- Induction over physical length implements significantCount even for padded zero input. -/
theorem scan_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (c d : BitVec 64) (words : List (BitVec 64))
    (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (d + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ z flags,
    (significantCount words n = 0 → ∀ z flags, Eventually (step e) P
      (state s c d 1 z flags, base + 74)) →
    (0 < significantCount words n → ∀ flags, Eventually (step e) P
      (state s c d (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 53)) →
    Eventually (step e) P (state s c d (BitVec.ofNat 64 (n+1)) z flags, base + 32) := by
  intro n
  induction n with
  | zero =>
    intro hn z flags hz hp
    have target := hc.targets ("natExact_u74", 74) (by decide)
    natexact_step 8 using hc
    natexact_step 9 using hc
    simpa [StatusFlags.from_result, target, Effects.All, state] using
      hz (by simp [significantCount]) z _
  | succ n ih =>
    intro hn z flags hz hp
    have observed : Mem.loadInt s.dmem (d + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply scan_step e base hc s c d z _ flags n (by omega) observed P
    · intro zero fl
      apply ih (by omega) _ fl
      · intro hs z fl
        apply hz (by simpa [significantCount, zero] using hs)
      · intro hs fl
        simpa [significantCount, zero] using hp (by simpa [significantCount, zero] using hs) fl
    · intro nonzero fl
      simpa [significantCount, nonzero] using hp (by simp [significantCount, nonzero]) fl

/-- The count comparison rejects genuinely wide values before any low-word conversion. -/
theorem count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (c d y z : BitVec 64) (flags : StatusFlags) (P : MachineState → Prop)
    (small : z.toNat < 3 → ∀ flags,
      Eventually (step e) P (state s c d y z flags, base + 79))
    (large : 3 ≤ z.toNat → ∀ flags,
      Eventually (step e) P (state s c d y z flags, base + 108)) :
    Eventually (step e) P (state s c d y z flags, base + 53) := by
  have target := hc.targets ("natExact_u79", 79) (by decide)
  natexact_step 14 using hc
  natexact_step 15 using hc
  by_cases short : z.toNat < 3
  · simpa [StatusFlags.from_result, Udivti3.cf_sub, short, target, state, Effects.All] using small short _
  · simp [StatusFlags.from_result, short, Effects.All]
    natexact_step 16 using hc
    simpa [state] using large (by omega) _

/-- Original physical length, not trimmed length, governs the second limb read. -/
theorem borrowed_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (c d y z lo hi : BitVec 64) (flags : StatusFlags)
    (hlo : Mem.loadInt s.dmem d 8 = some (lo.toNat : Int))
    (hhi : 2 ≤ c.toNat → Mem.loadInt s.dmem (d + 8#64) 8 = some (hi.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (state s lo (if c.toNat < 2 then 0 else hi) lo z flags, base + 100)) :
    Eventually (step e) P (state s c d y z flags, base + 79) := by
  have target := hc.targets ("natExact_u94", 94) (by decide)
  natexact_step 24 using hc
  natexact_load hlo
  natexact_step 25 using hc
  natexact_step 26 using hc
  by_cases short : c.toNat < 2
  · simp only [short, target]
    natexact_step 29 using hc
    constructor <;> natexact_step 30 using hc
    all_goals simpa [state, short] using next _
  · simp only [short]
    natexact_step 27 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
    natexact_load (hhi (by omega))
    natexact_step 28 using hc
    natexact_step 30 using hc
    simpa [state, short] using next _

/-- All-zero input still tests the original length before selecting empty storage. -/
theorem zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (c d y z : BitVec 64) (flags : StatusFlags) (P : MachineState → Prop)
    (empty : c = 0 → ∀ flags,
      Eventually (step e) P (state s 0 0 y z flags, base + 180))
    (nonempty : c ≠ 0 → ∀ flags,
      Eventually (step e) P (state s c d y z flags, base + 79)) :
    Eventually (step e) P (state s c d y z flags, base + 74) := by
  have target := hc.targets ("natExact_u175", 175) (by decide)
  natexact_step 22 using hc
  constructor <;> natexact_step 23 using hc
  all_goals
    by_cases zero : c = 0#64
    · simp [StatusFlags.from_result, zero, target, Effects.All]
      natexact_step 47 using hc
      constructor <;> natexact_step 48 using hc
      all_goals constructor <;> simpa [state] using empty zero _
    · simpa [StatusFlags.from_result, zero, state, Effects.All] using nonempty zero _

private theorem exact_pair (operand : NatOperand) (actual : BitVec 64)
    (count : operand.wordCount ≤ 2) :
    NatNarrow.runExact operand actual = true ↔
      (((operand.words[0]?.getD 0) ^^^ actual) ||| operand.words[1]?.getD 0) = 0 := by
  rw [NatNarrow.runExact_iff]
  exact (width_pair_eq operand.words actual count).symm

private theorem exact_pair_false (operand : NatOperand) (actual : BitVec 64)
    (count : operand.wordCount ≤ 2)
    (different : (((operand.words[0]?.getD 0) ^^^ actual) ||| operand.words[1]?.getD 0) ≠ 0) :
    NatNarrow.runExact operand actual = false := by
  cases result : NatNarrow.runExact operand actual
  · rfl
  · exact False.elim (different ((exact_pair operand actual count).mp result))

/-- Preparation starts at the actual entry and stops strictly before publication.
The only premises describing input are physical metadata/limb observations and RDX. -/
theorem prepare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (actual : BitVec 64)
    (actual_register : s.regs.rdx.toBitVec = actual)
    (operandAt : NatArithmetic.operandAt (widthLoad s.dmem) s.regs.rsi.toNat operand)
    (P : MachineState → Prop)
    (success : NatNarrow.runExact operand actual = true → ∀ t, ReadFrame s t →
      t.regs.rax.toBitVec = 0 → Eventually (step e) P (t, base + 171))
    (failure : NatNarrow.runExact operand actual = false → ∀ t, ReadFrame s t →
      Eventually (step e) P (t, base + 108)) :
    Eventually (step e) P (s, base) := by
  have pointerRead : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 =
      some (operand.pointer.toNat : Int) := by
    simpa using widthLoad_eq s.dmem _ _ _ operandAt.1
  have payloadRead : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 =
      some (operand.payload.toNat : Int) := by
    simpa only [show s.regs.rsi.toNat = s.regs.rsi.toBitVec.toNat from rfl,
      width_address, BitVec.ofNat_eq_ofNat] using widthLoad_eq s.dmem _ _ _ operandAt.2.1
  have finish : ∀ (c x y z : BitVec 64) (flags : StatusFlags),
      operand.wordCount ≤ 2 → c = operand.words[0]?.getD 0 → x = operand.words[1]?.getD 0 →
      Eventually (step e) P (state s c x y z flags, base + 64) ∧
      Eventually (step e) P (state s c x y z flags, base + 100) ∧
      Eventually (step e) P (state s c x y z flags, base + 180) := by
    intro c x y z flags count lowEq highEq
    apply compare_cps e base hc s c x y z flags P
    · intro equal fl
      apply success ((exact_pair operand actual count).mpr ?_) _ (state_frame _ _ _ _ _ _) rfl
      simpa only [actual_register, lowEq, highEq] using equal
    · intro different fl
      apply failure (exact_pair_false operand actual count ?_) _ (state_frame _ _ _ _ _ _)
      simpa only [actual_register, lowEq, highEq] using different
  have viewed := SszX86.NatDivision.operand_view s.dmem operand operandAt.2.2
  cases operand with
  | small limb =>
    apply entry_cps e base hc s _ _ pointerRead payloadRead P
    · intro _ flags
      natexact_step 17 using hc
      constructor
      · exact (finish limb 0 _ _ _ (by
          change significantCount [limb] 1 ≤ 2
          have bound := significantCount_le [limb] 1
          omega) rfl rfl).1
      · exact (finish limb 0 _ _ _ (by
          change significantCount [limb] 1 ≤ 2
          have bound := significantCount_le [limb] 1
          omega) rfl rfl).1
    · intro impossible
      exact False.elim (impossible rfl)
  | large pointer words =>
    change NatCompare.View s.dmem pointer (BitVec.ofNat 64 words.length) words at viewed
    rcases viewed with ⟨zero, _⟩ | ⟨nonzero, countEq, bound, limbs⟩
    · have positive : 0 < pointer.toNat := operandAt.2.2.1
      simp [zero] at positive
    · have lengthNat : (BitVec.ofNat 64 words.length).toNat = words.length :=
        Nat.mod_eq_of_lt (by omega)
      have borrowed : ∀ y z flags, sigWords words ≤ 2 → 0 < words.length →
          Eventually (step e) P
            (state s (BitVec.ofNat 64 words.length) pointer y z flags, base + 79) := by
        intro y z flags fits nonempty
        apply borrowed_cps e base hc s _ pointer y z
          (words[0]?.getD 0) (words[1]?.getD 0) flags
        · simpa [List.getElem?_eq_getElem nonempty] using limbs ⟨0, nonempty⟩
        · intro two
          have indexBound : 1 < words.length := by rw [lengthNat] at two; omega
          simpa [List.getElem?_eq_getElem indexBound] using limbs ⟨1, indexBound⟩
        · intro fl
          apply (finish _ _ _ _ fl fits rfl ?_).2.1
          change (if (BitVec.ofNat 64 words.length).toNat < 2 then 0 else words[1]?.getD 0) =
            words[1]?.getD 0
          by_cases short : (BitVec.ofNat 64 words.length).toNat < 2
          · rw [ite_eq_left short, List.getElem?_eq_none (by rw [lengthNat] at short; omega)]
            rfl
          · exact ite_eq_right short
      apply entry_cps e base hc s _ _ pointerRead payloadRead P
      · intro zero
        exact False.elim (nonzero zero)
      · intro _ flags
        have plusOne : BitVec.ofNat 64 words.length + 1#64 =
            BitVec.ofNat 64 (words.length+1) := by rw [BitVec.ofNat_add]
        change Eventually (step e) P
          (state s (BitVec.ofNat 64 words.length) pointer
            (BitVec.ofNat 64 words.length + 1#64) s.regs.r10.toBitVec flags, base + 32)
        rw [plusOne]
        apply scan_cps e base hc s _ pointer words bound limbs P words.length (Nat.le_refl _) _ flags
        · intro allZero z fl
          apply zero_cps e base hc
          · intro empty fl'
            have emptyLength : words.length = 0 := by
              have hz := congrArg BitVec.toNat empty
              change (BitVec.ofNat 64 words.length).toNat = 0 at hz
              rw [lengthNat] at hz
              exact hz
            have nil : words = [] := List.length_eq_zero_iff.mp emptyLength
            apply (finish 0 0 _ _ fl' (by change sigWords words ≤ 2; change significantCount words words.length ≤ 2; omega)
              (by simp [nil, NatOperand.words]) (by simp [nil, NatOperand.words])).2.2
          · intro nonempty fl'
            apply borrowed _ _ fl' (by change significantCount words words.length ≤ 2; omega)
            by_cases positive : 0 < words.length
            · exact positive
            · have emptyLength : words.length = 0 := by omega
              apply False.elim (nonempty ?_)
              rw [emptyLength]
              rfl
        · intro positive fl
          apply count_cps e base hc
          · intro fits fl'
            have sigBound : sigWords words < 2^64 :=
              Nat.lt_of_le_of_lt (sigWords_le_length words) (by omega)
            have smallCount : sigWords words ≤ 2 := by
              change (BitVec.ofNat 64 (sigWords words)).toNat < 3 at fits
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sigBound] at fits
              omega
            apply borrowed _ _ fl' smallCount
            have sigBound' := significantCount_le words words.length
            omega
          · intro large fl'
            have sigBound : sigWords words < 2^64 :=
              Nat.lt_of_le_of_lt (sigWords_le_length words) (by omega)
            have bigCount : ¬ (NatOperand.large pointer words).wordCount ≤ 2 := by
              change 3 ≤ (BitVec.ofNat 64 (sigWords words)).toNat at large
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sigBound] at large
              change ¬ sigWords words ≤ 2
              omega
            apply failure (by simp [NatNarrow.runExact, NatNarrow.toU128, bigCount]) _
              (state_frame _ _ _ _ _ _)

end SszX86.NatExact
