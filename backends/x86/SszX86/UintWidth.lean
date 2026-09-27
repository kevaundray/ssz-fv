import SszX86.UintImpl
import SszX86.UintWidthMemory

namespace SszX86.UintCodec
open Kraken.X64.Parser
open SszNative.Limbs

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

/-- Only these five integer registers and arithmetic flags are clobbered by
this prefix. In particular, every byte of memory, all vector registers, RSP,
RDI, RDX, RBX, RBP and R14 remain those of `s`. -/
def widthState (s : MachineData) (a c si x t : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec a
      rcx := UInt64.ofBitVec c
      rsi := UInt64.ofBitVec si
      r8 := UInt64.ofBitVec x
      r10 := UInt64.ofBitVec t}
    status := flags}

macro "uint_width_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := step_at _ _ $hc
     (SszX86.UintCodec.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.UintCodec.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [program, directives, labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits, widthState]))

private theorem width_cast (v : BitVec 64) :
    BitVec.ofInt 64 (v.toNat : Int) = v := by bv_omega

/-- Normalize the architectural load width before rewriting its mapped-memory
equation; leaving `W64.bytes` opaque prevents the equation from matching. -/
macro "uint_width_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), width_cast])

private theorem width_reg_address (p : UInt64) (offset : Nat) :
    BitVec.ofNat 64 (p.toNat + offset) = p.toBitVec + BitVec.ofNat 64 offset := by
  change BitVec.ofNat 64 (p.toBitVec.toNat + offset) = _
  exact width_address p.toBitVec offset

private theorem width_sub_zero (a b : BitVec 64) : a - b = 0#64 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun x : BitVec 64 => x + b) h
    simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using this
  · rintro rfl
    exact BitVec.sub_self _

private theorem width_cf (a b : BitVec 64) :
    (memcpySubFlags a b).cf = decide (a.toNat < b.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [memcpySubFlags, StatusFlags.from_result, bne_iff_ne,
    decide_eq_true_eq, BitVec.unsigned]
  by_cases h : a < b
  · rw [BitVec.toNat_sub_of_lt h]
    have ha := a.isLt
    have hb := b.isLt
    change a.toNat < b.toNat at h
    omega
  · have hle : b ≤ a := by exact Nat.le_of_not_gt h
    rw [BitVec.toNat_sub_of_le hle]
    change ¬ a.toNat < b.toNat at h
    omega

/-- Header loads, the pointer TEST, and its real conditional branch. -/
private theorem width_header (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c : BitVec 64) (P : MachineState → Prop)
    (ha : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 = some (a.toNat : Int))
    (hc' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 = some (c.toNat : Int))
    (hp : ∀ flags, Eventually (step e) P
      (widthState s a c s.regs.rsi.toBitVec s.regs.r8.toBitVec s.regs.r10.toBitVec flags,
       if a = 0#64 then base + 2462 else base + 1148)) :
    Eventually (step e) P (s, base + 1131) := by
  have target := hc.targets ("u2462", 2462) (by decide)
  uint_width_step 9 using hc
  uint_width_load ha
  uint_width_step 10 using hc
  uint_width_load hc'
  uint_width_step 11 using hc
  constructor <;> uint_width_step 12 using hc
  all_goals
    by_cases hz : a = 0#64
    · simpa [target, StatusFlags.from_result, hz, widthState, Effects.All] using hp _
    · simpa [StatusFlags.from_result, hz, widthState, Effects.All] using hp _

/-- The common two-word equality check, success register setup, and the actual
linked two-byte NOP at 2798. Both undefined logical-operation AFs, and the
success XOR's AF, are quantified by `Effects.All`, never chosen by the proof. -/
private theorem width_pair (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c lo hi t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hyes : ((lo ^^^ s.regs.r14.toBitVec) ||| hi) = 0#64 →
      ∀ flags, Eventually (step e) P
        (widthState s s.regs.r14.toBitVec c hi 0#64 s.regs.r14.toBitVec flags, base + 2800))
    (hno : ((lo ^^^ s.regs.r14.toBitVec) ||| hi) ≠ 0#64 →
      ∀ flags, Eventually (step e) P
        (widthState s a c hi ((lo ^^^ s.regs.r14.toBitVec) ||| hi) t flags, base + 2851)) :
    Eventually (step e) P (widthState s a c hi lo t flags, base + 2781) := by
  have target := hc.targets ("u2851", 2851) (by decide)
  by_cases hz : ((lo ^^^ s.regs.r14.toBitVec) ||| hi) = 0#64
  · have hcond : lo = s.regs.r14.toBitVec ∧ hi = 0#64 := by simpa using hz
    uint_width_step 54 using hc
    constructor <;> uint_width_step 55 using hc
    all_goals constructor <;> uint_width_step 56 using hc
    all_goals simp [StatusFlags.from_result, hcond.1, hcond.2, Effects.All]
    all_goals uint_width_step 57 using hc
    all_goals constructor <;> uint_width_step 58 using hc
    all_goals uint_width_step 59 using hc
    all_goals uint_width_step 60 using hc
    all_goals simpa [widthState, hcond.2] using hyes hz _
  · have hcond : lo = s.regs.r14.toBitVec → hi ≠ 0#64 := by
      intro hlo hhi
      apply hz
      simp [hlo, hhi]
    have hw : UInt64.ofBitVec ((lo ^^^ s.regs.r14.toBitVec) ||| hi) =
        (UInt64.ofBitVec lo ^^^ s.regs.r14) ||| UInt64.ofBitVec hi := by
      apply UInt64.toBitVec_inj.1
      simp
    uint_width_step 54 using hc
    constructor <;> uint_width_step 55 using hc
    all_goals constructor <;> uint_width_step 56 using hc
    all_goals simp [target, StatusFlags.from_result]
    all_goals rw [ite_eq_left hcond]
    all_goals simpa only [Effects.All, widthState, hw] using hno hz _

private theorem width_small (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si x t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (widthState s a c 0#64 c t flags, base + 2781)) :
    Eventually (step e) P (widthState s a c si x t flags, base + 2462) := by
  uint_width_step 28 using hc
  constructor <;> uint_width_step 29 using hc
  all_goals uint_width_step 30 using hc
  all_goals simpa [widthState] using hp _

private theorem width_empty (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si x t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (widthState s a c 0#64 0#64 t flags, base + 2781)) :
    Eventually (step e) P (widthState s a c si x t flags, base + 2776) := by
  uint_width_step 52 using hc
  constructor <;> uint_width_step 53 using hc
  all_goals constructor
  all_goals simpa [widthState] using hp _

private theorem width_one_hi (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si x t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (widthState s a c 0#64 x t flags, base + 2781)) :
    Eventually (step e) P (widthState s a c si x t flags, base + 2659) := by
  uint_width_step 38 using hc
  constructor <;> uint_width_step 39 using hc
  all_goals simpa [widthState] using hp _

/-- Low-word loading uses the *stored* length: a redundant second zero word
is still read when the significant count is only zero or one. -/
private theorem width_low_words (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a si x t : BitVec 64) (flags : StatusFlags)
    (words : List (BitVec 64)) (hn : words ≠ []) (hb : words.length < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8 * i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (widthState s a (BitVec.ofNat 64 words.length) (words[1]?.getD 0#64)
        (words[0]?.getD 0#64) t flags, base + 2781)) :
    Eventually (step e) P
      (widthState s a (BitVec.ofNat 64 words.length) si x t flags, base + 2538) := by
  have target := hc.targets ("u2659", 2659) (by decide)
  have hpos : 0 < words.length := by cases words <;> simp_all
  have h0 := hm ⟨0, hpos⟩
  have h0' : Mem.loadInt s.dmem a 8 = some ((words[0]?.getD 0#64).toNat : Int) := by
    simpa [List.getElem?_eq_getElem hpos] using h0
  have hcf : (memcpySubFlags (BitVec.ofNat 64 words.length) 2#64).cf =
      decide (words.length < 2) := by
    rw [width_cf]
    simp [Nat.mod_eq_of_lt hb]
  have hcf' :
      ((BitVec.ofNat 64 words.length - 2#64).unsigned !=
        (BitVec.ofNat 64 words.length).unsigned - (2#64).unsigned) =
        decide (words.length < 2) := hcf
  uint_width_step 33 using hc
  uint_width_load h0'
  uint_width_step 34 using hc
  uint_width_step 35 using hc
  by_cases htwo : words.length < 2
  · simp [StatusFlags.from_result, hcf', htwo, target, Effects.All]
    apply width_one_hi e base hc
    intro fl
    have h1 : words[1]?.getD 0#64 = 0#64 := by
      rw [List.getElem?_eq_none (by omega)]
      rfl
    simpa [h1] using hp fl
  · simp [StatusFlags.from_result, hcf', htwo, Effects.All]
    have h1 := hm ⟨1, by omega⟩
    have h1' : Mem.loadInt s.dmem (a + 8#64) 8 = some ((words[1]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show 1 < words.length by omega)] using h1
    uint_width_step 36 using hc
    uint_width_load h1'
    uint_width_step 37 using hc
    simpa [widthState] using hp _

private theorem width_zero_count (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si x t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (widthState s a c si x t flags, if c = 0#64 then base + 2776 else base + 2538)) :
    Eventually (step e) P (widthState s a c si x t flags, base + 2529) := by
  have target := hc.targets ("u2776", 2776) (by decide)
  uint_width_step 31 using hc
  constructor <;> uint_width_step 32 using hc
  all_goals
    by_cases hz : c = 0#64
    · simpa [target, StatusFlags.from_result, hz, widthState, Effects.All] using hp _
    · simpa [StatusFlags.from_result, hz, widthState, Effects.All] using hp _

/-- One descent reads exactly `words[n]`. The index/range assumptions below
are ordinary mapped-memory and no-wrap conditions, not execution hypotheses. -/
private theorem width_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c x t word : BitVec 64) (flags : StatusFlags)
    (n : Nat) (hb : n + 2 < 2^64)
    (hm : Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*n)) 8 = some (word.toNat : Int))
    (P : MachineState → Prop)
    (hzero : word = 0#64 → ∀ flags, Eventually (step e) P
      (widthState s a c (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) t flags, base + 1152))
    (hnonzero : word ≠ 0#64 → ∀ flags, Eventually (step e) P
      (widthState s a c (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) t flags,
        if n+1 < 3 then base + 2538 else base + 2851)) :
    Eventually (step e) P
      (widthState s a c (BitVec.ofNat 64 (n+2)) x t flags, base + 1152) := by
  have target1 := hc.targets ("u1152", 1152) (by decide)
  have target2 := hc.targets ("u2538", 2538) (by decide)
  have hz : BitVec.ofNat 64 (n+2) - 1#64 ≠ 0#64 := by
    intro he
    have heq := (width_sub_zero (BitVec.ofNat 64 (n+2)) 1#64).mp he
    have := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at this
    omega
  have hsi : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by
    bv_omega
  have haddr : BitVec.ofInt 64 (a.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      a + BitVec.ofNat 64 (8*n) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    rw [show BitVec.ofInt 64 8 = 8#64 by decide,
      show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
    bv_omega
  have hcf : (memcpySubFlags (BitVec.ofNat 64 (n+1)) 3#64).cf = decide (n+1 < 3) := by
    rw [width_cf]
    simp [Nat.mod_eq_of_lt (show n+1 < 2^64 by omega)]
  have hcf' : ((BitVec.ofNat 64 (n+1) - 3#64).unsigned !=
      (BitVec.ofNat 64 (n+1)).unsigned - (3#64).unsigned) = decide (n+1 < 3) := hcf
  uint_width_step 14 using hc
  uint_width_step 15 using hc
  simp [StatusFlags.from_result, hz, Effects.All]
  uint_width_step 16 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, hsi]
  uint_width_step 17 using hc
  rw [haddr]
  uint_width_load hm
  uint_width_step 18 using hc
  uint_width_step 19 using hc
  by_cases hw : word = 0#64
  · simpa [target1, StatusFlags.from_result, hw, widthState, Effects.All] using hzero hw _
  · simp [StatusFlags.from_result, hw, Effects.All]
    uint_width_step 20 using hc
    uint_width_step 21 using hc
    by_cases hsmall : n+1 < 3
    · simpa [target2, StatusFlags.from_result, hcf', hsmall, widthState, Effects.All]
        using hnonzero hw _
    · simp [StatusFlags.from_result, hcf', hsmall, Effects.All]
      uint_width_step 22 using hc
      simpa [hsmall, widthState] using hnonzero hw _

/-- Complete descending high-limb scan, with the same countdown as
`SszLimbOrder.significantCount`. Zero limbs may be arbitrarily redundant. -/
private theorem width_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c t : BitVec 64) (words : List (BitVec 64))
    (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ x flags,
    (SszNative.Limbs.significantCount words n = 0 → ∀ si x flags,
      Eventually (step e) P (widthState s a c si x t flags, base + 2529)) →
    (0 < SszNative.Limbs.significantCount words n →
      SszNative.Limbs.significantCount words n ≤ 2 → ∀ si x flags,
      Eventually (step e) P (widthState s a c si x t flags, base + 2538)) →
    (2 < SszNative.Limbs.significantCount words n → ∀ si x flags,
      Eventually (step e) P (widthState s a c si x t flags, base + 2851)) →
    Eventually (step e) P (widthState s a c (BitVec.ofNat 64 (n+1)) x t flags, base + 1152) := by
  intro n
  induction n with
  | zero =>
    intro hn x flags hzero hfew hmany
    have target := hc.targets ("u2529", 2529) (by decide)
    uint_width_step 14 using hc
    uint_width_step 15 using hc
    simpa [target, StatusFlags.from_result, widthState, Effects.All] using hzero rfl 1#64 x _
  | succ n ih =>
    intro hn x flags hzero hfew hmany
    have hload := hm ⟨n, by omega⟩
    have hload' : Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hload
    apply width_scan_step e base hc s a c x t (words[n]?.getD 0#64) flags n (by omega) hload' P
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
private theorem width_large (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a si x t : BitVec 64) (flags : StatusFlags)
    (words : List (BitVec 64)) (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop)
    (hyes : SszNative.Limbs.value words = s.regs.r14.toNat → ∀ si flags,
      Eventually (step e) P
        (widthState s s.regs.r14.toBitVec (BitVec.ofNat 64 words.length)
          si 0#64 s.regs.r14.toBitVec flags, base + 2800))
    (hno : SszNative.Limbs.value words ≠ s.regs.r14.toNat → ∀ si x flags,
      Eventually (step e) P
        (widthState s a (BitVec.ofNat 64 words.length) si x t flags, base + 2851)) :
    Eventually (step e) P
      (widthState s a (BitVec.ofNat 64 words.length) si x t flags, base + 1148) := by
  have pair (hfew : SszNative.Limbs.sigWords words ≤ 2) (fl : StatusFlags) :
      Eventually (step e) P
        (widthState s a (BitVec.ofNat 64 words.length) (words[1]?.getD 0#64)
          (words[0]?.getD 0#64) t fl, base + 2781) := by
    apply width_pair e base hc
    · intro he flags'
      exact hyes ((width_pair_eq words s.regs.r14.toBitVec hfew).mp he) _ flags'
    · intro he flags'
      exact hno (fun h => he ((width_pair_eq words s.regs.r14.toBitVec hfew).mpr h)) _ _ flags'
  have low (hn : words ≠ []) (hfew : SszNative.Limbs.sigWords words ≤ 2)
      (si x : BitVec 64) (fl : StatusFlags) :
      Eventually (step e) P
        (widthState s a (BitVec.ofNat 64 words.length) si x t fl, base + 2538) :=
    width_low_words e base hc s a si x t fl words hn (by omega) hm P (pair hfew)
  have loop (fl : StatusFlags) : Eventually (step e) P
      (widthState s a (BitVec.ofNat 64 words.length)
        (BitVec.ofNat 64 (words.length+1)) x t fl, base + 1152) := by
    apply width_scan e base hc s a (BitVec.ofNat 64 words.length) t words hb hm P
      words.length (Nat.le_refl _) x fl
    · intro hz si' x' fl'
      apply width_zero_count e base hc
      intro fl''
      by_cases hn : words = []
      · subst words
        change Eventually (step e) P (widthState s a 0#64 si' x' t fl'', base + 2776)
        apply width_empty e base hc
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
      exact hno (width_many_ne words s.regs.r14.toBitVec hmany) si' x' fl'
  have hlea : BitVec.ofInt 64 ((BitVec.ofNat 64 words.length).toInt + 1) =
      BitVec.ofNat 64 (words.length+1) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofNat_add]
    rfl
  uint_width_step 13 using hc
  simpa [hlea, widthState] using loop flags

/-- The exact frame for every outcome, including all integer registers not
used by the width prefix and the complete vector-register file. -/
def WidthFrame (s t : MachineData) : Prop :=
  t.dmem = s.dmem ∧ t.zmms = s.zmms ∧
  ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .r8 → r ≠ .r10 →
    t.regs.get64 r = s.regs.get64 r

theorem widthState_frame (s : MachineData) (a c si x t : BitVec 64) (fl : StatusFlags) :
    WidthFrame s (widthState s a c si x t fl) := by
  refine ⟨rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp_all [widthState, Reg64s.get64]

/-- Successful comparison stops before the first data-trim instruction.
Rejection stops before the first error store, retaining the descriptor's
original two words verbatim for the error-copy path. -/
def WidthPost (s : MachineData) (base : Int64) (expectedWidth : Nat)
    (st : MachineState) : Prop :=
  WidthFrame s st.1 ∧
  if expectedWidth = s.regs.r14.toNat then
    st.2 = base + 2800 ∧ st.1.regs.rax = s.regs.r14 ∧
      st.1.regs.r10 = s.regs.r14 ∧ st.1.regs.r8 = 0
  else
    st.2 = base + 2851 ∧
      Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 =
        some (st.1.regs.rax.toNat : Int) ∧
      Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 =
        some (st.1.regs.rcx.toNat : Int) ∧
      st.1.regs.r10 = s.regs.r10

/-- COMPLETE linked postdispatch descriptor-width prefix.

The sole memory assumption is the exact native `NatMemory.At` representation.
For Small this maps the two descriptor words; for Large it additionally maps
every stored limb, requires a non-null aligned pointer and bounds the whole
slice by 2^64. The descriptor header itself is required not to wrap. No data,
arena, output-object or stack mapping is needed because none is accessed here.
The relation permits Large [], all-zero slices and redundant high zero limbs.
All undefined flag choices are universally covered by the real Kraken steps. -/
theorem width_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (expectedWidth : Nat)
    (_hheader : s.regs.rbp.toNat + 24 ≤ 2^64)
    (hwidth : SszNative.NatMemory.At (widthLoad s.dmem)
      (s.regs.rbp.toNat + 8) expectedWidth) :
    Eventually (step e) (WidthPost s base expectedWidth) (s, base + 1131) := by
  rcases hwidth with ⟨⟨ha, hc'⟩, hv⟩ | ⟨pointer, words, hlarge, hvalue⟩
  · have ha' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 = some (0 : Int) := by
      simpa [width_reg_address] using widthLoad_eq s.dmem _ 8 0 ha
    have hc'' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 =
        some (expectedWidth : Int) := by
      simpa only [Nat.add_assoc, width_reg_address] using widthLoad_eq s.dmem _ 8 expectedWidth hc'
    have hn : (BitVec.ofNat 64 expectedWidth).toNat = expectedWidth :=
      Nat.mod_eq_of_lt hv
    apply width_header e base hc s 0#64 (BitVec.ofNat 64 expectedWidth)
      (WidthPost s base expectedWidth) ha'
    · simpa only [hn] using hc''
    intro fl
    simp only [↓reduceIte]
    apply width_small e base hc
    intro fl'
    apply width_pair e base hc
    · intro he fl''
      have heq : expectedWidth = s.regs.r14.toNat := by
        have heq : BitVec.ofNat 64 expectedWidth = s.regs.r14.toBitVec :=
          BitVec.xor_eq_zero_iff.mp (by simpa only [BitVec.or_zero] using he)
        exact hn.symm.trans (congrArg BitVec.toNat heq)
      apply Eventually.done
      refine ⟨widthState_frame _ _ _ _ _ _ _, ?_⟩
      rw [ite_eq_left heq]
      exact ⟨rfl, UInt64.ofBitVec_toBitVec _, UInt64.ofBitVec_toBitVec _, rfl⟩
    · intro he fl''
      have hne : expectedWidth ≠ s.regs.r14.toNat := by
        intro heq
        apply he
        have hv' : BitVec.ofNat 64 expectedWidth = s.regs.r14.toBitVec := by
          apply BitVec.eq_of_toNat_eq
          exact hn.trans heq
        simp [hv']
      apply Eventually.done
      refine ⟨widthState_frame _ _ _ _ _ _ _, ?_⟩
      rw [ite_eq_right hne]
      refine ⟨rfl, ha', ?_, UInt64.ofBitVec_toBitVec _⟩
      change Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 =
        some ((BitVec.ofNat 64 expectedWidth).toNat : Int)
      rw [hn]
      exact hc''
  · rcases hlarge with ⟨hptr, hptrBound, _halign, hrange, ha, hc', hwords⟩
    have hlen : words.length + 1 < 2^64 := by omega
    let a := BitVec.ofNat 64 pointer
    let c := BitVec.ofNat 64 words.length
    have han : a.toNat = pointer := Nat.mod_eq_of_lt hptrBound
    have hcn : c.toNat = words.length := Nat.mod_eq_of_lt (by omega)
    have ha' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 = some (a.toNat : Int) := by
      simpa only [width_reg_address, han] using widthLoad_eq s.dmem _ 8 pointer ha
    have hc'' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 = some (c.toNat : Int) := by
      simpa only [Nat.add_assoc, width_reg_address, hcn] using widthLoad_eq s.dmem _ 8 words.length hc'
    have ha0 : a ≠ 0#64 := by
      intro he
      have := congrArg BitVec.toNat he
      rw [han] at this
      simp only [BitVec.toNat_ofNat] at this
      omega
    have loads (i : Fin words.length) :
        Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int) := by
      have h := widthLoad_eq s.dmem _ 8 _ (hwords i)
      simpa only [← han, width_address] using h
    apply width_header e base hc s a c (WidthPost s base expectedWidth) ha' hc''
    intro fl
    simp only [ha0, ↓reduceIte]
    apply width_large e base hc s a _ _ _ fl words hlen loads
    · intro he si' fl'
      have heq : expectedWidth = s.regs.r14.toNat := hvalue.symm.trans he
      apply Eventually.done
      refine ⟨widthState_frame _ _ _ _ _ _ _, ?_⟩
      rw [ite_eq_left heq]
      exact ⟨rfl, UInt64.ofBitVec_toBitVec _, UInt64.ofBitVec_toBitVec _, rfl⟩
    · intro he si' x' fl'
      have hne : expectedWidth ≠ s.regs.r14.toNat := fun h => he (hvalue.trans h)
      apply Eventually.done
      refine ⟨widthState_frame _ _ _ _ _ _ _, ?_⟩
      rw [ite_eq_right hne]
      exact ⟨rfl, ha', hc'', UInt64.ofBitVec_toBitVec _⟩

/-- CPS form for composition with either data trimming or scope-error stores. -/
theorem width_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (expectedWidth : Nat)
    (hheader : s.regs.rbp.toNat + 24 ≤ 2^64)
    (hwidth : SszNative.NatMemory.At (widthLoad s.dmem)
      (s.regs.rbp.toNat + 8) expectedWidth)
    (P : MachineState → Prop)
    (hp : ∀ st, WidthPost s base expectedWidth st → Eventually (step e) P st) :
    Eventually (step e) P (s, base + 1131) := by
  exact eventually_trans (step e) (WidthPost s base expectedWidth) P _
    (width_runs e base hc s expectedWidth hheader hwidth) hp

end SszX86.UintCodec

namespace SszX86.UintCodec.WidthPost

/-- The two exit PCs are distinct even in the modular signed address type. -/
private theorem exits_ne (base : Int64) : base + 2800 ≠ base + 2851 := by
  intro he
  have h := congrArg (fun p : Int64 => p - base) he
  simp only [Int64.add_comm base 2800, Int64.add_comm base 2851,
    Int64.add_sub_cancel] at h
  exact (show (2800 : Int64) ≠ 2851 by decide) h

/-- Both directions of both exit characterizations, not merely soundness of
one selected execution path. -/
theorem outcomes (s : MachineData) (base : Int64) (expectedWidth : Nat)
    (st : MachineState) (h : SszX86.UintCodec.WidthPost s base expectedWidth st) :
    (st.2 = base + 2800 ↔ expectedWidth = s.regs.r14.toNat) ∧
    (st.2 = base + 2851 ↔ expectedWidth ≠ s.regs.r14.toNat) := by
  rcases h with ⟨_, h⟩
  by_cases he : expectedWidth = s.regs.r14.toNat
  · simp only [he, ↓reduceIte] at h
    refine ⟨⟨fun _ => he, fun _ => h.1⟩, ⟨?_, ?_⟩⟩
    · intro hp
      exact False.elim (exits_ne base (h.1.symm.trans hp))
    · intro hn
      exact False.elim (hn he)
  · simp only [he, ↓reduceIte] at h
    refine ⟨⟨?_, ?_⟩, ⟨fun _ => he, fun _ => h.1⟩⟩
    · intro hp
      exact False.elim (exits_ne base (hp.symm.trans h.1))
    · intro hp
      exact False.elim (he hp)

end SszX86.UintCodec.WidthPost
