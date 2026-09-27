import SszX86.ByteViewImpl
import SszX86.UintBodyMemory

namespace SszX86.ByteView.Vector
open Kraken.X64.Parser
open SszNative.Limbs
open UintCodec
open SszX86.ByteView

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

macro "view_vector_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.ByteView.step_at _ _ $hc
     (SszX86.ByteView.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.ByteView.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.ByteView.program, SszX86.ByteView.directives, SszX86.ByteView.labels, Directives.interp, Directive.interp,
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
macro "view_vector_load " hl:term : tactic => `(tactic|
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
private theorem width_header (e : Executable) (base : Int64) (hc : SszX86.ByteView.CodeAt e base)
    (s : MachineData) (a c : BitVec 64) (P : MachineState → Prop)
    (ha : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 = some (a.toNat : Int))
    (hc' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 = some (c.toNat : Int))
    (hp : ∀ flags, Eventually (step e) P
      (widthState s a c s.regs.rsi.toBitVec s.regs.r8.toBitVec s.regs.r10.toBitVec flags,
       if a = 0#64 then base + 2023 else base + 767)) :
    Eventually (step e) P (s, base + 750) := by
  have target := hc.targets ("u2023", 2023) (by decide)
  view_vector_step 9 using hc
  view_vector_load ha
  view_vector_step 10 using hc
  view_vector_load hc'
  view_vector_step 11 using hc
  constructor <;> view_vector_step 12 using hc
  all_goals
    by_cases hz : a = 0#64
    · simpa [target, StatusFlags.from_result, hz, widthState, Effects.All] using hp _
    · simpa [StatusFlags.from_result, hz, widthState, Effects.All] using hp _

private theorem width_pair (e : Executable) (base : Int64) (hc : SszX86.ByteView.CodeAt e base)
    (s : MachineData) (a c lo hi t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (widthState s a c hi ((lo ^^^ s.regs.r14.toBitVec) ||| hi) t flags,
       if ((lo ^^^ s.regs.r14.toBitVec) ||| hi) = 0#64 then base + 2759 else base + 2851)) :
    Eventually (step e) P (widthState s a c hi lo t flags, base + 2751) := by
  have target := hc.targets ("u2851", 2851) (by decide)
  view_vector_step 146 using hc
  constructor <;> view_vector_step 147 using hc
  all_goals constructor <;> view_vector_step 148 using hc
  all_goals
    by_cases hz : ((lo ^^^ s.regs.r14.toBitVec) ||| hi) = 0#64
    · have he : lo = s.regs.r14.toBitVec ∧ hi = 0#64 := by simpa using hz
      simpa [StatusFlags.from_result, he.1, he.2, widthState, Effects.All] using hp _
    · have he : lo = s.regs.r14.toBitVec → hi ≠ 0#64 := by
        intro hlo hhi
        exact hz (by simp [hlo, hhi])
      have hw : UInt64.ofBitVec ((lo ^^^ s.regs.r14.toBitVec) ||| hi) =
          (UInt64.ofBitVec lo ^^^ s.regs.r14) ||| UInt64.ofBitVec hi := by
        apply UInt64.toBitVec_inj.1
        simp
      simpa [target, StatusFlags.from_result, he, hz, widthState, hw, Effects.All] using hp _

private theorem width_small (e : Executable) (base : Int64) (hc : SszX86.ByteView.CodeAt e base)
    (s : MachineData) (a c si x t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (widthState s a c 0#64 c t flags, base + 2751)) :
    Eventually (step e) P (widthState s a c si x t flags, base + 2023) := by
  view_vector_step 71 using hc
  constructor <;> view_vector_step 72 using hc
  all_goals view_vector_step 73 using hc
  all_goals simpa [widthState] using hp _

private theorem width_empty (e : Executable) (base : Int64) (hc : SszX86.ByteView.CodeAt e base)
    (s : MachineData) (a c si x t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (widthState s a c 0#64 0#64 t flags, base + 2751)) :
    Eventually (step e) P (widthState s a c si x t flags, base + 2746) := by
  view_vector_step 144 using hc
  constructor <;> view_vector_step 145 using hc
  all_goals constructor
  all_goals simpa [widthState] using hp _

private theorem width_one_hi (e : Executable) (base : Int64) (hc : SszX86.ByteView.CodeAt e base)
    (s : MachineData) (a c si x t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (widthState s a c 0#64 x t flags, base + 2751)) :
    Eventually (step e) P (widthState s a c si x t flags, base + 2655) := by
  view_vector_step 128 using hc
  constructor <;> view_vector_step 129 using hc
  all_goals simpa [widthState] using hp _

/-- Low-word loading uses the *stored* length: a redundant second zero word
is still read when the significant count is only zero or one. -/
private theorem width_low_words (e : Executable) (base : Int64) (hc : SszX86.ByteView.CodeAt e base)
    (s : MachineData) (a si x t : BitVec 64) (flags : StatusFlags)
    (words : List (BitVec 64)) (hn : words ≠ []) (hb : words.length < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8 * i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (widthState s a (BitVec.ofNat 64 words.length) (words[1]?.getD 0#64)
        (words[0]?.getD 0#64) t flags, base + 2751)) :
    Eventually (step e) P
      (widthState s a (BitVec.ofNat 64 words.length) si x t flags, base + 2481) := by
  have target := hc.targets ("u2655", 2655) (by decide)
  have hpos : 0 < words.length := by cases words <;> simp_all
  have h0 := hm ⟨0, hpos⟩
  have h0' : Mem.loadInt s.dmem a 8 = some ((words[0]?.getD 0#64).toNat : Int) := by
    simpa [List.getElem?_eq_getElem hpos] using h0
  view_vector_step 90 using hc
  view_vector_load h0'
  view_vector_step 91 using hc
  view_vector_step 92 using hc
  by_cases htwo : words.length < 2
  · simp [StatusFlags.from_result, Nat.mod_eq_of_lt hb, htwo, target, Effects.All]
    apply width_one_hi e base hc
    intro fl
    have h1 : words[1]?.getD 0#64 = 0#64 := by
      rw [List.getElem?_eq_none (by omega)]
      rfl
    simpa [h1] using hp fl
  · simp [StatusFlags.from_result, Nat.mod_eq_of_lt hb, htwo, Effects.All]
    have h1 := hm ⟨1, by omega⟩
    have h1' : Mem.loadInt s.dmem (a + 8#64) 8 = some ((words[1]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show 1 < words.length by omega)] using h1
    view_vector_step 93 using hc
    view_vector_load h1'
    view_vector_step 94 using hc
    simpa [widthState] using hp _

private theorem width_zero_count (e : Executable) (base : Int64) (hc : SszX86.ByteView.CodeAt e base)
    (s : MachineData) (a c si x t : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (widthState s a c si x t flags, if c = 0#64 then base + 2746 else base + 2481)) :
    Eventually (step e) P (widthState s a c si x t flags, base + 2472) := by
  have target := hc.targets ("u2746", 2746) (by decide)
  view_vector_step 88 using hc
  constructor <;> view_vector_step 89 using hc
  all_goals
    by_cases hz : c = 0#64
    · simpa [target, StatusFlags.from_result, hz, widthState, Effects.All] using hp _
    · simpa [StatusFlags.from_result, hz, widthState, Effects.All] using hp _

/-- One descent reads exactly `words[n]`. The index/range assumptions below
are ordinary mapped-memory and no-wrap conditions, not execution hypotheses. -/
private theorem width_scan_step (e : Executable) (base : Int64) (hc : SszX86.ByteView.CodeAt e base)
    (s : MachineData) (a c x t limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (hb : n + 2 < 2^64)
    (hm : Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*n)) 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (hzero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (widthState s a c (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) t flags, base + 784))
    (hnonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (widthState s a c (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) t flags,
        if n+1 < 3 then base + 2481 else base + 2851)) :
    Eventually (step e) P
      (widthState s a c (BitVec.ofNat 64 (n+2)) x t flags, base + 784) := by
  have target1 := hc.targets ("u784", 784) (by decide)
  have target2 := hc.targets ("u2851", 2851) (by decide)
  have hz : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have hsi : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by
    bv_omega
  have haddr : BitVec.ofInt 64 (a.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      a + BitVec.ofNat 64 (8*n) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    rw [show BitVec.ofInt 64 8 = 8#64 by decide,
      show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
    bv_omega
  view_vector_step 16 using hc
  view_vector_step 17 using hc
  simp [StatusFlags.from_result, hz, Effects.All]
  view_vector_step 18 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, hsi]
  view_vector_step 19 using hc
  rw [haddr]
  view_vector_load hm
  view_vector_step 20 using hc
  view_vector_step 21 using hc
  by_cases hw : limb = 0#64
  · simpa [target1, StatusFlags.from_result, hw, widthState, Effects.All] using hzero hw _
  · simp [StatusFlags.from_result, hw, Effects.All]
    view_vector_step 22 using hc
    view_vector_step 23 using hc
    by_cases hsmall : n+1 < 3
    · simp [StatusFlags.from_result, Nat.mod_eq_of_lt (show n+1 < 2^64 by omega),
        hsmall, Effects.All]
      view_vector_step 24 using hc
      simpa [hsmall, widthState] using hnonzero hw _
    · simpa [target2, StatusFlags.from_result,
        Nat.mod_eq_of_lt (show n+1 < 2^64 by omega), hsmall, Effects.All, widthState]
        using hnonzero hw _

/-- Complete descending high-limb scan, with the same countdown as
`SszLimbOrder.significantCount`. Zero limbs may be arbitrarily redundant. -/
private theorem width_scan (e : Executable) (base : Int64) (hc : SszX86.ByteView.CodeAt e base)
    (s : MachineData) (a c t : BitVec 64) (words : List (BitVec 64))
    (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ x flags,
    (SszNative.Limbs.significantCount words n = 0 → ∀ si x flags,
      Eventually (step e) P (widthState s a c si x t flags, base + 2472)) →
    (0 < SszNative.Limbs.significantCount words n →
      SszNative.Limbs.significantCount words n ≤ 2 → ∀ si x flags,
      Eventually (step e) P (widthState s a c si x t flags, base + 2481)) →
    (2 < SszNative.Limbs.significantCount words n → ∀ si x flags,
      Eventually (step e) P (widthState s a c si x t flags, base + 2851)) →
    Eventually (step e) P (widthState s a c (BitVec.ofNat 64 (n+1)) x t flags, base + 784) := by
  intro n
  induction n with
  | zero =>
    intro hn x flags hzero hfew hmany
    have target := hc.targets ("u2472", 2472) (by decide)
    view_vector_step 16 using hc
    view_vector_step 17 using hc
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
private theorem width_large (e : Executable) (base : Int64) (hc : SszX86.ByteView.CodeAt e base)
    (s : MachineData) (a si x t : BitVec 64) (flags : StatusFlags)
    (words : List (BitVec 64)) (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop)
    (hyes : SszNative.Limbs.value words = s.regs.r14.toNat → ∀ si flags,
      Eventually (step e) P
        (widthState s a (BitVec.ofNat 64 words.length)
          si 0#64 t flags, base + 2759))
    (hno : SszNative.Limbs.value words ≠ s.regs.r14.toNat → ∀ si x flags,
      Eventually (step e) P
        (widthState s a (BitVec.ofNat 64 words.length) si x t flags, base + 2851)) :
    Eventually (step e) P
      (widthState s a (BitVec.ofNat 64 words.length) si x t flags, base + 767) := by
  have pair (hfew : SszNative.Limbs.sigWords words ≤ 2) (fl : StatusFlags) :
      Eventually (step e) P
        (widthState s a (BitVec.ofNat 64 words.length) (words[1]?.getD 0#64)
          (words[0]?.getD 0#64) t fl, base + 2751) := by
    apply width_pair e base hc
    intro flags'
    by_cases he : (((words[0]?.getD 0#64) ^^^ s.regs.r14.toBitVec) |||
        words[1]?.getD 0#64) = 0#64
    · simpa only [he, ↓reduceIte] using
        hyes ((width_pair_eq words s.regs.r14.toBitVec hfew).mp he) _ flags'
    · simpa only [he, ↓reduceIte] using
        hno (fun h => he ((width_pair_eq words s.regs.r14.toBitVec hfew).mpr h)) _ _ flags'
  have low (hn : words ≠ []) (hfew : SszNative.Limbs.sigWords words ≤ 2)
      (si x : BitVec 64) (fl : StatusFlags) :
      Eventually (step e) P
        (widthState s a (BitVec.ofNat 64 words.length) si x t fl, base + 2481) :=
    width_low_words e base hc s a si x t fl words hn (by omega) hm P (pair hfew)
  have loop (fl : StatusFlags) : Eventually (step e) P
      (widthState s a (BitVec.ofNat 64 words.length)
        (BitVec.ofNat 64 (words.length+1)) x t fl, base + 784) := by
    apply width_scan e base hc s a (BitVec.ofNat 64 words.length) t words hb hm P
      words.length (Nat.le_refl _) x fl
    · intro hz si' x' fl'
      apply width_zero_count e base hc
      intro fl''
      by_cases hn : words = []
      · subst words
        change Eventually (step e) P (widthState s a 0#64 si' x' t fl'', base + 2746)
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
  view_vector_step 13 using hc
  view_vector_step 14 using hc
  view_vector_step 15 using hc
  simpa [hlea, widthState] using loop flags

def Post (s : MachineData) (base : Int64) (expected : Nat) (t : MachineState) : Prop :=
  WidthFrame s t.1 ∧
  t.2 = (if expected = s.regs.r14.toNat then base + 2759 else base + 2851) ∧
  Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 = some (t.1.regs.rax.toNat : Int) ∧
  Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 = some (t.1.regs.rcx.toNat : Int)

theorem runs (e : Executable) (base : Int64) (hc : SszX86.ByteView.CodeAt e base)
    (s : MachineData) (expected : Nat)
    (hwidth : SszNative.NatMemory.At (widthLoad s.dmem)
      (s.regs.rbp.toNat + 8) expected) :
    Eventually (step e) (Post s base expected) (s, base + 750) := by
  rcases hwidth with ⟨⟨ha, hc'⟩, hv⟩ | ⟨pointer, words, hlarge, hvalue⟩
  · have ha' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 8#64) 8 = some (0 : Int) := by
      simpa [width_reg_address] using widthLoad_eq s.dmem _ 8 0 ha
    have hc'' : Mem.loadInt s.dmem (s.regs.rbp.toBitVec + 16#64) 8 =
        some (expected : Int) := by
      simpa only [Nat.add_assoc, width_reg_address] using widthLoad_eq s.dmem _ 8 expected hc'
    have hn : (BitVec.ofNat 64 expected).toNat = expected := Nat.mod_eq_of_lt hv
    apply width_header e base hc s 0#64 (BitVec.ofNat 64 expected) (Post s base expected) ha'
    · simpa only [hn] using hc''
    intro fl
    simp only [↓reduceIte]
    apply width_small e base hc
    intro fl'
    apply width_pair e base hc
    intro fl''
    have he : ((BitVec.ofNat 64 expected ^^^ s.regs.r14.toBitVec) ||| 0#64) = 0#64 ↔
        expected = s.regs.r14.toNat := by
      simp only [BitVec.or_zero, BitVec.xor_eq_zero_iff]
      constructor
      · intro he
        exact hn.symm.trans (congrArg BitVec.toNat he)
      · intro he
        exact BitVec.eq_of_toNat_eq (hn.trans he)
    apply Eventually.done
    exact ⟨widthState_frame _ _ _ _ _ _ _, by simp only [he], ha',
      by simpa only [widthState, UInt64.toNat_ofBitVec, hn] using hc''⟩
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
    apply width_header e base hc s a c (Post s base expected) ha' hc''
    intro fl
    simp only [ha0, ↓reduceIte]
    apply width_large e base hc s a _ _ _ fl words hlen loads
    · intro he si fl'
      apply Eventually.done
      exact ⟨widthState_frame _ _ _ _ _ _ _, by simp [hvalue.symm.trans he], ha', hc''⟩
    · intro he si x fl'
      apply Eventually.done
      exact ⟨widthState_frame _ _ _ _ _ _ _, by simp [show expected ≠ s.regs.r14.toNat
        from fun h => he (hvalue.trans h)], ha', hc''⟩

end SszX86.ByteView.Vector
