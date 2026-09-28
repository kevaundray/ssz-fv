import SszX86.EmitUintWidthSteps

namespace SszX86.Emit.Uint
open Kraken.X64.Parser
open BoolCodec UintCodec
open SszNative

/-- The descending scan decreases the physical index. The bound concerns only
its significant prefix, never the number of padding limbs. -/
theorem width_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64) (words : List (BitVec 64))
    (physical : words.length + 1 < 2 ^ 64)
    (loads : ∀ i, i < words.length → Mem.loadInt s.dmem
      (pointer + BitVec.ofNat 64 (8 * i)) 8 = some ((words[i]?.getD 0).toNat : Int))
    (P : MachineState → Prop)
    (empty : ∀ d flags, Eventually (step e) P
      (widthState s pointer 1 d payload flags, base + 575))
    (one : 0 < words.length → ∀ flags, Eventually (step e) P
      (widthState s pointer 1 1 payload flags, base + 580)) :
    ∀ n, n ≤ words.length → Limbs.significantCount words n ≤ 1 →
    ∀ d flags, Eventually (step e) P
      (widthState s pointer (BitVec.ofNat 64 (n + 1)) d payload flags, base + 80) := by
  intro n
  induction n with
  | zero =>
    intro within significant d flags
    apply width_scan_empty e base hc
    exact empty d
  | succ n ih =>
    intro within significant d flags
    by_cases zero : words[n]?.getD 0 = 0
    · apply width_scan_zero_step e base hc s pointer d payload flags (n + 1)
        (by omega) (by omega)
      · simpa only [Nat.add_sub_cancel, zero,
          show (((0 : BitVec 64).toNat : Int)) = 0 by decide] using loads n (by omega)
      · intro flags'
        apply ih (by omega)
        simpa only [Limbs.significantCount, zero, ↓reduceIte] using significant
    · have count : n = 0 := by
        simp only [Limbs.significantCount, zero, ↓reduceIte] at significant
        omega
      subst n
      apply width_scan_one e base hc s pointer d payload (words[0]?.getD 0) flags
        (by simpa only [BitVec.ofNat_eq_ofNat] using zero)
      · simpa only [Nat.mul_zero, BitVec.add_zero] using loads 0 (by omega)
      · exact one (by omega)

/-- A complete normalization result is a concrete readonly register state. -/
def WidthPost (s : MachineData) (base : Int64) (logicalWidth : NatOperand)
    (state : MachineState) : Prop :=
  ∃ a c d flags, state.1 = widthState s a c d (BitVec.ofNat 64 logicalWidth.value) flags ∧
    (state.2 = base + 583 ∨ state.2 = base + 653 ∧ logicalWidth.value = 0)

theorem width_pair_loads (s : MachineData) (pair : BitVec 64) (operand : NatOperand)
    (stored : NatAt s.dmem pair operand) :
    Mem.loadInt s.dmem pair 8 = some (operand.pointer.toNat : Int) ∧
    Mem.loadInt s.dmem (pair + 8) 8 = some (operand.payload.toNat : Int) := by
  constructor
  · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using widthLoad_eq s.dmem _ 8 _ stored.1
  · simpa only [width_address, BitVec.ofNat_eq_ofNat] using widthLoad_eq s.dmem _ 8 _ stored.2.1

/-- Width normalization starts before the actual value-tag check and includes
all original pair loads, physical padding reads, and real conditional jumps.
The only logical premise is the bound derived from successful fitting output. -/
theorem width_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (logicalWidth : NatOperand)
    (tag : s.regs.rcx.toBitVec = 1#64)
    (stored : NatAt s.dmem (s.regs.rsi.toBitVec + 8) logicalWidth)
    (fits : logicalWidth.value < 2 ^ 64) :
    Eventually (step e) (WidthPost s base logicalWidth) (s, base + 50) := by
  have pair := width_pair_loads s (s.regs.rsi.toBitVec + 8) logicalWidth stored
  have first := pair.1
  have second : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16) 8 =
      some (logicalWidth.payload.toNat : Int) := by
    simpa only [BitVec.add_assoc, show (8 : BitVec 64) + 8 = 16 by decide] using pair.2
  apply width_tag e base hc s _ tag
  intro taggedFlags
  apply width_header e base hc {s with status := taggedFlags}
    logicalWidth.pointer logicalWidth.payload _ first second
  intro flags
  cases logicalWidth with
  | small limb =>
    simp only [NatOperand.pointer, ↓reduceIte]
    apply Eventually.done
    refine ⟨0, s.regs.rcx.toBitVec, s.regs.rdx.toBitVec, flags, ?_, Or.inl rfl⟩
    simp [widthState, NatOperand.payload, NatOperand.value, NatOperand.words, Limbs.value]
  | large pointer words =>
    obtain ⟨positive, aligned, physical, loads⟩ := stored.2.2
    have nonzero : pointer ≠ 0#64 := by
      intro equal
      simp only [equal, BitVec.toNat_ofNat, Nat.zero_mod] at positive
      omega
    have countBound : words.length + 1 < 2 ^ 64 := by omega
    have countNat : (BitVec.ofNat 64 words.length).toNat = words.length :=
      Nat.mod_eq_of_lt (by omega)
    have valueBound : Limbs.value words < 2 ^ 64 := fits
    have normalized : (words[0]?.getD 0).toNat = Limbs.value words := low_word words fits
    have normalizedBits : words[0]?.getD 0 = BitVec.ofNat 64 (Limbs.value words) := by
      apply BitVec.eq_of_toNat_eq
      rw [normalized, BitVec.toNat_ofNat, Nat.mod_eq_of_lt valueBound]
    have physicalLoads (i : Nat) (hi : i < words.length) :
        Mem.loadInt s.dmem (pointer + BitVec.ofNat 64 (8 * i)) 8 =
          some ((words[i]?.getD 0).toNat : Int) := by
      simpa only [width_address, Fin.getElem_fin, List.getElem?_eq_getElem hi, Option.getD_some] using
        widthLoad_eq s.dmem _ 8 _ (loads ⟨i, hi⟩)
    simp only [NatOperand.pointer, nonzero, ↓reduceIte, NatOperand.payload]
    apply width_begin e base hc
    have finish (c d : BitVec 64) (flags' : StatusFlags) (nonempty : 0 < words.length) :
        Eventually (step e) (WidthPost s base (.large pointer words))
          (widthState {s with status := taggedFlags} pointer c d
            (BitVec.ofNat 64 words.length) flags', base + 580) := by
      apply width_low_load e base hc
      · simpa only [widthState, Nat.mul_zero, BitVec.add_zero] using
          physicalLoads 0 nonempty
      · apply Eventually.done
        refine ⟨pointer, c, d, flags', ?_, Or.inl rfl⟩
        simp only [widthState, normalizedBits, NatOperand.value, NatOperand.words]
    rw [show (BitVec.ofNat 64 words.length + 1 : BitVec 64) =
      BitVec.ofNat 64 (words.length + 1) from (BitVec.ofNat_add words.length 1).symm]
    apply width_scan e base hc _ pointer (BitVec.ofNat 64 words.length) words countBound
    · exact physicalLoads
    · intro d flags'
      apply width_scan_finish e base hc
      intro flags''
      by_cases empty : words.length = 0
      · have nil : words = [] := List.length_eq_zero_iff.mp empty
        subst words
        simp only [List.length_nil, ↓reduceIte]
        apply Eventually.done
        refine ⟨pointer, 1, d, flags'', ?_, Or.inr ⟨rfl, rfl⟩⟩
        simp only [widthState, NatOperand.value, NatOperand.words, Limbs.value]
      · have countNonzero : BitVec.ofNat 64 words.length ≠ 0#64 := by
          intro equal
          have value := congrArg BitVec.toNat equal
          rw [countNat] at value
          exact empty value
        simp only [countNonzero, ↓reduceIte]
        exact finish 1 d flags'' (by omega)
    · intro nonempty flags'
      exact finish 1 1 flags' nonempty
    · exact Nat.le_refl _
    · exact width_significant (.large pointer words) fits

end SszX86.Emit.Uint
