import SszX86.CodecEmitPartsWidthSteps

namespace SszX86.CodecEmitParts
open SszNative UintCodec

/-- The native countdown is well founded on the number of physical limbs still
to inspect. Arbitrary high-zero padding and Large [] are both retained. -/
theorem width_scan (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64) (words : List (BitVec 64))
    (physical : words.length + 1 < 2 ^ 64)
    (loads : ∀ i, i < words.length → Mem.loadInt s.dmem
      (pointer + BitVec.ofNat 64 (8 * i)) 8 = some ((words[i]?.getD 0).toNat : Int))
    (P : MachineState → Prop)
    (empty : ∀ d flags, Eventually (step e) P
      (widthState s pointer 1 d payload flags, base + 288))
    (one : 0 < words.length → ∀ flags, Eventually (step e) P
      (widthState s pointer 1 1 payload flags, base + 297)) :
    ∀ n, n ≤ words.length → Limbs.significantCount words n ≤ 1 →
    ∀ d flags, Eventually (step e) P
      (widthState s pointer (BitVec.ofNat 64 (n + 1)) d payload flags, base + 256) := by
  intro n
  induction n with
  | zero =>
    intro within significant d flags
    apply width_scan_empty e base code
    exact empty d
  | succ n ih =>
    intro within significant d flags
    by_cases zero : words[n]?.getD 0 = 0
    · apply width_scan_zero_step e base code s pointer d payload flags (n + 1)
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
      apply width_scan_one e base code s pointer d payload (words[0]?.getD 0) flags
        (by simpa only [BitVec.ofNat_eq_ofNat] using zero)
      · simpa only [Nat.mul_zero, BitVec.add_zero] using loads 0 (by omega)
      · exact one (by omega)

def WidthPost (s : MachineData) (base : Int64) (size : NatOperand)
    (state : MachineState) : Prop :=
  ∃ a count d flags,
    state.1 = widthState s a count d (BitVec.ofNat 64 size.value) flags ∧
    (state.2 = base + 300 ∨ state.2 = base + 436 ∧ size.value = 0)

/-- The real retained-plan host conversion starts at its two active Nat words,
scans the borrowed representation and reads the original low limb. The size
bound is supplied by the generated table invariant, not by a branch oracle. -/
theorem width_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (size : NatOperand)
    (stored : Emit.NatAt s.dmem (s.regs.rcx.toBitVec + 16) size)
    (fits : size.value < 2 ^ 64) :
    Eventually (step e) (WidthPost s base size) (s, base + 227) := by
  have pair := Emit.Uint.width_pair_loads s (s.regs.rcx.toBitVec + 16) size stored
  have first := pair.1
  have second : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + 24) 8 =
      some (size.payload.toNat : Int) := by
    simpa only [BitVec.add_assoc, show (16 : BitVec 64) + 8 = 24 by decide] using pair.2
  apply width_header e base code s size.pointer size.payload _ first second
  intro flags
  cases size with
  | small limb =>
    simp only [NatOperand.pointer, ↓reduceIte]
    apply Eventually.done
    refine ⟨0, s.regs.r11.toBitVec, s.regs.rdx.toBitVec, flags, ?_, Or.inl rfl⟩
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
    have normalized := Emit.Uint.low_word words fits
    have normalizedBits : words[0]?.getD 0 = BitVec.ofNat 64 (Limbs.value words) := by
      apply BitVec.eq_of_toNat_eq
      rw [normalized, BitVec.toNat_ofNat, Nat.mod_eq_of_lt valueBound]
    have physicalLoads (i : Nat) (hi : i < words.length) :
        Mem.loadInt s.dmem (pointer + BitVec.ofNat 64 (8 * i)) 8 =
          some ((words[i]?.getD 0).toNat : Int) := by
      simpa only [width_address, Fin.getElem_fin, List.getElem?_eq_getElem hi, Option.getD_some] using
        widthLoad_eq s.dmem _ 8 _ (loads ⟨i, hi⟩)
    simp only [NatOperand.pointer, nonzero, ↓reduceIte, NatOperand.payload]
    apply width_begin e base code
    have finish (count d : BitVec 64) (flags' : StatusFlags) (nonempty : 0 < words.length) :
        Eventually (step e) (WidthPost s base (.large pointer words))
          (widthState s pointer count d (BitVec.ofNat 64 words.length) flags', base + 297) := by
      apply width_low_load e base code
      · simpa only [widthState, Nat.mul_zero, BitVec.add_zero] using physicalLoads 0 nonempty
      · apply Eventually.done
        refine ⟨pointer, count, d, flags', ?_, Or.inl rfl⟩
        simp only [widthState, normalizedBits, NatOperand.value, NatOperand.words]
    rw [show (BitVec.ofNat 64 words.length + 1 : BitVec 64) =
      BitVec.ofNat 64 (words.length + 1) from (BitVec.ofNat_add words.length 1).symm]
    apply width_scan e base code s pointer (BitVec.ofNat 64 words.length) words countBound
    · exact physicalLoads
    · intro d flags'
      apply width_scan_finish e base code
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
    · exact Emit.Uint.width_significant (.large pointer words) fits

end SszX86.CodecEmitParts
