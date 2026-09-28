import SszX86.MeasureUintWidthSteps
import SszSerializeMeasure
import SszX86.EmitUintWidth

namespace SszX86.Measure.Uint
open SszNative SszNative.Serialize SszNative.Limbs UintCodec

/-- Width checking preserves the original Nat pair for successful publication. -/
structure WidthReady (s t : MachineData) (logicalWidth : NatOperand) : Prop where
  frame : WidthFrame s t
  pointer : t.regs.rcx.toBitVec = logicalWidth.pointer
  payload : t.regs.rax.toBitVec = logicalWidth.payload

/-- Complete inlined width conversion and comparison. Unlike emitter normalization,
this admits arbitrary widths, returns the original operand, and retains failure. -/
theorem width_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (logicalWidth : NatOperand)
    (stored : NatAt s.dmem (s.regs.rsi.toBitVec + 8) logicalWidth)
    (P : MachineState → Prop)
    (next : ∀ t, WidthReady s t logicalWidth → Eventually (step e) P
      (t, if s.regs.rdx.toNat * 2 ^ 64 + s.regs.rdi.toNat ≤ logicalWidth.value
        then base + 3052 else base + 3265)) :
    Eventually (step e) P (s, base + 2686) := by
  have pair := Emit.Uint.width_pair_loads s (s.regs.rsi.toBitVec + 8) logicalWidth stored
  have second : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16) 8 =
      some (logicalWidth.payload.toNat : Int) := by
    simpa only [BitVec.add_assoc, show (8 : BitVec 64) + 8 = 16 by decide] using pair.2
  have finish : ∀ current, WidthReady s current logicalWidth →
      current.regs.rsi.toNat * 2 ^ 64 + current.regs.r8.toNat = logicalWidth.value →
      Eventually (step e) P (current, base + 3253) := by
    intro current ready normalized
    apply width_compare_cps e base hc current P
    intro fl
    have required : current.regs.rdx.toNat * 2 ^ 64 + current.regs.rdi.toNat =
        s.regs.rdx.toNat * 2 ^ 64 + s.regs.rdi.toNat := by
      rw [ready.frame.requiredHigh, ready.frame.requiredLow]
    rw [required, normalized]
    apply next
    exact ⟨⟨ready.frame.memory, ready.frame.vectors, ready.frame.stack,
      ready.frame.result, ready.frame.requiredLow, ready.frame.requiredHigh⟩,
      ready.pointer, ready.payload⟩
  apply width_header_cps e base hc s logicalWidth.pointer logicalWidth.payload pair.1 second P
  intro headerFlags
  cases logicalWidth with
  | small limb =>
    simp only [NatOperand.pointer, ↓reduceIte, NatOperand.payload]
    apply width_small_cps e base hc
    intro fl
    apply finish
    · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
    · simp [widthState, NatOperand.value, NatOperand.words, Limbs.value]
  | large pointer words =>
    obtain ⟨positive, aligned, physical, observations⟩ := stored.2.2
    have nonzero : pointer ≠ 0#64 := by
      intro equal
      simp only [equal, BitVec.toNat_ofNat, Nat.zero_mod] at positive
      omega
    have countBound : words.length + 1 < 2 ^ 64 := by omega
    have countNat : (BitVec.ofNat 64 words.length).toNat = words.length :=
      Nat.mod_eq_of_lt (by omega)
    have limbRead (i : Nat) (within : i < words.length) :
        Mem.loadInt s.dmem (pointer + BitVec.ofNat 64 (8 * i)) 8 =
          some ((words[i]?.getD 0).toNat : Int) := by
      simpa only [width_address, List.getElem?_eq_getElem within, Option.getD_some, Fin.getElem_fin] using
        widthLoad_eq s.dmem _ 8 _ (observations ⟨i, within⟩)
    have borrowed : ∀ index previous flags, sigWords words ≤ 2 → 0 < words.length →
        Eventually (step e) P
          (widthState s pointer (BitVec.ofNat 64 words.length) index previous flags, base + 2755) := by
      intro index previous flags fits nonempty
      apply width_borrowed_cps e base hc _ (words[0]?.getD 0) (words[1]?.getD 0)
      · simpa only [widthState, Nat.mul_zero, BitVec.add_zero] using limbRead 0 nonempty
      · intro two
        have indexBound : 1 < words.length := by
          change (BitVec.ofNat 64 words.length).toNat ≥ 2 at two
          rw [countNat] at two
          omega
        simpa only [widthState] using limbRead 1 indexBound
      · intro fl
        apply finish
        · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
        · have high : (if (BitVec.ofNat 64 words.length).toNat < 2 then 0#64
              else words[1]?.getD 0) = words[1]?.getD 0 := by
            rw [countNat]
            by_cases short : words.length < 2
            · simp [short, List.getElem?_eq_none (by omega : words.length ≤ 1)]
            · simp [short]
          change (if (BitVec.ofNat 64 words.length).toNat < 2 then 0#64
            else words[1]?.getD 0).toNat * 2 ^ 64 + (words[0]?.getD 0).toNat = Limbs.value words
          rw [high, width_two_value words fits]
          omega
    simp only [NatOperand.pointer, nonzero, ↓reduceIte, NatOperand.payload]
    apply width_begin_cps e base hc
    change Eventually (step e) P
      (widthScanState (widthState s pointer (BitVec.ofNat 64 words.length)
        s.regs.rsi.toBitVec s.regs.r8.toBitVec headerFlags)
        (BitVec.ofNat 64 words.length + 1) s.regs.r8.toBitVec headerFlags, base + 2704)
    have index : BitVec.ofNat 64 words.length + 1 = BitVec.ofNat 64 (words.length + 1) := by
      bv_omega
    rw [index]
    apply width_scan_cps e base hc _ words countBound
    · intro i
      simpa only [widthState, List.getElem?_eq_getElem i.isLt, Option.getD_some, Fin.getElem_fin] using limbRead i.val i.isLt
    · exact Nat.le_refl _
    · intro allZero previous fl
      apply width_zero_cps e base hc
      intro fl'
      by_cases empty : words.length = 0
      · have nil : words = [] := List.length_eq_zero_iff.mp empty
        subst words
        simp only [widthScanState, widthState, List.length_nil,
          UInt64.toBitVec_ofBitVec, ↓reduceIte]
        apply width_empty_cps e base hc
        intro finalFlags
        apply finish
        · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
        · simp [NatOperand.value, NatOperand.words, Limbs.value]
      · have countNonzero : BitVec.ofNat 64 words.length ≠ 0#64 := by
          intro equal
          have value := congrArg BitVec.toNat equal
          rw [countNat] at value
          exact empty value
        simp only [widthScanState, widthState, UInt64.toBitVec_ofBitVec,
          countNonzero, ↓reduceIte]
        apply borrowed 1 previous fl' (by change significantCount words words.length ≤ 2; omega) (by omega)
    · intro countPositive fl
      apply width_count_cps e base hc
      · intro fits fl'
        have sigBound : sigWords words < 2 ^ 64 :=
          Nat.lt_of_le_of_lt (sigWords_le_length words) (by omega)
        have smallCount : sigWords words ≤ 2 := by
          change (BitVec.ofNat 64 (sigWords words)).toNat < 3 at fits
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sigBound] at fits
          omega
        have physicalPositive : 0 < words.length := by
          have := significantCount_le words words.length
          omega
        simpa only [widthScanState, widthState, sigWords] using
          borrowed (BitVec.ofNat 64 (sigWords words)) (BitVec.ofNat 64 (sigWords words))
            fl' smallCount physicalPositive
      · intro large fl'
        have sigBound : sigWords words < 2 ^ 64 :=
          Nat.lt_of_le_of_lt (sigWords_le_length words) (by omega)
        have wide : 2 < sigWords words := by
          change 3 ≤ (BitVec.ofNat 64 (sigWords words)).toNat at large
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sigBound] at large
          omega
        have lower := wide_width_bound words wide
        have highBound := s.regs.rdx.toBitVec.isLt
        have lowBound := s.regs.rdi.toBitVec.isLt
        simp only [UInt64.toNat_toBitVec] at highBound lowBound
        have fits : s.regs.rdx.toNat * 2 ^ 64 + s.regs.rdi.toNat ≤
            (NatOperand.large pointer words).value := by
          change _ ≤ Limbs.value words
          omega
        have terminal := next
          ({widthScanState (widthState s pointer (BitVec.ofNat 64 words.length)
            s.regs.rsi.toBitVec s.regs.r8.toBitVec headerFlags)
            (BitVec.ofNat 64 (sigWords words)) (BitVec.ofNat 64 (sigWords words)) fl
            with status := fl'})
          ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
        simpa only [fits, ↓reduceIte, sigWords] using terminal

end SszX86.Measure.Uint
