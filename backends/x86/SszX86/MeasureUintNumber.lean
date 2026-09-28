import SszX86.MeasureUintEntry
import SszX86.MeasureUintBsr
import SszX86.MeasureUintArithmetic
import SszX86.EmitUintWidth

namespace SszX86.Measure.Uint
open SszNative SszNative.Serialize SszNative.Limbs UintCodec

/-- The preparation preserves all original input pointers and either does not
write memory or writes precisely the BSR's two saved words. -/
structure NumberReady (s t : MachineData) (number : NatOperand) : Prop where
  memory : t.dmem = s.dmem ∨ t.dmem = bsrMem s
  stack : t.regs.rsp = s.regs.rsp
  result : t.regs.rbx = s.regs.rbx
  descriptor : t.regs.rsi = s.regs.rsi
  valuePointer : t.regs.r14 = s.regs.r14
  vectors : t.zmms = s.zmms
  required : pairValue t.regs.rdi.toBitVec t.regs.rdx.toBitVec = requiredBytes number.value

/-- Cut the BSR/rounding composition before introducing any concrete scan state. -/
private theorem number_nonzero_tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (number : NatOperand)
    (memoryMapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 16#64) 16)
    (nonzero : s.regs.rcx.toBitVec ≠ 0)
    (bounded : pairValue s.regs.rax.toBitVec s.regs.rdx.toBitVec +
      s.regs.rcx.toNat.log2 + 1 < 2 ^ 128)
    (formula : (pairValue s.regs.rax.toBitVec s.regs.rdx.toBitVec +
      s.regs.rcx.toNat.log2 + 1) / 8 = requiredBytes number.value)
    (P : MachineState → Prop)
    (next : ∀ t, NumberReady s t number → Eventually (step e) P (t, base + 2686)) :
    Eventually (step e) P (s, base + 1736) := by
  have highest := bsr_bound s.regs.rcx.toBitVec nonzero
  simp only [UInt64.toNat_toBitVec] at highest
  have logNat : (BitVec.ofNat 64 s.regs.rcx.toNat.log2).toNat = s.regs.rcx.toNat.log2 :=
    Nat.mod_eq_of_lt (by omega)
  have arithmetic := rounded_pair s.regs.rax.toBitVec s.regs.rdx.toBitVec
    (BitVec.ofNat 64 s.regs.rcx.toNat.log2)
    (by rw [logNat]; exact highest) (by rw [logNat]; exact bounded)
  apply bsr_cps e base hc s memoryMapped nonzero
  intro bsrFlags
  apply round_cps e base hc
  intro additionFlags quotientFlags
  apply next
  refine ⟨Or.inr rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  change pairValue
    (dividedLow (sumLow s.regs.rax.toBitVec
      ((BitVec.ofNat 64 s.regs.rcx.toNat.log2).setWidth 32 + 1#32 |>.setWidth 64))
      (sumHigh s.regs.rax.toBitVec s.regs.rdx.toBitVec
        ((BitVec.ofNat 64 s.regs.rcx.toNat.log2).setWidth 32 + 1#32 |>.setWidth 64)))
    (dividedHigh (sumHigh s.regs.rax.toBitVec s.regs.rdx.toBitVec
      ((BitVec.ofNat 64 s.regs.rcx.toNat.log2).setWidth 32 + 1#32 |>.setWidth 64))) = _
  rw [arithmetic, logNat]
  exact formula

private def numberScaledUpdate (s : MachineData) (lo hi : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rdx := UInt64.ofBitVec hi
      rax := UInt64.ofBitVec lo}
    status := flags}

private theorem scale_update_memory (s : MachineData) (lo hi : BitVec 64) (flags : StatusFlags) :
    (numberScaledUpdate s lo hi flags).dmem = s.dmem := rfl

private theorem scale_update_stack (s : MachineData) (lo hi : BitVec 64) (flags : StatusFlags) :
    (numberScaledUpdate s lo hi flags).regs.rsp = s.regs.rsp := rfl

private theorem scale_update_result (s : MachineData) (lo hi : BitVec 64) (flags : StatusFlags) :
    (numberScaledUpdate s lo hi flags).regs.rbx = s.regs.rbx := rfl

private theorem scale_update_descriptor (s : MachineData) (lo hi : BitVec 64) (flags : StatusFlags) :
    (numberScaledUpdate s lo hi flags).regs.rsi = s.regs.rsi := rfl

private theorem scale_update_valuePointer (s : MachineData) (lo hi : BitVec 64) (flags : StatusFlags) :
    (numberScaledUpdate s lo hi flags).regs.r14 = s.regs.r14 := rfl

private theorem scale_update_vectors (s : MachineData) (lo hi : BitVec 64) (flags : StatusFlags) :
    (numberScaledUpdate s lo hi flags).zmms = s.zmms := rfl

private theorem scale_update_limb (s : MachineData) (lo hi : BitVec 64) (flags : StatusFlags) :
    (numberScaledUpdate s lo hi flags).regs.rcx = s.regs.rcx := rfl

private theorem scale_update_low (s : MachineData) (lo hi : BitVec 64) (flags : StatusFlags) :
    (numberScaledUpdate s lo hi flags).regs.rax.toBitVec = lo := rfl

private theorem scale_update_high (s : MachineData) (lo hi : BitVec 64) (flags : StatusFlags) :
    (numberScaledUpdate s lo hi flags).regs.rdx.toBitVec = hi := rfl

private theorem scale_update_saved (s : MachineData) (lo hi : BitVec 64) (flags : StatusFlags) :
    bsrMem (numberScaledUpdate s lo hi flags) = bsrMem s := rfl

@[irreducible] private def numberScaled (s : MachineData) (flags : StatusFlags) : MachineData :=
  numberScaledUpdate s (scaledLow s.regs.rax.toBitVec) (scaledHigh s.regs.rax.toBitVec) flags

private theorem numberScaled_effect (s : MachineData) (flags : StatusFlags) :
    numberScaled s flags = scaledState s flags := by
  unfold numberScaled numberScaledUpdate scaledState
  rfl

private theorem numberScaled_memory (s : MachineData) (flags : StatusFlags) :
    (numberScaled s flags).dmem = s.dmem := by
  unfold numberScaled
  exact scale_update_memory s _ _ flags

private theorem numberScaled_stack (s : MachineData) (flags : StatusFlags) :
    (numberScaled s flags).regs.rsp = s.regs.rsp := by
  unfold numberScaled
  exact scale_update_stack s _ _ flags

private theorem numberScaled_result (s : MachineData) (flags : StatusFlags) :
    (numberScaled s flags).regs.rbx = s.regs.rbx := by
  unfold numberScaled
  exact scale_update_result s _ _ flags

private theorem numberScaled_descriptor (s : MachineData) (flags : StatusFlags) :
    (numberScaled s flags).regs.rsi = s.regs.rsi := by
  unfold numberScaled
  exact scale_update_descriptor s _ _ flags

private theorem numberScaled_valuePointer (s : MachineData) (flags : StatusFlags) :
    (numberScaled s flags).regs.r14 = s.regs.r14 := by
  unfold numberScaled
  exact scale_update_valuePointer s _ _ flags

private theorem numberScaled_vectors (s : MachineData) (flags : StatusFlags) :
    (numberScaled s flags).zmms = s.zmms := by
  unfold numberScaled
  exact scale_update_vectors s _ _ flags

private theorem numberScaled_limb (s : MachineData) (flags : StatusFlags) :
    (numberScaled s flags).regs.rcx = s.regs.rcx := by
  unfold numberScaled
  exact scale_update_limb s _ _ flags

private theorem numberScaled_low (s : MachineData) (flags : StatusFlags) :
    (numberScaled s flags).regs.rax.toBitVec = scaledLow s.regs.rax.toBitVec := by
  unfold numberScaled
  exact scale_update_low s _ _ flags

private theorem numberScaled_high (s : MachineData) (flags : StatusFlags) :
    (numberScaled s flags).regs.rdx.toBitVec = scaledHigh s.regs.rax.toBitVec := by
  unfold numberScaled
  exact scale_update_high s _ _ flags

private theorem numberScaled_saved (s : MachineData) (flags : StatusFlags) :
    bsrMem (numberScaled s flags) = bsrMem s := by
  unfold numberScaled
  exact scale_update_saved s _ _ flags

private theorem number_scaled_boundary_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (numberScaled s flags, base + 1736)) :
    Eventually (step e) P (s, base + 855) := by
  apply scaled_cps e base hc
  intro flags
  rw [← numberScaled_effect]
  exact next flags

/-- Scaling preserves the pre-BSR input frame and discharges the wide arithmetic bound. -/
private theorem number_scaled_tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (number : NatOperand)
    (memoryMapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 16#64) 16)
    (positive : 0 < s.regs.rax.toNat)
    (nonzero : s.regs.rcx.toBitVec ≠ 0)
    (formula : (64 * (s.regs.rax.toNat - 1) + s.regs.rcx.toNat.log2 + 8) / 8 =
      requiredBytes number.value)
    (P : MachineState → Prop)
    (next : ∀ t, NumberReady s t number → Eventually (step e) P (t, base + 2686)) :
    Eventually (step e) P (s, base + 855) := by
  have scaled := scaled_value s.regs.rax.toBitVec positive
  have countBound := s.regs.rax.toBitVec.isLt
  have highest := bsr_bound s.regs.rcx.toBitVec nonzero
  simp only [UInt64.toNat_toBitVec] at scaled countBound highest
  apply number_scaled_boundary_cps e base hc
  intro scaleFlags
  apply number_nonzero_tail_cps e base hc _ number
  · simpa only [numberScaled_memory, numberScaled_stack] using memoryMapped
  · simpa only [numberScaled_limb] using nonzero
  · rw [numberScaled_low, numberScaled_high, numberScaled_limb, scaled]
    omega
  · rw [numberScaled_low, numberScaled_high, numberScaled_limb, scaled]
    calc
      _ = (64 * (s.regs.rax.toNat - 1) + s.regs.rcx.toNat.log2 + 8) / 8 := by
        exact congrArg (fun n : Nat => n / 8) (by omega)
      _ = requiredBytes number.value := formula
  · intro t ready
    apply next t
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ready.required⟩
    · simpa only [numberScaled_memory, numberScaled_saved] using ready.memory
    · simpa only [numberScaled_stack] using ready.stack
    · simpa only [numberScaled_result] using ready.result
    · simpa only [numberScaled_descriptor] using ready.descriptor
    · simpa only [numberScaled_valuePointer] using ready.valuePointer
    · simpa only [numberScaled_vectors] using ready.vectors

/-- Complete Small/Large required-byte computation, including arbitrarily padded
zero representations, real BSR lowering, and the original 128-bit arithmetic. -/
theorem number_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (number : NatOperand)
    (stored : NatAt s.dmem (s.regs.r14.toBitVec + 8) number)
    (memoryMapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 16) 16)
    (P : MachineState → Prop)
    (next : ∀ t, NumberReady s t number → Eventually (step e) P (t, base + 2686)) :
    Eventually (step e) P (s, base + 803) := by
  have pair := Emit.Uint.width_pair_loads s (s.regs.r14.toBitVec + 8) number stored
  have second : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 16) 8 =
      some (number.payload.toNat : Int) := by
    simpa only [BitVec.add_assoc, show (8 : BitVec 64) + 8 = 16 by decide] using pair.2
  apply number_header_cps e base hc s number.pointer number.payload pair.1 second P
  intro headerFlags
  cases number with
  | small limb =>
    simp only [NatOperand.pointer, NatOperand.payload, ↓reduceIte]
    apply number_small_cps e base hc
    intro smallFlags
    by_cases zero : limb = 0#64
    · simp only [numberHeader, UInt64.toBitVec_ofBitVec, zero, ↓reduceIte]
      apply number_small_zero_cps e base hc
      intro zeroFlags
      apply next
      refine ⟨Or.inl rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      simp [pairValue, numberSmall, zero, NatOperand.value,
        NatOperand.words, Limbs.value, requiredBytes, bitLength]
    · simp only [numberHeader, UInt64.toBitVec_ofBitVec, zero, ↓reduceIte]
      apply bsr_cps e base hc
      · exact memoryMapped
      · exact zero
      · intro bsrFlags
        apply round_cps e base hc
        intro additionFlags quotientFlags
        apply next
        refine ⟨Or.inr rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
        have highest := bsr_bound limb zero
        have logNat : (BitVec.ofNat 64 limb.toNat.log2).toNat = limb.toNat.log2 :=
          Nat.mod_eq_of_lt (by omega)
        have positive : limb.toNat ≠ 0 := by
          intro equal
          apply zero
          apply BitVec.eq_of_toNat_eq
          simpa using equal
        have smallPair : pairValue 7#64 0#64 = 7 := by rfl
        have arithmetic := rounded_pair 7#64 0#64 (BitVec.ofNat 64 limb.toNat.log2)
          (by rw [logNat]; exact highest) (by rw [smallPair, logNat]; omega)
        change pairValue
          (dividedLow (sumLow 7#64 ((BitVec.ofNat 64 limb.toNat.log2).setWidth 32 + 1#32 |>.setWidth 64))
            (sumHigh 7#64 0#64 ((BitVec.ofNat 64 limb.toNat.log2).setWidth 32 + 1#32 |>.setWidth 64)))
          (dividedHigh (sumHigh 7#64 0#64 ((BitVec.ofNat 64 limb.toNat.log2).setWidth 32 + 1#32 |>.setWidth 64))) = _
        rw [arithmetic, smallPair]
        simp only [NatOperand.value, NatOperand.words, Limbs.value, Nat.mul_zero,
          Nat.add_zero, requiredBytes_round, bitLength, positive, ↓reduceIte, logNat]
        congr 1
        omega
  | large pointer words =>
    obtain ⟨positive, aligned, physical, observations⟩ := stored.2.2
    have nonzero : pointer ≠ 0#64 := by
      intro equal
      simp only [equal, BitVec.toNat_ofNat, Nat.zero_mod] at positive
      omega
    have countBound : words.length + 1 < 2 ^ 64 := by omega
    have countNat : (BitVec.ofNat 64 words.length).toNat = words.length :=
      Nat.mod_eq_of_lt (by omega)
    have limbRead (i : Fin words.length) :
        Mem.loadInt s.dmem (pointer + BitVec.ofNat 64 (8 * i.val)) 8 =
          some (words[i].toNat : Int) := by
      simpa only [width_address] using widthLoad_eq s.dmem _ 8 _ (observations i)
    simp only [NatOperand.pointer, NatOperand.payload, nonzero, ↓reduceIte]
    apply number_large_cps e base hc
    intro largeFlags
    let initial := numberLarge (numberHeader s pointer (BitVec.ofNat 64 words.length) headerFlags) largeFlags
    change Eventually (step e) P (numberScanState initial
      (BitVec.ofNat 64 words.length + 1) (BitVec.ofNat 64 words.length + 1) largeFlags, base + 832)
    have index : BitVec.ofNat 64 words.length + 1 = BitVec.ofNat 64 (words.length + 1) := by
      bv_omega
    rw [index]
    apply number_scan_cps e base hc initial words countBound
    · exact limbRead
    · exact Nat.le_refl _
    · intro allZero old flags
      apply number_large_zero_cps e base hc
      intro zeroFlags
      apply next
      refine ⟨Or.inl rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      change 0 = requiredBytes (Limbs.value words)
      exact (requiredBytes_zero_significant words allZero).symm
    · intro countPositive scanFlags
      have significantBound := sigWords_le_length words
      have representedCount : (BitVec.ofNat 64 (sigWords words)).toNat = sigWords words :=
        Nat.mod_eq_of_lt (by omega)
      apply number_scaled_tail_cps e base hc _ (.large pointer words)
      · simpa only [numberScanState, initial, numberLarge, numberHeader,
          BitVec.ofNat_eq_ofNat] using memoryMapped
      · change 0 < (BitVec.ofNat 64 (sigWords words)).toNat
        rw [representedCount]
        exact countPositive
      · exact significant_top_nonzero words words.length countPositive
      · change (64 * ((BitVec.ofNat 64 (sigWords words)).toNat - 1) +
          (words[sigWords words - 1]?.getD 0).toNat.log2 + 8) / 8 =
          requiredBytes (Limbs.value words)
        rw [representedCount, requiredBytes_significant words countPositive]
      · intro t ready
        apply next t
        exact ⟨ready.memory, ready.stack, ready.result, ready.descriptor,
          ready.valuePointer, ready.vectors, ready.required⟩

end SszX86.Measure.Uint
