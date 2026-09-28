import SszX86.MeasureBitsVectorWords

namespace SszX86.Measure.Bits
open SszNative UintCodec

def VectorChecked (s : MachineData) (expected : NatOperand) (count : BitVec 128)
    (base : Int64) (t : MachineState) : Prop :=
  VectorReadFrame s t.1 ∧
    t.2 = if expected.value = count.toNat then base + 2796 else base + 2805

private theorem pair_checked (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (expected : NatOperand) (count : BitVec 128)
    (frame : VectorReadFrame s t)
    (equal : (t.regs.rdi.toBitVec = t.regs.rax.toBitVec ∧
      t.regs.r8.toBitVec = t.regs.rdx.toBitVec) ↔ expected.value = count.toNat) :
    Eventually (step e) (VectorChecked s expected count base) (t, base + 2785) := by
  apply vector_pair_cps e base hc
  intro flags
  apply Eventually.done
  refine ⟨⟨frame.memory, frame.vectors, frame.output, frame.stack,
    frame.descriptor, frame.input, frame.arena, frame.low, frame.high⟩, ?_⟩
  change (if t.regs.rdi.toBitVec = t.regs.rax.toBitVec ∧
      t.regs.r8.toBitVec = t.regs.rdx.toBitVec then base + 2796 else base + 2805) = _
  simp only [equal]

/-- The full actual inlined cmp_u128 path, including every padding limb read.
The post branches on mathematical equality, not an expected-success premise. -/
theorem vector_check_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (expected : NatOperand) (count : BitVec 128)
    (pointer : s.regs.r8.toBitVec = expected.pointer)
    (payload : s.regs.rdi.toBitVec = expected.payload)
    (lowCount : s.regs.rax.toBitVec = count.setWidth 64)
    (highCount : s.regs.rdx.toBitVec = (count >>> 64).setWidth 64)
    (stored : expected.At (widthLoad s.dmem)) :
    Eventually (step e) (VectorChecked s expected count base) (s, base + 106) := by
  apply vector_pointer_cps e base hc
  intro firstFlags
  cases expected with
  | small limb =>
    simp only [pointer, NatOperand.pointer, ↓reduceIte]
    apply vector_small_cps e base hc
    intro secondFlags
    apply pair_checked e base hc s _ (.small limb) count
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simpa only [payload, NatOperand.payload, lowCount, highCount,
        UInt64.toBitVec_zero, NatOperand.value, NatOperand.words,
        Limbs.value, Nat.mul_zero, Nat.add_zero] using small_count_words limb count
  | large ptr words =>
    obtain ⟨positive, aligned, bound, observations⟩ := stored
    have nonzero : ptr ≠ 0#64 := by intro impossible; simp [impossible] at positive
    have physical : words.length + 1 < 2^64 := by omega
    have readsWords (i : Fin words.length) :
        Mem.loadInt s.dmem (ptr + BitVec.ofNat 64 (8*i.val)) 8 = some (words[i].toNat : Int) := by
      simpa only [width_address] using widthLoad_eq _ _ _ _ (observations i)
    have lowWords (a b : BitVec 64) (flags : StatusFlags)
        (nonempty : words ≠ []) (few : Limbs.sigWords words ≤ 2) :
        Eventually (step e) (VectorChecked s (.large ptr words) count base)
          (normalizeScanState s a b flags, base + 1863) := by
      apply vector_low_words_cps e base hc _ words nonempty (by omega)
      · exact payload
      · intro i
        simpa only [normalizeScanState, pointer, NatOperand.pointer] using readsWords i
      intro terminalFlags
      apply pair_checked e base hc s _ (.large ptr words) count
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simpa only [vectorLowPair, normalizeScanState, UInt64.toBitVec_ofBitVec,
          lowCount, highCount, NatOperand.value, NatOperand.words] using vector_pair_words words count few
    have emptyCount (a b : BitVec 64) (flags : StatusFlags)
        (empty : Limbs.sigWords words = 0) :
        Eventually (step e) (VectorChecked s (.large ptr words) count base)
          (normalizeScanState s a b flags, base + 1854) := by
      apply vector_empty_cps e base hc
      intro terminalFlags
      by_cases nil : words = []
      · subst words
        simp only [normalizeScanState, payload, NatOperand.payload, List.length_nil,
          ↓reduceIte]
        apply vector_zero_cps e base hc
        intro zeroFlags
        apply pair_checked e base hc s _ (.large ptr []) count
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · simpa only [lowCount, highCount, NatOperand.value, NatOperand.words,
            List.getElem?_nil, Option.getD_none, UInt64.toBitVec_zero] using
            vector_pair_words [] count (by simp [Limbs.sigWords, Limbs.significantCount])
      · have positiveLength : 0 < words.length := by
          cases words with
          | nil => exact False.elim (nil rfl)
          | cons head rest => simp only [List.length_cons]; omega
        have countNonzero : BitVec.ofNat 64 words.length ≠ 0#64 := by
          intro zero
          have equal := congrArg BitVec.toNat zero
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show words.length < 2^64 by omega)] at equal
          omega
        simp only [normalizeScanState, payload, NatOperand.payload, countNonzero, ↓reduceIte]
        exact lowWords a b terminalFlags nil (by omega)
    have scanned (temporary : BitVec 64) (flags : StatusFlags) :
        Eventually (step e) (VectorChecked s (.large ptr words) count base)
          (normalizeScanState s (BitVec.ofNat 64 (words.length+1)) temporary flags, base + 128) := by
      apply normalize_scan e base hc s words physical
      · intro i
        simpa only [pointer, NatOperand.pointer] using readsWords i
      · exact Nat.le_refl _
      · intro scratch terminalFlags empty
        exact emptyCount 1 scratch terminalFlags empty
      · intro nonempty terminalFlags
        change Limbs.sigWords words ≠ 0 at nonempty
        change Eventually (step e) (VectorChecked s (.large ptr words) count base)
          (normalizeScanState s (BitVec.ofNat 64 (Limbs.sigWords words))
            (BitVec.ofNat 64 (Limbs.sigWords words)) terminalFlags, base + 153)
        apply vector_scan_exit_cps e base hc
        intro exitFlags
        change Eventually (step e) (VectorChecked s (.large ptr words) count base)
          (normalizeScanState s (BitVec.ofNat 64 (Limbs.sigWords words))
            (BitVec.ofNat 64 (Limbs.sigWords words)) exitFlags,
            if (BitVec.ofNat 64 (Limbs.sigWords words)).toNat < 3
              then base + 1863 else base + 2805)
        have significantBound : Limbs.sigWords words < 2^64 := by
          have bound' := Limbs.sigWords_le_length words
          omega
        by_cases few : Limbs.sigWords words < 3
        · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt significantBound, few, ↓reduceIte]
          apply lowWords (BitVec.ofNat 64 (Limbs.sigWords words))
            (BitVec.ofNat 64 (Limbs.sigWords words)) exitFlags
          · intro nil
            subst words
            simp [Limbs.sigWords, Limbs.significantCount] at nonempty
          · omega
        · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt significantBound, few, ↓reduceIte]
          apply Eventually.done
          refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
          change base + 2805 =
            if Limbs.value words = count.toNat then base + 2796 else base + 2805
          rw [ite_eq_right (vector_many_ne ptr words count (by omega))]
    simp only [pointer, NatOperand.pointer, nonzero, ↓reduceIte]
    apply vector_scan_begin_cps e base hc
    simpa only [normalizeScanState, payload, NatOperand.payload,
      BitVec.ofNat_add, BitVec.ofNat_one] using scanned s.regs.r10.toBitVec firstFlags

end SszX86.Measure.Bits
