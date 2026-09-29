import SszX86.IndicesElementTypeExec

namespace SszX86.IndicesElementType
open Kraken.X64.Parser
open SszNative UintCodec

/-- Borrowed ordinal words are retained unchanged in R8/RCX for error57. -/
def ordinalState (s : MachineData) (ordinal : NatOperand) (index previous : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r8 := UInt64.ofBitVec ordinal.pointer,
    rcx := UInt64.ofBitVec ordinal.payload, rdx := UInt64.ofBitVec index,
    r9 := UInt64.ofBitVec previous}, status := flags}

/-- Field-slice offsets are the actual Desc payload offsets:8 and24. -/
theorem field_offset_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (progressive : Bool) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rax := if progressive then 24 else 8}}, base + 218)) :
    Eventually (step e) P (s, base + if progressive then 206 else 213) := by
  cases progressive with
  | false =>
    indices_element_step 43 using hc
    simpa using next
  | true =>
    indices_element_step 41 using hc
    indices_element_step 42 using hc
    simpa using next

/-- Sequence children are borrowed pointers; no ordinal load is performed. -/
theorem child_pointer_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (progressive : Bool) (child : BitVec 64)
    (load : Mem.loadInt s.dmem
      (s.regs.rsi.toBitVec + if progressive then 8 else 24) 8 = some (child.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rax := UInt64.ofBitVec child}}, base + 297)) :
    Eventually (step e) P (s, base + if progressive then 121 else 76) := by
  cases progressive with
  | false =>
    indices_element_step 20 using hc
    indices_element_step 21 using hc
    indices_element_load load
    indices_element_step 22 using hc
    simpa using next
  | true =>
    indices_element_step 28 using hc
    indices_element_step 29 using hc
    indices_element_load load
    indices_element_step 30 using hc
    simpa using next

theorem low_word_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (word : BitVec 64)
    (load : Mem.loadInt s.dmem s.regs.r8.toBitVec 8 = some (word.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rdx := UInt64.ofBitVec word}}, base + 277)) :
    Eventually (step e) P (s, base + 274) := by
  indices_element_step 62 using hc
  indices_element_load load
  simpa using next

/-- The scan's nonzero exit accepts exactly one significant limb. -/
theorem nonzero_count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : Nat) (bound : count < 2^64)
    (countReg : s.regs.r9.toBitVec = BitVec.ofNat 64 count)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if count = 1 then base + 274 else base + 352)) :
    Eventually (step e) P (s, base + 261) := by
  have target := hc.targets ("indices_element_type_u274", 274) (by decide)
  indices_element_step 57 using hc
  indices_element_step 58 using hc
  by_cases one : count = 1
  · simpa [countReg, one, StatusFlags.from_result, target, Effects.All] using next _
  · have ne : BitVec.ofNat 64 count ≠ 1#64 := by bv_omega
    simp [countReg, ne, StatusFlags.from_result, Effects.All]
    indices_element_step 59 using hc
    simpa [one] using next _

/-- A zero physical length takes the special XOR path without dereferencing the
nonnull empty-Large pointer. A nonempty all-zero list still loads its low word. -/
theorem zero_count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (empty : s.regs.rcx.toBitVec = 0 → ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rdx := 0}, status := flags}, base + 345))
    (nonempty : s.regs.rcx.toBitVec ≠ 0 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 274)) :
    Eventually (step e) P (s, base + 269) := by
  have target := hc.targets ("indices_element_type_u343", 343) (by decide)
  indices_element_step 60 using hc
  constructor <;> indices_element_step 61 using hc
  all_goals
    by_cases hz : s.regs.rcx.toBitVec = 0#64
    · simp [hz, StatusFlags.from_result, Effects.All, target]
      indices_element_step 80 using hc
      constructor <;> simpa using empty hz _
    · simpa [hz, StatusFlags.from_result, Effects.All] using nonempty hz _

/-- Actual bound checks at277 and345. The empty-Large path and ordinary path
have opposite branch polarities but implement the same unsigned comparison. -/
theorem bounds_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : BitVec 64)
    (load : Mem.loadInt s.dmem
      (s.regs.rsi.toBitVec + s.regs.rax.toBitVec + 8) 8 = some (count.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags},
      if s.regs.rdx.toBitVec.toNat < count.toNat then base + 284 else base + 352)) :
    Eventually (step e) P (s, base + 277) ∧
    Eventually (step e) P (s, base + 345) := by
  have target352 := hc.targets ("indices_element_type_u352", 352) (by decide)
  have target284 := hc.targets ("indices_element_type_u284", 284) (by decide)
  have address : BitVec.ofInt 64
      (s.regs.rsi.toBitVec.toInt + s.regs.rax.toBitVec.toInt * 1 + 8) =
      s.regs.rsi.toBitVec + s.regs.rax.toBitVec + 8 := by
    simp [BitVec.ofInt_add, BitVec.ofInt_toInt]
  constructor
  · indices_element_step 63 using hc
    rw [address]
    indices_element_load load
    indices_element_step 64 using hc
    by_cases lt : s.regs.rdx.toBitVec.toNat < count.toNat
    · simpa [StatusFlags.from_result, NatCompare.cf_sub, lt, Effects.All] using next _
    · simpa [StatusFlags.from_result, NatCompare.cf_sub, lt, Effects.All, target352] using next _
  · indices_element_step 81 using hc
    rw [address]
    indices_element_load load
    indices_element_step 82 using hc
    by_cases lt : s.regs.rdx.toBitVec.toNat < count.toNat
    · simpa [StatusFlags.from_result, NatCompare.cf_sub, lt, Effects.All, target284] using next _
    · simpa [StatusFlags.from_result, NatCompare.cf_sub, lt, Effects.All] using next _

/-- Fields are24-byte records and their descriptor pointer is at+16. -/
theorem selected_pointer_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (fields child : BitVec 64)
    (pointer : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + s.regs.rax.toBitVec) 8 =
      some (fields.toNat : Int))
    (selected : Mem.loadInt s.dmem (fields + 24 * s.regs.rdx.toBitVec + 16) 8 =
      some (child.toNat : Int)) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rax := UInt64.ofBitVec child,
        rcx := UInt64.ofBitVec (s.regs.rdx.toBitVec * 3)}}, base + 297)) :
    Eventually (step e) P (s, base + 284) := by
  indices_element_step 65 using hc
  indices_element_load pointer
  indices_element_step 66 using hc
  indices_element_step 67 using hc
  have address : BitVec.ofInt 64
      (fields.toInt + (BitVec.ofInt 64
        (s.regs.rdx.toBitVec.toInt + s.regs.rdx.toBitVec.toInt * 2)).toInt * 8 + 16) =
      fields + 24 * s.regs.rdx.toBitVec + 16 := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    bv_omega
  rw [address]
  indices_element_load selected
  have triple : BitVec.ofInt 64
      (s.regs.rdx.toBitVec.toInt + s.regs.rdx.toBitVec.toInt * 2) =
      s.regs.rdx.toBitVec * 3 := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    bv_omega
  simpa only [triple] using next

/-- The original Position Nat header is read at PathStep+8 and+16. Only its
nonnull representation tag selects the physical backwards scan. -/
theorem prepare_ordinal_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ordinal : NatOperand)
    (pointer : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + 8) 8 =
      some (ordinal.pointer.toNat : Int))
    (payload : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + 16) 8 =
      some (ordinal.payload.toNat : Int))
    (P : MachineState → Prop)
    (small : ordinal.pointer = 0 → ∀ flags, Eventually (step e) P
      (ordinalState s ordinal ordinal.payload s.regs.r9.toBitVec flags, base + 277))
    (large : ordinal.pointer ≠ 0 → ∀ flags, Eventually (step e) P
      (ordinalState s ordinal (ordinal.payload + 1) s.regs.r9.toBitVec flags, base + 240)) :
    Eventually (step e) P (s, base + 218) := by
  have target := hc.targets ("indices_element_type_u277", 277) (by decide)
  indices_element_step 44 using hc
  indices_element_load pointer
  indices_element_step 45 using hc
  indices_element_load payload
  indices_element_step 46 using hc
  indices_element_step 47 using hc
  constructor <;> indices_element_step 48 using hc
  all_goals
    by_cases hz : ordinal.pointer = 0#64
    · simpa [ordinalState, hz, StatusFlags.from_result, Effects.All, target] using small hz _
    · simp [hz, StatusFlags.from_result, Effects.All]
      indices_element_step 49 using hc
      indices_element_step 50 using hc
      simpa [ordinalState, BitVec.ofInt_add, BitVec.ofInt_toInt] using large hz _

/-- Normalization is derived from the original physical representation. The
error continuation retains that original representation, never the trimmed one. -/
theorem ordinal_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ordinal : NatOperand)
    (pointer : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + 8) 8 =
      some (ordinal.pointer.toNat : Int))
    (payload : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + 16) 8 =
      some (ordinal.payload.toNat : Int))
    (owned : ordinal.At (widthLoad s.dmem)) (P : MachineState → Prop)
    (fits : ordinal.wordCount ≤ 1 → ∀ previous flags, Eventually (step e) P
      (ordinalState s ordinal (SszNative.Indices.word ordinal 0) previous flags,
        base + if ordinal.words.isEmpty then 345 else 277))
    (wide : 1 < ordinal.wordCount → ∀ index previous flags, Eventually (step e) P
      (ordinalState s ordinal index previous flags, base + 352)) :
    Eventually (step e) P (s, base + 218) := by
  apply prepare_ordinal_cps e base hc s ordinal pointer payload P
  · intro hz flags
    cases ordinal with
    | small word =>
      have count : (NatOperand.small word).wordCount ≤ 1 := by
        exact Limbs.sigWords_le_length [word]
      simpa [ordinalState, NatOperand.pointer, NatOperand.payload,
        NatOperand.words, SszNative.Indices.word] using fits count s.regs.r9.toBitVec flags
    | large address words =>
      have positive := owned.1
      simp only [NatOperand.pointer] at hz
      simp [hz] at positive
  · intro nonzero flags
    cases ordinal with
    | small word => exact False.elim (nonzero rfl)
    | large address words =>
      rcases owned with ⟨positive, aligned, physical, memory⟩
      have bound : words.length + 1 < 2^64 := by omega
      have loads : ∀ i : Fin words.length,
          Mem.loadInt s.dmem (address + BitVec.ofNat 64 (8*i.val)) 8 =
            some (words[i].toNat : Int) := by
        intro i
        simpa only [width_address] using widthLoad_eq s.dmem _ _ _ (memory i)
      let t := ordinalState s (.large address words) 0 s.regs.r9.toBitVec flags
      have scan :
          Eventually (step e) P
            (scanState t (BitVec.ofNat 64 (words.length+1)) s.regs.r9.toBitVec flags,
              base + 240) := by
        apply scan_cps e base hc t words bound loads P words.length (Nat.le_refl _) _ flags
        · intro zero previous fl
          apply zero_count_cps e base hc
          · intro empty fl'
            have lengthZero : words.length = 0 := by
              change BitVec.ofNat 64 words.length = 0 at empty
              bv_omega
            have wordsZero : words = [] := List.length_eq_zero.mp lengthZero
            subst words
            simpa [t, scanState, ordinalState, NatOperand.words, NatOperand.payload,
              SszNative.Indices.word] using fits (by simpa [NatOperand.wordCount,
                NatOperand.words, Limbs.sigWords] using zero) previous fl'
          · intro nonempty fl'
            have lengthPositive : 0 < words.length := by
              by_contra h
              have zeroLength : words.length = 0 := by omega
              apply nonempty
              simp [scanState, t, ordinalState, NatOperand.payload, zeroLength]
            apply low_word_cps e base hc _ (words[0]?.getD 0)
            · simpa [scanState, t, ordinalState,
                List.getElem?_eq_getElem lengthPositive] using loads ⟨0, lengthPositive⟩
            · have notEmpty : words.isEmpty = false := by
                cases words <;> simp_all
              simpa [scanState, t, ordinalState, NatOperand.words,
                SszNative.Indices.word, notEmpty] using fits
                  (by simpa [NatOperand.wordCount, NatOperand.words, Limbs.sigWords] using
                    (show Limbs.significantCount words words.length ≤ 1 by omega))
                  previous fl'
        · intro positiveCount fl
          have countBound : Limbs.significantCount words words.length < 2^64 := by
            have := Limbs.significantCount_le words words.length
            omega
          apply nonzero_count_cps e base hc _ (Limbs.significantCount words words.length)
            countBound rfl P
          intro fl'
          by_cases one : Limbs.significantCount words words.length = 1
          · simp only [one, ↓reduceIte]
            have lengthPositive : 0 < words.length := by
              have := Limbs.significantCount_le words words.length
              omega
            apply low_word_cps e base hc _ (words[0]?.getD 0)
            · simpa [scanState, t, ordinalState,
                List.getElem?_eq_getElem lengthPositive] using loads ⟨0, lengthPositive⟩
            · have notEmpty : words.isEmpty = false := by
                cases words <;> simp_all
              simpa [scanState, t, ordinalState, NatOperand.words,
                SszNative.Indices.word, notEmpty] using fits
                  (by simp [NatOperand.wordCount, NatOperand.words, Limbs.sigWords, one])
                  (BitVec.ofNat 64 (Limbs.significantCount words words.length)) fl'
          · simp only [one, ↓reduceIte]
            simpa [scanState, t, ordinalState] using wide
              (by change 1 < Limbs.significantCount words words.length; omega)
              (BitVec.ofNat 64 (Limbs.significantCount words words.length))
              (BitVec.ofNat 64 (Limbs.significantCount words words.length)) fl'
      simpa [scanState, t, ordinalState, NatOperand.payload, BitVec.ofNat_add] using scan

end SszX86.IndicesElementType
