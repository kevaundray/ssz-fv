import SszX86.NatMulWordNormalize
import SszNatOperandNormalization

namespace SszX86.NatMulWord
open SszNative UintCodec

structure BorrowFrame (s t : MachineData) : Prop where
  memory : t.dmem = s.dmem
  stack : t.regs.rsp = s.regs.rsp
  output : t.regs.rdi = s.regs.rdi
  arena : t.regs.r8 = s.regs.r8
  rbx : t.regs.rbx = s.regs.rbx
  rbp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15
  simd : t.zmms = s.zmms

protected theorem BorrowFrame.refl (s : MachineData) : BorrowFrame s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

protected theorem BorrowFrame.trans {s t u : MachineData}
    (first : BorrowFrame s t) (second : BorrowFrame t u) : BorrowFrame s u :=
  ⟨second.memory.trans first.memory, second.stack.trans first.stack,
    second.output.trans first.output, second.arena.trans first.arena,
    second.rbx.trans first.rbx, second.rbp.trans first.rbp,
    second.r12.trans first.r12, second.r13.trans first.r13,
    second.r14.trans first.r14, second.r15.trans first.r15,
    second.simd.trans first.simd⟩

def entryState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r9 := s.regs.rdx}, status := flags}

theorem entry_zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (zero : s.regs.rcx.toBitVec = 0#64) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (entryState s flags, base + 14)) :
    Eventually (step e) P (s, base) := by
  rw [← show base + Int64.ofNat 0 = base by simp]
  natmulword_step 0:0 using hc
  natmulword_step 0:1 using hc
  natmulword_step 0:2 using hc
  simp [StatusFlags.from_result, zero, Effects.All]
  natmulword_step 0:3 using hc
  constructor <;> natmulword_step 0:4 using hc
  all_goals simpa [StatusFlags.from_result, zero, entryState, Effects.All] using next _

theorem entry_one_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (one : s.regs.rcx.toBitVec = 1#64) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (entryState s flags, base + 37)) :
    Eventually (step e) P (s, base) := by
  have target := hc.targets ("natMulWord_u37", 37) (by decide)
  rw [← show base + Int64.ofNat 0 = base by simp]
  natmulword_step 0:0 using hc
  natmulword_step 0:1 using hc
  natmulword_step 0:2 using hc
  simpa [StatusFlags.from_result, one, target, entryState, Effects.All] using next _

theorem normalize_entry (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rsi.toBitVec = 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 82))
    (large : s.regs.rsi.toBitVec ≠ 0#64 → ∀ flags,
      Eventually (step e) P
        (normalizeState s (s.regs.r9.toBitVec + 1) (s.regs.r9.toBitVec + 1) flags, base + 48)) :
    Eventually (step e) P (s, base + 37) := by
  have target := hc.targets ("natMulWord_u82", 82) (by decide)
  natmulword_step 0:9 using hc
  constructor <;> natmulword_step 0:10 using hc
  all_goals
    by_cases hz : s.regs.rsi.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using small hz _
    · simp [StatusFlags.from_result, hz, Effects.All]
      natmulword_step 0:11 using hc
      natmulword_step 0:12 using hc
      simpa [normalizeState] using large hz _

/-- Complete factor-one scan of the original representation, including an empty
Large and arbitrary redundant high zeros.  No memory is written during it. -/
theorem normalize_large_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (p : BitVec 64) (words : List (BitVec 64))
    (pointer : s.regs.rsi.toBitVec = p)
    (payload : s.regs.r9.toBitVec = BitVec.ofNat 64 words.length)
    (stored : (NatOperand.large p words).At (widthLoad s.dmem)) (P : MachineState → Prop)
    (next : ∀ t pc, BorrowFrame s t →
      t.regs.rsi.toBitVec = (NatOperand.large p words).normalized.pointer →
      t.regs.r9.toBitVec = (NatOperand.large p words).normalized.payload →
      (pc = 84 ∨ pc = 373) → Eventually (step e) P (t, base + Int64.ofNat pc)) :
    Eventually (step e) P (s, base + 37) := by
  have zero64 : (0 : BitVec 64) = 0#64 := by decide
  have positive := stored.1
  have extent := stored.2.2.1
  have bound : words.length+1 < 2^64 := by omega
  have hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int) := by
    intro i
    rw [pointer]
    simpa only [width_address] using widthLoad_eq s.dmem _ _ _ (stored.2.2.2 i)
  apply normalize_entry e base hc s P
  · intro zero flags
    rw [pointer] at zero
    simp only [zero, BitVec.toNat_zero] at positive
    omega
  · intro nonzero flags
    have entry : s.regs.r9.toBitVec + 1 = BitVec.ofNat 64 (words.length+1) := by
      rw [payload]
      simp only [BitVec.ofNat_add, show (1 : BitVec 64) = 1#64 by decide]
    rw [entry]
    apply normalize_scan e base hc s words bound hm P words.length (by omega) _ flags
    · intro v flags zero
      have nil : Limbs.trim words = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa only [Limbs.trim_length, Limbs.sigWords] using zero
      have normalized : (NatOperand.large p words).normalized = .small 0 := by
        simp [NatOperand.normalized, NatOperand.words, NatOperand.fromWords, nil]
      apply normalize_zero e base hc
      intro flags
      apply next _ 373
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [pairState, normalized, NatOperand.pointer, UInt64.toBitVec_ofBitVec, zero64]
      · simp only [pairState, normalized, NatOperand.payload, UInt64.toBitVec_ofBitVec]
      · exact Or.inr rfl
    · intro nonzeroCount flags
      have countBound := Limbs.sigWords_le_length words
      have countPositive : 0 < Limbs.sigWords words := by
        change Limbs.sigWords words ≠ 0 at nonzeroCount
        omega
      apply normalize_publish e base hc s _ words flags (Limbs.sigWords words)
        countPositive (by omega)
      · intro one
        have nonempty : 0 < words.length := by omega
        have first := hm ⟨0, nonempty⟩
        change Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*0)) 8 =
          some (words[0].toNat : Int) at first
        simpa only [List.getElem?_eq_getElem nonempty, Option.getD_some,
          Nat.mul_zero, BitVec.add_zero] using first
      · intro flags
        apply next _ 84
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · simp only [pairState, UInt64.toBitVec_ofBitVec]
          change (if Limbs.sigWords words = 1 then 0 else s.regs.rsi.toBitVec) =
            (NatOperand.fromWords p words).pointer
          rw [NatOperand.fromWords_pointer]
          by_cases one : Limbs.sigWords words = 1
          · simp [one]
          · have many : ¬ Limbs.sigWords words ≤ 1 := by omega
            simp only [one, many, ↓reduceIte]
            exact pointer
        · simp only [pairState, UInt64.toBitVec_ofBitVec,
            NatOperand.normalized, NatOperand.pointer, NatOperand.words, NatOperand.fromWords_payload]
          by_cases one : Limbs.sigWords words = 1
          · simp [one]
          · have many : ¬ Limbs.sigWords words ≤ 1 := by omega
            simp [one, many]
        · exact Or.inl rfl

theorem normalize_operand_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand)
    (pointer : s.regs.rsi.toBitVec = operand.pointer)
    (payload : s.regs.r9.toBitVec = operand.payload)
    (stored : operand.At (widthLoad s.dmem)) (P : MachineState → Prop)
    (next : ∀ t pc, BorrowFrame s t →
      t.regs.rsi.toBitVec = operand.normalized.pointer →
      t.regs.r9.toBitVec = operand.normalized.payload →
      (pc = 84 ∨ pc = 373) → Eventually (step e) P (t, base + Int64.ofNat pc)) :
    Eventually (step e) P (s, base + 37) := by
  cases operand with
  | large p words => exact normalize_large_cps e base hc s p words pointer payload stored P next
  | small limb =>
    have normalized : (NatOperand.small limb).normalized = .small limb := by
      by_cases zero : limb = 0#64 <;>
        simp [NatOperand.normalized, NatOperand.words,
          NatOperand.fromWords, Limbs.trim, zero]
    apply normalize_entry e base hc s P
    · intro zero flags
      natmulword_step 0:22 using hc
      constructor
      all_goals
        apply next _ 84
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · simp [normalized, NatOperand.pointer]
        · simpa only [normalized] using payload
        · exact Or.inl rfl
    · intro nonzero
      exact False.elim (nonzero pointer)

end SszX86.NatMulWord
