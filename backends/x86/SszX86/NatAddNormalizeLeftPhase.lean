import SszX86.NatAddNormalizeEntry
import SszX86.NatAddControl
import SszNatOperandNormalization

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The complete actual zero-right normalization, preserving the original
borrowed list and never allocating or modifying memory. -/
theorem normalize_left_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand)
    (pointer : s.regs.rsi.toBitVec = operand.pointer)
    (payload : s.regs.rdx.toBitVec = operand.payload)
    (stored : operand.At (widthLoad s.dmem)) (P : MachineState → Prop)
    (next : ∀ t, ControlFrame s t → t.regs.rsi.toBitVec = operand.normalized.pointer →
      t.regs.rdx.toBitVec = operand.normalized.payload →
      Eventually (step e) P (t, base + 598)) :
    Eventually (step e) P (s, base + 271) := by
  cases operand with
  | small limb =>
    have normalized : (NatOperand.small limb).normalized = .small limb := by
      by_cases zero : limb = 0#64 <;>
        simp [NatOperand.normalized, NatOperand.fromWords, NatOperand.words, Limbs.trim, zero]
    apply left_normalize_entry e base hc s P
    · intro zero flags
      apply left_small_normalize e base hc
      intro flags
      apply next
      · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · simp only [normalized, NatOperand.pointer, UInt64.toBitVec_ofNat]
      · simpa only [normalized, NatOperand.payload] using payload
    · intro nonzero
      exact False.elim (nonzero pointer)
  | large p words =>
    have zero64 : (0 : BitVec 64) = 0#64 := by decide
    have one64 : (1 : BitVec 64) = 1#64 := by decide
    have positive := stored.1
    have extent := stored.2.2.1
    have bound : words.length+1 < 2^64 := by omega
    have nonzero : p ≠ 0#64 := by intro hz; simp [hz] at positive
    have hm : ∀ i : Fin words.length,
        Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
          some (words[i].toNat : Int) := by
      intro i
      rw [pointer]
      simpa only [NatOperand.pointer, width_address] using
        widthLoad_eq s.dmem _ _ _ (stored.2.2.2 i)
    apply left_normalize_entry e base hc s P
    · intro zero
      exact False.elim (nonzero (pointer.symm.trans zero))
    · intro hp flags
      have entry : s.regs.rdx.toBitVec + 1 = BitVec.ofNat 64 (words.length+1) := by
        rw [payload]
        simp only [NatOperand.payload, BitVec.ofNat_add, one64]
      rw [entry]
      apply left_normalize_scan e base hc s words bound hm P words.length (by omega) _ flags
      · intro d flags zero
        have nil : Limbs.trim words = [] := by
          apply List.eq_nil_of_length_eq_zero
          simpa only [Limbs.trim_length, Limbs.sigWords] using zero
        have normalized : (NatOperand.large p words).normalized = .small 0 := by
          simp [NatOperand.normalized, NatOperand.words, NatOperand.fromWords, nil]
        apply left_normalize_zero e base hc
        intro flags
        apply next
        · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        · simp only [leftPairState, normalized, NatOperand.pointer, UInt64.toBitVec_ofBitVec, zero64]
        · simp only [leftPairState, normalized, NatOperand.payload, UInt64.toBitVec_ofBitVec]
      · intro nonzeroCount flags
        have countBound := Limbs.sigWords_le_length words
        have countPositive : 0 < Limbs.sigWords words := by
          change Limbs.sigWords words ≠ 0 at nonzeroCount
          omega
        apply left_normalize_publish e base hc s _ words flags (Limbs.sigWords words)
          countPositive (by omega)
        · intro one
          have nonempty : 0 < words.length := by omega
          have first := hm ⟨0, nonempty⟩
          change Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*0)) 8 =
            some (words[0].toNat : Int) at first
          simpa only [List.getElem?_eq_getElem nonempty, Option.getD_some,
            Nat.mul_zero, BitVec.add_zero] using first
        · intro flags
          apply next
          · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
          · simp only [leftPairState, UInt64.toBitVec_ofBitVec]
            change (if Limbs.sigWords words = 1 then 0 else s.regs.rsi.toBitVec) =
              (NatOperand.fromWords p words).pointer
            rw [NatOperand.fromWords_pointer]
            by_cases one : Limbs.sigWords words = 1
            · simp [one]
            · have many : ¬ Limbs.sigWords words ≤ 1 := by omega
              simp only [one, many, ↓reduceIte]
              exact pointer
          · simp only [leftPairState, UInt64.toBitVec_ofBitVec,
              NatOperand.normalized, NatOperand.pointer, NatOperand.words, NatOperand.fromWords_payload]
            by_cases one : Limbs.sigWords words = 1
            · simp [one]
            · have many : ¬ Limbs.sigWords words ≤ 1 := by omega
              simp [one, many]

end SszX86.NatAdd
