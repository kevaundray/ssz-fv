import SszX86.EmitCore
import SszNatNarrow

namespace SszX86.Emit.Uint
open Kraken.X64.Parser
open SszNative
open BoolCodec UintCodec

/-- Successful logical measurement determines the actual byte count, before any
machine guard is executed. The number representation remains unmodified. -/
theorem measured (logicalWidth number : NatOperand) (size : Nat)
    (valid : Serialize.expectedSize (.uint logicalWidth) (.uint number) = .ok size) :
    logicalWidth.value = size ∧ number.value < 2 ^ (8 * logicalWidth.value) := by
  change (if Serialize.uintFits logicalWidth number then
    Except.ok logicalWidth.value else Except.error Ssz.Err.typeMismatch) = Except.ok size at valid
  by_cases fits : Serialize.uintFits logicalWidth number
  · simp only [fits, ↓reduceIte, Except.ok.injEq] at valid
    exact ⟨valid, (Serialize.uintFits_iff logicalWidth number).mp fits⟩
  · rw [ite_eq_right fits] at valid
    cases valid

/-- No logical width ceiling is imposed: representability follows from fitting
inside the actual usize-sized output slice. -/
theorem width_physical (logicalWidth number : NatOperand) (size : Nat) (capacity : UInt64)
    (valid : Serialize.expectedSize (.uint logicalWidth) (.uint number) = .ok size)
    (fits : size ≤ capacity.toNat) :
    logicalWidth.value < 2 ^ 64 ∧ logicalWidth.wordCount ≤ 1 := by
  have same := (measured logicalWidth number size valid).1
  have bound : logicalWidth.value < 2 ^ 64 := by
    have hc := capacity.toBitVec.isLt
    change capacity.toNat < 2 ^ 64 at hc
    omega
  exact ⟨bound, (logicalWidth.wordCount_le_iff_value_lt 1).2 (by simpa using bound)⟩

/-- The low physical word equals the complete value whenever the value fits in
one word, regardless of physical high-zero padding. -/
theorem low_word (words : List (BitVec 64)) (fits : Limbs.value words < 2 ^ 64) :
    (words[0]?.getD 0).toNat = Limbs.value words := by
  cases words with
  | nil => simp [Limbs.value]
  | cons limb rest =>
    have tail : Limbs.value rest = 0 := by
      simp only [Limbs.value] at fits
      omega
    simp [Limbs.value, tail]

/-- The same significant-count function used by the existing Nat model is the
countdown invariant of the emitter's descending width scan. -/
theorem width_significant (logicalWidth : NatOperand) (fits : logicalWidth.value < 2 ^ 64) :
    Limbs.significantCount logicalWidth.words logicalWidth.words.length ≤ 1 := by
  exact (logicalWidth.wordCount_le_iff_value_lt 1).2 (by simpa using fits)

theorem width_scan_zero (words : List (BitVec 64)) (n : Nat)
    (fits : Limbs.significantCount words (n + 1) ≤ 1)
    (many : 1 < n + 1) : words[n]?.getD 0 = 0 := by
  by_cases zero : words[n]?.getD 0 = 0
  · exact zero
  · simp only [Limbs.significantCount, zero, ↓reduceIte] at fits
    omega

/-- Limb extraction, not a truncated machine cast of the full number, supplies
all bytes. Missing limbs are the actual zero-extension branch. -/
theorem emitted_byte (logicalWidth number : NatOperand) (i : Nat) (within : i < logicalWidth.value) :
    (Serialize.emit (.uint logicalWidth) (.uint number))[i]'(by
      simpa only [Serialize.emit, Limbs.bytes, Array.size_ofFn] using within) =
      Limbs.byteAt number.words i := by
  simp only [Serialize.emit, Limbs.bytes, Array.getElem_ofFn]

theorem emitted_size (logicalWidth number : NatOperand) :
    (Serialize.emit (.uint logicalWidth) (.uint number)).size = logicalWidth.value := by
  simp only [Serialize.emit, Limbs.bytes, Array.size_ofFn]

theorem missing_limb_byte (words : List (BitVec 64)) (i : Nat)
    (outside : words.length ≤ i / 8) : Limbs.byteAt words i = 0 := by
  simp [Limbs.byteAt, List.getElem?_eq_none outside]

/-- Original pair and limb observations use ordinary byte-span separation; two
readonly operands may alias one another. -/
def Borrowed (pair : BitVec 64) (operand : NatOperand) (address : BitVec 64) : Prop :=
  InSpan address pair 16 ∨
    match operand with
    | .small _ => False
    | .large pointer words => InSpan address pointer (8 * words.length)

/-- These are only original body registers, original physical ownership, and
logical successful measurement. There are no guard or loop outcome premises. -/
structure Owned (s : MachineData) (logicalWidth number : NatOperand) (size : Nat) : Prop where
  tag : s.regs.rcx.toBitVec = 1#64
  widthAt : NatAt s.dmem (s.regs.rsi.toBitVec + 8) logicalWidth
  numberAt : NatAt s.dmem (s.regs.r12.toBitVec + 8) number
  valid : Serialize.expectedSize (.uint logicalWidth) (.uint number) = .ok size
  capacity : size ≤ s.regs.r9.toNat
  width_bound : s.regs.rsi.toNat + 24 ≤ 2 ^ 64
  number_bound : s.regs.r12.toNat + 24 ≤ 2 ^ 64
  output_bound : s.regs.r14.toNat + size ≤ 2 ^ 64
  result_bound : s.regs.rbx.toNat + 8 ≤ 2 ^ 64
  output : ∀ i, i < size → ∃ byte,
    s.dmem.get? (s.regs.r14.toBitVec + BitVec.ofNat 64 i) = some byte
  result : ∀ i, i < 8 → ∃ byte,
    s.dmem.get? (s.regs.rbx.toBitVec + BitVec.ofNat 64 i) = some byte
  apart : ∀ address, InSpan address s.regs.r14.toBitVec size →
    ¬ InSpan address s.regs.rbx.toBitVec 8
  readonly : ∀ address,
    Borrowed (s.regs.rsi.toBitVec + 8) logicalWidth address ∨
      Borrowed (s.regs.r12.toBitVec + 8) number address →
    ¬ (InSpan address s.regs.r14.toBitVec size ∨
      InSpan address s.regs.rbx.toBitVec 8)

end SszX86.Emit.Uint
