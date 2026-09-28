import SszX86.MeasureBytesVector
import SszX86.MeasureBytesList

namespace SszX86.Measure.Bytes
open Kraken.X64.Parser UintCodec SszNative SszNative.Limbs

/-- The vector's TEST and genuine small/large split retain the original pair. -/
theorem vector_compare (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (si x y : BitVec 64) (fl : StatusFlags)
    (owned : operand.At (widthLoad s.dmem)) (P : MachineState → Prop)
    (hp : ∀ si x fl, Eventually (step e) P
      (state s operand.pointer operand.payload si x y fl,
        if operand.value = s.regs.rax.toNat then base + 3050 else base + 3095)) :
    Eventually (step e) P
      (state s operand.pointer operand.payload si x y fl, base + 549) := by
  have target := hc.targets ("measure_u1662", 1662) (by decide)
  measure_bytes_step 43 using hc
  constructor <;> measure_bytes_step 44 using hc
  all_goals
    cases operand with
    | small limb =>
      simp [NatOperand.pointer, NatOperand.payload, StatusFlags.from_result, target, Effects.All]
      apply vector_small e base hc
      intro fl'
      apply vector_pair e base hc
      intro fl''
      have he : limb = s.regs.rax.toBitVec ↔ limb.toNat = s.regs.rax.toNat := by
        constructor
        · exact congrArg BitVec.toNat
        · exact BitVec.eq_of_toNat_eq
      simpa [NatOperand.pointer, NatOperand.payload, NatOperand.value, NatOperand.words,
        Limbs.value, BitVec.or_zero, BitVec.xor_eq_zero_iff,
        he, state] using hp 0#64 (limb ^^^ s.regs.rax.toBitVec) fl''
    | large pointer words =>
      obtain ⟨hpos, halign, hbound, hwords⟩ := owned
      have hp0 : pointer ≠ 0#64 := by
        intro hz
        simp [hz] at hpos
      have hlen : words.length + 1 < 2^64 := by omega
      have loads (i : Fin words.length) :
          Mem.loadInt s.dmem (pointer + BitVec.ofNat 64 (8*i.val)) 8 =
            some (words[i].toNat : Int) := by
        simpa only [width_address] using widthLoad_eq s.dmem _ 8 _ (hwords i)
      simp [NatOperand.pointer, NatOperand.payload, StatusFlags.from_result, hp0, Effects.All]
      apply vector_large e base hc s pointer _ _ y _ words hlen loads
      · intro he si' fl'
        simpa [NatOperand.pointer, NatOperand.payload, NatOperand.value, NatOperand.words, he]
          using hp si' 0#64 fl'
      · intro he si' x' fl'
        simpa [NatOperand.pointer, NatOperand.payload, NatOperand.value, NatOperand.words, he]
          using hp si' x' fl'

/-- No value or descriptor stores occur in this normalization prefix. -/
theorem list_prepare (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c si x y : BitVec 64) (fl : StatusFlags)
    (P : MachineState → Prop)
    (hsmall : a = 0#64 → ∀ x y fl,
      Eventually (step e) P (state s a c 0#64 x y fl, base + 1672))
    (hlarge : a ≠ 0#64 → ∀ y fl,
      Eventually (step e) P
        (state s a c (BitVec.ofNat 64 (list_nz s)) (c + 1#64) y fl, base + 672)) :
    Eventually (step e) P (state s a c si x y fl, base + 636) := by
  have target := hc.targets ("measure_u1672", 1672) (by decide)
  measure_bytes_step 62 using hc
  constructor <;> measure_bytes_step 63 using hc
  all_goals constructor <;> measure_bytes_step 64 using hc
  all_goals measure_bytes_step 65 using hc
  all_goals constructor <;> measure_bytes_step 66 using hc
  all_goals
    by_cases hz : a = 0#64
    · simpa [target, StatusFlags.from_result, hz, state, Effects.All] using hsmall hz _ _ _
    · simp [StatusFlags.from_result, hz, Effects.All]
      measure_bytes_step 67 using hc
      measure_bytes_step 68 using hc
      measure_bytes_step 69 using hc
      measure_bytes_step 70 using hc
      by_cases hs : s.regs.rax.toBitVec = 0#64
      · simpa [list_nz, hs, StatusFlags.from_result, BitVec.ofInt_add,
          BitVec.ofInt_toInt, state] using hlarge hz _ _
      · simpa [list_nz, hs, StatusFlags.from_result, BitVec.ofInt_add,
          BitVec.ofInt_toInt, state] using hlarge hz _ _

/-- Complete inlined bounded comparison, retaining padding even on Limit. -/
theorem list_compare (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (si x y : BitVec 64) (fl : StatusFlags)
    (owned : operand.At (widthLoad s.dmem)) (P : MachineState → Prop)
    (hp : ∀ si x y fl, Eventually (step e) P
      (state s operand.pointer operand.payload si x y fl,
        if s.regs.rax.toNat ≤ operand.value then base + 3050 else base + 2252)) :
    Eventually (step e) P
      (state s operand.pointer operand.payload si x y fl, base + 636) := by
  apply list_prepare e base hc
  · intro hz x' y' fl'
    cases operand with
    | small limb =>
      apply list_small e base hc
      intro si'' x'' y'' fl''
      have next := hp si'' x'' y'' fl''
      simp only [NatOperand.pointer, NatOperand.payload, NatOperand.value,
        NatOperand.words, Limbs.value, Nat.mul_zero, Nat.add_zero] at next ⊢
      with_unfolding_all exact next
    | large pointer words =>
      have hpos := owned.1
      simp [NatOperand.pointer] at hz
      simp [hz] at hpos
  · intro hn y' fl'
    cases operand with
    | small limb => exact (hn rfl).elim
    | large pointer words =>
      obtain ⟨hpos, halign, hbound, hwords⟩ := owned
      have hlen : words.length + 1 < 2^64 := by omega
      have loads (i : Fin words.length) :
          Mem.loadInt s.dmem (pointer + BitVec.ofNat 64 (8*i.val)) 8 =
            some (words[i].toNat : Int) := by
        simpa only [width_address] using widthLoad_eq s.dmem _ 8 _ (hwords i)
      have hinc : BitVec.ofNat 64 words.length + 1#64 =
          BitVec.ofNat 64 (words.length+1) := by rw [BitVec.ofNat_add]
      simp only [NatOperand.pointer, NatOperand.payload, hinc]
      apply list_large e base hc s pointer y' fl' words hlen loads
      intro si'' x'' y'' fl''
      have next := hp si'' x'' y'' fl''
      simp only [NatOperand.pointer, NatOperand.payload, NatOperand.value,
        NatOperand.words] at next ⊢
      with_unfolding_all exact next

/-- Loading the byte count does not canonicalize the descriptor operand. -/
def lengthState (s : MachineData) (n : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec n}}

theorem operand_loads (s : MachineData) (operand : NatOperand)
    (h : NatAt s.dmem (s.regs.rsi.toBitVec + 8) operand) :
    Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8) 8 = some (operand.pointer.toNat : Int) ∧
    Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16) 8 = some (operand.payload.toNat : Int) := by
  constructor
  · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using widthLoad_eq _ _ _ _ h.1
  · simpa only [width_address, BitVec.add_assoc,
      show (8 : BitVec 64) = 8#64 by decide,
      show (16 : BitVec 64) = 16#64 by decide,
      show (8#64 + 8#64) = 16#64 by decide] using widthLoad_eq _ _ _ _ h.2.1

theorem vector_header (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (n : BitVec 64)
    (h : NatAt s.dmem (s.regs.rsi.toBitVec + 8) operand)
    (hn : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 16) 8 = some (n.toNat : Int))
    (P : MachineState → Prop)
    (hp : Eventually (step e) P
      (state (lengthState s n) operand.pointer operand.payload s.regs.rsi.toBitVec
        s.regs.rdi.toBitVec s.regs.r8.toBitVec s.status, base + 549)) :
    Eventually (step e) P (s, base + 537) := by
  have loads := operand_loads s operand h
  simp only [show (8 : BitVec 64) = 8#64 by decide,
    show (16 : BitVec 64) = 16#64 by decide] at loads hn
  measure_bytes_step 40 using hc
  measure_bytes_load loads.1
  measure_bytes_step 41 using hc
  measure_bytes_load loads.2
  measure_bytes_step 42 using hc
  measure_bytes_load hn
  simpa [state, lengthState] using hp

theorem list_header (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (n : BitVec 64)
    (h : NatAt s.dmem (s.regs.rsi.toBitVec + 8) operand)
    (hn : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 16) 8 = some (n.toNat : Int))
    (P : MachineState → Prop)
    (hp : Eventually (step e) P
      (state (lengthState s n) operand.pointer operand.payload s.regs.rsi.toBitVec
        s.regs.rdi.toBitVec s.regs.r8.toBitVec s.status, base + 636)) :
    Eventually (step e) P (s, base + 624) := by
  have loads := operand_loads s operand h
  simp only [show (8 : BitVec 64) = 8#64 by decide,
    show (16 : BitVec 64) = 16#64 by decide] at loads hn
  measure_bytes_step 59 using hc
  measure_bytes_load loads.1
  measure_bytes_step 60 using hc
  measure_bytes_load loads.2
  measure_bytes_step 61 using hc
  measure_bytes_load hn
  simpa [state, lengthState] using hp

end SszX86.Measure.Bytes
