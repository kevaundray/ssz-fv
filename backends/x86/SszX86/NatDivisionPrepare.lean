import SszX86.NatDivisionSelect
import SszX86.NatDivisionSmall

namespace SszX86.NatDivision
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

structure PreparationFrame (s t : MachineData) : Prop where
  memory : t.dmem = s.dmem
  vectors : t.zmms = s.zmms
  stack : t.regs.rsp = s.regs.rsp
  output : t.regs.rbx = s.regs.rbx
  arena : t.regs.r12 = s.regs.r12
  divisor : t.regs.r13 = s.regs.r13
  base_pointer : t.regs.rbp = s.regs.rbp

structure WidePrepared (s : MachineData) (words : List (BitVec 64))
    (t : MachineData) : Prop extends PreparationFrame s t where
  low : t.regs.r15.toBitVec = words[0]?.getD 0
  high : t.regs.rsi.toBitVec = words[1]?.getD 0

private theorem large_load (s : MachineData) (pointer : BitVec 64) (words : List (BitVec 64))
    (stored : (NatOperand.large pointer words).At (widthLoad s.dmem))
    (i : Nat) (hi : i < words.length) :
    Mem.loadInt s.dmem (pointer + BitVec.ofNat 64 (8*i)) 8 =
      some ((words[i]?.getD 0).toNat : Int) := by
  have h := stored.2.2.2 ⟨i, hi⟩
  change widthLoad s.dmem (pointer.toNat + 8*i) 8 = some words[i].toNat at h
  simpa only [List.getElem?_eq_getElem hi, Option.getD_some, width_address] using
    widthLoad_eq s.dmem _ _ _ h

private theorem length_word (pointer : BitVec 64) (words : List (BitVec 64))
    (s : MachineData) (stored : (NatOperand.large pointer words).At (widthLoad s.dmem)) :
    (BitVec.ofNat 64 words.length).toNat = words.length := by
  have bound := stored.2.2.1
  exact Nat.mod_eq_of_lt (by omega)

/-- Physical two-limb loading from a nonempty original Large operand, allowing
arbitrarily many stored high zero limbs. -/
theorem prepare_borrowed_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer : BitVec 64) (words : List (BitVec 64))
    (hp : s.regs.rsi.toBitVec = pointer)
    (hn : s.regs.rdx.toBitVec = BitVec.ofNat 64 words.length)
    (stored : (NatOperand.large pointer words).At (widthLoad s.dmem))
    (nonempty : 0 < words.length) (P : MachineState → Prop)
    (next : ∀ t, WidePrepared s words t → Eventually (step e) P (t, base + 250)) :
    Eventually (step e) P (s, base + 226) := by
  have lengthNat : s.regs.rdx.toBitVec.toNat = words.length := by
    rw [hn, length_word pointer words s stored]
  apply borrowed_cps e base hc s (words[0]?.getD 0) (words[1]?.getD 0)
  · simpa only [hp, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      large_load s pointer words stored 0 nonempty
  · intro two
    simpa only [hp] using large_load s pointer words stored 1 (by omega)
  intro flags
  apply next
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
  change (if s.regs.rdx.toBitVec.toNat < 2 then 0 else words[1]?.getD 0) = words[1]?.getD 0
  by_cases short : s.regs.rdx.toBitVec.toNat < 2
  · rw [ite_eq_left short, List.getElem?_eq_none (by omega)]
    rfl
  · exact ite_eq_right short

/-- The zero-scan branch still performs the genuine original-length test;
empty borrowed storage is never dereferenced. -/
theorem prepare_zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer : BitVec 64) (words : List (BitVec 64))
    (hp : s.regs.rsi.toBitVec = pointer)
    (hn : s.regs.rdx.toBitVec = BitVec.ofNat 64 words.length)
    (stored : (NatOperand.large pointer words).At (widthLoad s.dmem))
    (P : MachineState → Prop)
    (next : ∀ t, WidePrepared s words t → Eventually (step e) P (t, base + 250)) :
    Eventually (step e) P (s, base + 221) := by
  have lengthNat : s.regs.rdx.toBitVec.toNat = words.length := by
    rw [hn, length_word pointer words s stored]
  apply zero_dispatch_cps e base hc s P
  · intro zero flags
    have nil : words = [] := by
      apply List.length_eq_zero_iff.mp
      have hz := congrArg BitVec.toNat zero
      change s.regs.rdx.toBitVec.toNat = 0 at hz
      omega
    apply empty_cps e base hc
    intro flags'
    apply next
    subst words
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
  · intro nz flags
    apply prepare_borrowed_cps e base hc _ pointer words
    · exact hp
    · exact hn
    · exact stored
    · by_cases positive : 0 < words.length
      · exact positive
      · have zero : words.length = 0 := by omega
        apply False.elim (nz _)
        rw [hn, zero]
        rfl
    · intro t ht
      apply next t
      exact ⟨⟨ht.memory, ht.vectors, ht.stack, ht.output, ht.arena, ht.divisor,
        ht.base_pointer⟩, ht.low, ht.high⟩

/-- Complete operand dispatch from the post-prologue PC20. The original
representation determines all reads; only its significant count selects the
two-word or allocated path. -/
theorem prepare_operand_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand)
    (pointer : s.regs.rsi.toBitVec = operand.pointer)
    (payload : s.regs.rdx.toBitVec = operand.payload)
    (stored : operand.At (widthLoad s.dmem)) (P : MachineState → Prop)
    (wide : operand.wordCount ≤ 2 → ∀ t, WidePrepared s operand.words t →
      Eventually (step e) P (t, base + 250))
    (large : 2 < operand.wordCount → ∀ flags, Eventually (step e) P
      (scanState s (BitVec.ofNat 64 operand.wordCount)
        (BitVec.ofNat 64 operand.wordCount) flags, base + 83)) :
    Eventually (step e) P (s, base + 20) := by
  cases operand with
  | small limb =>
    have pp : s.regs.rsi.toBitVec = 0 := pointer
    have pv : s.regs.rdx.toBitVec = limb := payload
    apply entry_dispatch_cps e base hc s P
    · intro _ flags
      apply immediate_cps e base hc
      intro flags'
      apply wide
      · change Limbs.significantCount [limb] 1 ≤ 2
        have bound := Limbs.significantCount_le [limb] 1
        omega
      · refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, rfl⟩
        exact pv
    · intro nonzero
      exact False.elim (nonzero pp)
  | large p words =>
    have pp : s.regs.rsi.toBitVec = p := pointer
    have pv : s.regs.rdx.toBitVec = BitVec.ofNat 64 words.length := payload
    have hb : words.length + 1 < 2^64 := by
      have bound := stored.2.2.1
      omega
    have pnonzero : p ≠ 0 := by
      intro zero
      have positive := stored.1
      simp [zero] at positive
    have counts : (NatOperand.large p words).wordCount = Limbs.sigWords words := rfl
    have smallCount : Limbs.sigWords words < 2^64 :=
      Nat.lt_of_le_of_lt (Limbs.sigWords_le_length words) (by omega)
    apply entry_dispatch_cps e base hc s P
    · intro zero
      exact False.elim (pnonzero (pp.symm.trans zero))
    · intro _ flags
      have plusOne : s.regs.rdx.toBitVec + 1 = BitVec.ofNat 64 (words.length+1) := by
        change s.regs.rdx.toBitVec + 1#64 = BitVec.ofNat 64 (words.length+1)
        rw [pv, BitVec.ofNat_add]
      rw [plusOne]
      apply scan e base hc s words hb
      · intro i
        have h := large_load s p words stored i.val i.isLt
        rw [List.getElem?_eq_getElem i.isLt, Option.getD_some] at h
        change Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
          some (words[i.val].toNat : Int)
        simpa only [pp] using h
      · exact Nat.le_refl _
      · intro zero c flags'
        apply prepare_zero_cps e base hc _ p words
        · exact pp
        · exact pv
        · exact stored
        · intro t prepared
          apply wide
          · change Limbs.significantCount words words.length ≤ 2
            omega
          · exact ⟨⟨prepared.memory, prepared.vectors, prepared.stack, prepared.output,
              prepared.arena, prepared.divisor, prepared.base_pointer⟩,
              prepared.low, prepared.high⟩
      · intro positive flags'
        apply count_dispatch_cps e base hc
        · intro small flags''
          apply prepare_borrowed_cps e base hc _ p words
          · exact pp
          · exact pv
          · exact stored
          · have bound := Limbs.significantCount_le words words.length
            omega
          · intro t prepared
            apply wide
            · change Limbs.sigWords words ≤ 2
              change (BitVec.ofNat 64 (Limbs.sigWords words)).toNat < 3 at small
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt smallCount] at small
              omega
            · exact ⟨⟨prepared.memory, prepared.vectors, prepared.stack, prepared.output,
                prepared.arena, prepared.divisor, prepared.base_pointer⟩,
                prepared.low, prepared.high⟩
        · intro big flags''
          have bound : 2 < (NatOperand.large p words).wordCount := by
            change 3 ≤ (BitVec.ofNat 64 (Limbs.sigWords words)).toNat at big
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt smallCount] at big
            change 2 < Limbs.sigWords words
            omega
          simpa only [scanState, NatOperand.wordCount, NatOperand.words, Limbs.sigWords]
            using large bound flags''

end SszX86.NatDivision
