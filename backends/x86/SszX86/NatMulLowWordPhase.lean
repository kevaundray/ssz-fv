import SszX86.NatMulSelect
import SszX86.NatAddSmallMath

namespace SszX86.NatMul
open SszNative
open UintCodec

structure LeftLow (s t : MachineData) (operand : NatOperand) : Prop where
  frame : ControlFrame s t
  low : t.regs.rax.toBitVec = SszNative.NatMul.lowWord operand
  pointer : t.regs.rcx = s.regs.rcx
  payload : t.regs.r8 = s.regs.r8

theorem left_low_phase_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand)
    (pointer : s.regs.rsi.toBitVec = operand.pointer)
    (payload : s.regs.rax.toBitVec = operand.payload)
    (stored : operand.At (widthLoad s.dmem)) (nonzero : operand.wordCount ≠ 0)
    (P : MachineState → Prop)
    (next : ∀ t, LeftLow s t operand → Eventually (step e) P (t, base + 709)) :
    Eventually (step e) P (s, base + 249) := by
  cases operand with
  | small limb =>
    apply left_representation_cps e base hc s P
    · intro hp flags
      apply next
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_, rfl, rfl⟩
      simpa only [SszNative.NatMul.lowWord, SszNative.NatAdd.lowWord, NatOperand.words,
        List.getElem?_cons_zero, Option.getD_some, NatOperand.payload] using payload
    · intro hp
      exact False.elim (hp pointer)
  | large p words =>
    have positive := stored.1
    have extent := stored.2.2.1
    have count := Limbs.sigWords_le_length words
    have nonempty : 0 < words.length := by
      change Limbs.sigWords words ≠ 0 at nonzero
      omega
    have pNonzero : p ≠ 0#64 := by intro hz; simp [hz] at positive
    have lengthNonzero : s.regs.rax.toBitVec ≠ 0#64 := by
      rw [payload]
      change BitVec.ofNat 64 words.length ≠ 0#64
      bv_omega
    apply left_representation_cps e base hc s P
    · intro hp
      exact False.elim (pNonzero (pointer.symm.trans hp))
    · intro hp flags
      apply left_low_cps e base hc _ (words[0]?.getD 0)
      · intro hn
        change Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 =
          some ((words[0]?.getD 0).toNat : Int)
        rw [pointer]
        have observed := stored.2.2.2 ⟨0, nonempty⟩
        change widthLoad s.dmem (p.toNat+8*0) 8 = some words[0].toNat at observed
        have first := widthLoad_eq s.dmem _ _ _ observed
        simpa only [NatOperand.pointer, Nat.mul_zero, Nat.add_zero,
          BitVec.ofNat_toNat, BitVec.setWidth_eq,
          List.getElem?_eq_getElem nonempty, Option.getD_some] using first
      · intro hz
        exact False.elim (lengthNonzero hz)
      · intro hz flags
        apply next
        exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

end SszX86.NatMul
