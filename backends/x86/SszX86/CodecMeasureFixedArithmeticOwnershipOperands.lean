import SszX86.CodecMeasureFixedArithmeticOwnershipPhysical

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

structure ArithmeticProtected (out sp header : BitVec 64) (helper : Nat)
    (address capacity used : BitVec 64) (p n : Nat) : Prop where
  bound : p + n ≤ 2 ^ 64
  output : Body.Apart p n out.toNat 72
  activation : Body.Apart p n (sp.toNat - helper) helper
  cursor : Body.Apart p n (header.toNat + 16) 8
  arena : Body.Apart p n (address.toNat + used.toNat) (capacity.toNat - used.toNat)

def ArithmeticOperandProtected (out sp header : BitVec 64) (helper : Nat)
    (address capacity used : BitVec 64) : NatOperand → Prop
  | .small _ => True
  | .large p words => ArithmeticProtected out sp header helper address capacity used p.toNat (8 * words.length)

theorem arithmetic_operand_protected (original caller : MachineData)
    (base : Int64) (r : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (address capacity used originalRa : BitVec 64) (bytes helper : Nat)
    (owned : Owned original base r desc address capacity used originalRa bytes)
    (stack : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (enough : 144 + helper ≤ bytes) (operand : NatOperand)
    (stored : operand.At (widthLoad original.dmem))
    (safe : ArithmeticOperandSafe original bytes address capacity used operand) :
    ArithmeticOperandProtected caller.regs.rsp.toBitVec (caller.regs.rsp.toBitVec - 8)
      original.regs.rdx.toBitVec helper address capacity used operand := by
  cases operand with
  | small word => trivial
  | large pointer words =>
    obtain ⟨positive, aligned, bound, limbs⟩ := stored
    have low := owned.stack.lowEnough
    have originalBound := owned.return_bound
    have callerNat : caller.regs.rsp.toBitVec.toNat = original.regs.rsp.toNat - 136 := by
      rw [stack]
      simp only [← UInt64.toNat_toBitVec] at low ⊢
      bv_omega
    have pushedNat : (caller.regs.rsp.toBitVec - 8).toNat = original.regs.rsp.toNat - 144 := by
      rw [stack]
      simp only [← UInt64.toNat_toBitVec] at low ⊢
      bv_omega
    have rootPointer : BitVec.ofNat 64 (original.regs.rsp.toNat - bytes) =
        original.regs.rsp.toBitVec - BitVec.ofNat 64 bytes := by
      simp only [← UInt64.toNat_toBitVec] at low ⊢
      bv_omega
    have stackApart : Body.Apart pointer.toNat (8 * words.length)
        (original.regs.rsp.toNat - bytes) bytes := by
      apply arithmetic_apart_of_disjoint _ _ _ _ bound (by omega)
      intro a borrowed inside
      apply safe a
      · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using borrowed
      · exact Or.inl (by simpa only [rootPointer, Codec.StackWrites] using inside)
    have cursorApart : Body.Apart pointer.toNat (8 * words.length)
        (original.regs.rdx.toNat + 16) 8 := by
      apply arithmetic_apart_of_disjoint _ _ _ _ bound (by have := owned.header_bound; omega)
      intro a borrowed inside
      apply safe a
      · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using borrowed
      · apply Or.inr; apply Or.inl
        simpa only [← UInt64.toNat_toBitVec, width_address] using inside
    have arenaApart : Body.Apart pointer.toNat (8 * words.length)
        (address.toNat + used.toNat) (capacity.toNat - used.toNat) := by
      apply arithmetic_apart_of_disjoint _ _ _ _ bound
        (by have := owned.arena_bound; have := owned.used_bound; omega)
      intro a borrowed inside
      apply safe a
      · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using borrowed
      · apply Or.inr; apply Or.inr
        simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using inside
    refine ⟨bound, ?_, ?_, cursorApart, arenaApart⟩
    · apply arithmetic_apart_subspan stackApart
      · rw [callerNat]; omega
      · rw [callerNat]; omega
    · apply arithmetic_apart_subspan stackApart
      · rw [pushedNat]; omega
      · rw [pushedNat]; omega

end SszX86.CodecMeasureFixed
