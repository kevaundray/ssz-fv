import SszX86.CodecMeasureFixedMemory
import SszX86.CodecMeasureFixedArithmeticCall

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

/-- The real recursive CALL writes exactly the parent's owned return-slot bytes. -/
theorem recursive_call_frame (original caller : MachineData) (ra : BitVec 64) (bytes : Nat)
    (memory : caller.dmem = original.dmem)
    (sp : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (enough : 144 ≤ bytes) :
    Codec.MemoryFrame original.dmem (arithmeticCallState caller ra).dmem
      (Codec.StackWrites original.regs.rsp.toBitVec bytes) := by
  intro a outside
  simp only [arithmeticCallState, NatDivision.callState, memory]
  apply memmove_store_lookup_outside
  intro i hi same
  have count : i < 8 := by simpa only [Int.toBytes_length] using hi
  apply outside
  apply Codec.stack_subspan original.regs.rsp.toBitVec 136 8 bytes (by omega) a
  refine ⟨i, count, ?_⟩
  simpa only [sp] using same

/-- Complete child initial ownership, obtained from the caller's current
physical resources, actual stack layout and a stored child descriptor. -/
theorem recursive_child_owned (original caller : MachineData) (base : Int64)
    (r : Codec.Footprint) (parent child : SszNative.Codec.Desc)
    (address capacity used outerReturn childReturn : BitVec 64) (bytes : Nat)
    (owned : Owned original base r parent address capacity used outerReturn bytes)
    (memory : caller.dmem = original.dmem)
    (sp : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (output : caller.regs.rdi.toBitVec = caller.regs.rsp.toBitVec)
    (header : caller.regs.rdx = original.regs.rdx)
    (stored : Codec.DescAt original.dmem r caller.regs.rsi.toBitVec child)
    (enough : 144 + stackBytes child ≤ bytes) :
    Owned (arithmeticCallState caller childReturn) base r child
      address capacity used childReturn (bytes - 144) := by
  have enoughCall : 144 ≤ bytes := by omega
  have low := owned.stack.lowEnough
  have originalBound := owned.return_bound
  have callFrame := recursive_call_frame original caller childReturn bytes memory sp enoughCall
  have readonlyStack : ∀ a, r a → ¬ Codec.StackWrites original.regs.rsp.toBitVec bytes a := by
    intro a readonly writes
    exact owned.readonly a readonly (Or.inr (Or.inl writes))
  have outputPosition : (arithmeticCallState caller childReturn).regs.rdi.toNat =
      original.regs.rsp.toNat - 136 := by
    simp only [arithmeticCallState, NatDivision.callState]
    bv_omega
  have childPosition : (arithmeticCallState caller childReturn).regs.rsp.toNat =
      original.regs.rsp.toNat - 144 := by
    simp only [arithmeticCallState, NatDivision.callState]
    bv_omega
  have childPointer : (arithmeticCallState caller childReturn).regs.rsp.toBitVec =
      original.regs.rsp.toBitVec - BitVec.ofNat 64 144 := by
    simp only [arithmeticCallState, NatDivision.callState, sp]
    bv_omega
  have headerPosition : (arithmeticCallState caller childReturn).regs.rdx = original.regs.rdx := header
  have mapping (p : BitVec 64) (n : Nat) (hm : Large.Mapped original.dmem p n) :
      Large.Mapped (arithmeticCallState caller childReturn).dmem p n := by
    simp only [arithmeticCallState, NatDivision.callState, memory]
    exact Large.mapped_store _ _ _ _ _ _ hm
  have outputSub (p n : Nat)
      (apart : Body.Apart p n (original.regs.rsp.toNat - bytes) (bytes + 8)) :
      Body.Apart p n (original.regs.rsp.toNat - 136) 72 := by
    unfold Body.Apart at *
    omega
  have childSub (p n : Nat)
      (apart : Body.Apart p n (original.regs.rsp.toNat - bytes) (bytes + 8)) :
      Body.Apart p n (original.regs.rsp.toNat - 144 - (bytes - 144)) (bytes - 144 + 8) := by
    unfold Body.Apart at *
    omega
  have headerLoad (offset : Nat) (bound : offset + 8 ≤ 24) :
      Mem.loadInt (arithmeticCallState caller childReturn).dmem
        (original.regs.rdx.toBitVec + BitVec.ofNat 64 offset) 8 =
      Mem.loadInt original.dmem (original.regs.rdx.toBitVec + BitVec.ofNat 64 offset) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    apply callFrame
    intro inside
    have atStack := stack_bounds low inside
    have hb := owned.header_bound
    have atHeader : original.regs.rdx.toNat ≤
          (original.regs.rdx.toBitVec + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat ∧
        (original.regs.rdx.toBitVec + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
          original.regs.rdx.toNat + 24 := by bv_omega
    have apart := owned.header_stack.nonempty (by decide) (by omega)
    omega
  refine ⟨stored.frame callFrame readonlyStack, ?_, owned.table_readonly, ?_, by omega,
    ?_, arithmetic_call_slot_load _ _, ?_, ?_, ?_,
    (by simpa only [arithmeticCallState, NatDivision.callState, header] using owned.header_bound), ?_, ?_, ?_,
    ?_, ?_, owned.arena_bound, owned.used_bound, owned.arena_nonzero,
    mapping _ _ owned.arena_mapped, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (callFrame _ (readonlyStack _ (owned.table_readonly i hi))).trans (owned.table i hi)
  · have stack := owned.stack.substack 144 (bytes - 144) (by omega)
    rw [childPointer]
    exact ⟨stack.lowEnough, mapping _ _ stack.mapped⟩
  · rw [childPosition]
    omega
  · rw [outputPosition]
    omega
  · have local := owned.stack.substack 64 72 (by omega)
    have pointer : original.regs.rsp.toBitVec - BitVec.ofNat 64 64 - BitVec.ofNat 64 72 =
        (arithmeticCallState caller childReturn).regs.rdi.toBitVec := by
      simp only [arithmeticCallState, NatDivision.callState]
      bv_omega
    rw [← pointer]
    exact mapping _ _ local.mapped
  · rw [outputPosition, childPosition]
    unfold Body.Apart
    omega
  · simpa only [arithmeticCallState, NatDivision.callState, header,
      BitVec.ofNat_zero, BitVec.add_zero] using (headerLoad 0 (by decide)).trans owned.address_load
  · simpa only [arithmeticCallState, NatDivision.callState, header] using
      (headerLoad 8 (by decide)).trans owned.capacity_load
  · simpa only [arithmeticCallState, NatDivision.callState, header] using
      (headerLoad 16 (by decide)).trans owned.used_load
  · rw [headerPosition, outputPosition]
    exact outputSub _ _ owned.header_stack
  · rw [headerPosition, childPosition]
    exact childSub _ _ owned.header_stack
  · rw [outputPosition]
    exact outputSub _ _ owned.arena_stack
  · rw [childPosition]
    exact childSub _ _ owned.arena_stack
  · simpa only [headerPosition] using owned.arena_header
  · intro a readonly writes
    apply owned.readonly a readonly
    rcases writes with out | stack | cursor | arena
    · apply Or.inr; apply Or.inl
      rcases out with ⟨i, hi, same⟩
      refine ⟨bytes - 136 + i, by omega, ?_⟩
      simp only [arithmeticCallState, NatDivision.callState] at same
      bv_omega
    · apply Or.inr; apply Or.inl
      rw [childPointer] at stack
      exact Codec.stack_subspan _ 144 (bytes - 144) bytes (by omega) a stack
    · exact Or.inr (Or.inr (Or.inl (by simpa only [headerPosition] using cursor)))
    · exact Or.inr (Or.inr (Or.inr arena))

end SszX86.CodecMeasureFixed
