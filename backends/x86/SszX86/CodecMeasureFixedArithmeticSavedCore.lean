import SszX86.CodecMeasureFixedArithmeticPostFramesCore
import SszX86.CodecMeasureFixedArithmeticGeometry
import SszX86.CodecMeasureFixedOutputSaved

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

/-- Provider output ends before byte72; locals72..88, saves88..136 and the
original return slot136..144 are untouched by the CALL and every helper write. -/
theorem arithmetic_upper_bytes (original caller : MachineData) (base : Int64)
    (r : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (address capacity used originalRa ra : BitVec 64) (bytes helper : Nat)
    (owned : Owned original base r desc address capacity used originalRa bytes)
    (memory : caller.dmem = original.dmem)
    (stack : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (enough : 144 + helper ≤ bytes) (call : NatArithmetic.Outcome NatOperand)
    (after : DataMem)
    (geometry : ∀ a, ArithmeticWrites call a →
      address.toNat + used.toNat ≤ a.toNat ∧ a.toNat < address.toNat + capacity.toNat)
    (frame : ∀ a : BitVec 64,
      Body.Outside a.toNat caller.regs.rsp.toNat 72 →
      Body.Outside a.toNat ((caller.regs.rsp.toBitVec - 8).toNat - helper) helper →
      (∀ reservation, call.allocation = some reservation →
        Body.Outside a.toNat (original.regs.rdx.toNat + 16) 8 ∧
        Body.Outside a.toNat reservation.pointer (8 * call.written.length)) →
      after.get? a = (arithmeticCallState caller ra).dmem.get? a) :
    ∀ offset, 72 ≤ offset → offset < 144 →
      after.get? (caller.regs.rsp.toBitVec + BitVec.ofNat 64 offset) =
        caller.dmem.get? (caller.regs.rsp.toBitVec + BitVec.ofNat 64 offset) := by
  intro offset lowOffset highOffset
  have low := owned.stack.lowEnough
  have high := owned.return_bound
  have callerNat : caller.regs.rsp.toNat = original.regs.rsp.toNat - 136 := by
    simp only [← UInt64.toNat_toBitVec] at low ⊢
    rw [stack]
    bv_omega
  have pushedNat : (caller.regs.rsp.toBitVec - 8).toNat = original.regs.rsp.toNat - 144 := by
    simp only [← UInt64.toNat_toBitVec] at low ⊢
    rw [stack]
    bv_omega
  let a := caller.regs.rsp.toBitVec + BitVec.ofNat 64 offset
  have addressNat : a.toNat = original.regs.rsp.toNat - 136 + offset := by
    dsimp only [a]
    rw [stack]
    simp only [← UInt64.toNat_toBitVec] at low high ⊢
    bv_omega
  have cursorOutside : Body.Outside a.toNat (original.regs.rdx.toNat + 16) 8 := by
    have apart := owned.header_stack
    rw [addressNat]
    unfold Body.Apart at apart
    unfold Body.Outside
    omega
  have arenaOutside : Body.Outside a.toNat (address.toNat + used.toNat)
      (capacity.toNat - used.toNat) := by
    have apart := owned.arena_stack
    have usedBound := owned.used_bound
    rw [addressNat]
    unfold Body.Apart at apart
    unfold Body.Outside
    omega
  have kept : after.get? a = (arithmeticCallState caller ra).dmem.get? a := by
    apply frame
    · rw [addressNat, callerNat]
      unfold Body.Outside
      omega
    · rw [addressNat, pushedNat]
      unfold Body.Outside
      omega
    · intro reservation allocated
      refine ⟨cursorOutside, ?_⟩
      apply arithmetic_outside_of_no_span
      intro span
      have bounds := geometry a ⟨reservation, allocated, span⟩
      have usedBound := owned.used_bound
      unfold Body.Outside at arenaOutside
      omega
  apply kept.trans
  change (Mem.storeInt caller.dmem (caller.regs.rsp.toBitVec - 8) 8 ra.toInt).get? a = _
  apply memmove_store_lookup_outside
  intro i index equal
  have small : i < 8 := by simpa only [Int.toBytes_length] using index
  have natural := congrArg BitVec.toNat equal
  have slotIndex : (caller.regs.rsp.toBitVec - 8 + BitVec.ofNat 64 i).toNat =
      original.regs.rsp.toNat - 144 + i := by
    rw [stack]
    simp only [← UInt64.toNat_toBitVec] at low high ⊢
    bv_omega
  rw [addressNat, slotIndex] at natural
  omega

theorem arithmetic_saved_of_upper_bytes (before after : DataMem) (sp : BitVec 64)
    (saved : Output.Saved)
    (bytes : ∀ offset, 72 ≤ offset → offset < 144 →
      after.get? (sp + BitVec.ofNat 64 offset) = before.get? (sp + BitVec.ofNat 64 offset))
    (stored : Output.SavedAt before sp saved) : Output.SavedAt after sp saved := by
  have load (offset : Nat) (low : 88 ≤ offset) (high : offset + 8 ≤ 144) :
      Mem.loadInt after (sp + BitVec.ofNat 64 offset) 8 =
        Mem.loadInt before (sp + BitVec.ofNat 64 offset) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    rw [memmove_addr_add]
    exact bytes (offset + i) (by omega) (by omega)
  simpa only [Output.SavedAt, load 88 (by decide) (by decide),
    load 96 (by decide) (by decide), load 104 (by decide) (by decide),
    load 112 (by decide) (by decide), load 120 (by decide) (by decide),
    load 128 (by decide) (by decide), load 136 (by decide) (by decide)] using stored

end SszX86.CodecMeasureFixed
