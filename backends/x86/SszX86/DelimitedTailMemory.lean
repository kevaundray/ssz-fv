import SszX86.DelimitedLimit
import SszNatABI

namespace SszX86.Delimited
open UintCodec

set_option autoImplicit false

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

private theorem tagged_memory (s : MachineData) :
    (tagged s).dmem = Mem.storeInt s.dmem
      (s.regs.rdi.toBitVec + BitVec.ofNat 64 0) 8 s.regs.rax.toBitVec.toInt := by
  simp only [tagged, BitVec.add_zero]

private theorem tail_observe (m : DataMem) (out : UInt64) (distance count : Nat) :
    widthLoad m (out.toNat + distance) count =
      BoolCodec.observe m out.toBitVec distance count := by
  simp only [widthLoad, BoolCodec.observe, ← UInt64.toNat_toBitVec, width_address]

private theorem tail_observe_zero (m : DataMem) (out : UInt64) (count : Nat) :
    widthLoad m out.toNat count = BoolCodec.observe m out.toBitVec 0 count := by
  simpa only [Nat.add_zero] using tail_observe m out 0 count

/-- The success stores expose the native words without imposing any restriction
on the source pointer, byte length, or the high count limb. -/
theorem success_fields (s : MachineData) (flags : StatusFlags)
    (bound : s.regs.rdi.toNat + 76 ≤ 2^64) :
    let observe := widthLoad (tagged (successReady s flags)).dmem
    observe s.regs.rdi.toNat 8 = some 0 ∧
    observe (s.regs.rdi.toNat + 16) 1 = some 3 ∧
    observe (s.regs.rdi.toNat + 32) 8 = some s.regs.rdx.toNat ∧
    observe (s.regs.rdi.toNat + 40) 8 = some s.regs.rcx.toNat ∧
    observe (s.regs.rdi.toNat + 48) 8 = some s.regs.r14.toNat ∧
    observe (s.regs.rdi.toNat + 56) 8 = some s.regs.rbp.toNat := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [tail_observe, tail_observe_zero]
  all_goals
    simp (disch := first | simpa only [UInt64.toNat_toBitVec] using bound | omega | decide) only
      [tagged_memory, successReady, successMem, observe_apart, BoolCodec.observe_store64,
        UInt64.toNat_toBitVec]
  all_goals
    first
    | rfl
    | rw [observe_same _ _ _ _ _ (by decide)]; decide

theorem success_frame (s : MachineData) (flags : StatusFlags) (a : BitVec 64)
    (outside : ∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) :
    (tagged (successReady s flags)).dmem.get? a = s.dmem.get? a := by
  simp (disch := first | assumption | omega | decide) only
    [tagged_memory, successReady, successMem, BoolCodec.store_frame (limit := 76)]

theorem scratch_result (s : MachineData) (flags : StatusFlags)
    (bound : s.regs.rdi.toNat + 76 ≤ 2^64) :
    SszNative.UintCodec.errorAt
      (widthLoad (tagged (errorTailReady (scratchReady s flags))).dmem)
      s.regs.rdi.toNat 32768 0 0 := by
  refine ⟨?_, ?_, ?_, Or.inl ⟨⟨?_, ?_⟩, by decide⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals simp only [Nat.add_assoc, Nat.reduceAdd, tail_observe, tail_observe_zero]
  all_goals
    simp (disch := first | simpa only [UInt64.toNat_toBitVec] using bound | omega | decide) only
      [tagged_memory, errorTailReady, errorTailMem, scratchReady, scratchMem,
        UInt64.toBitVec_ofNat, observe_apart, observe_same]
  all_goals decide

theorem scratch_frame (s : MachineData) (flags : StatusFlags) (a : BitVec 64)
    (outside : ∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) :
    (tagged (errorTailReady (scratchReady s flags))).dmem.get? a = s.dmem.get? a := by
  simp (disch := first | assumption | omega | decide) only
    [tagged_memory, errorTailReady, errorTailMem, scratchReady, scratchMem,
      UInt64.toBitVec_ofNat, BoolCodec.store_frame (limit := 76)]

/-- Capacity headers are copied verbatim; actual-count headers are the two
words selected before the comparison, including the allocation on rejection. -/
theorem limit_fields (s : MachineData) (pointer payload : BitVec 64)
    (bound : s.regs.rdi.toNat + 76 ≤ 2^64) :
    let observe := widthLoad (tagged (errorTailReady (limitReady s pointer payload))).dmem
    observe s.regs.rdi.toNat 8 = some 1 ∧
    observe (s.regs.rdi.toNat + 8) 8 = some 1 ∧
    observe (s.regs.rdi.toNat + 16) 8 = some 0 ∧
    observe (s.regs.rdi.toNat + 24) 8 = some pointer.toNat ∧
    observe (s.regs.rdi.toNat + 32) 8 = some payload.toNat ∧
    observe (s.regs.rdi.toNat + 40) 8 = some s.regs.rsi.toNat ∧
    observe (s.regs.rdi.toNat + 48) 8 = some s.regs.r15.toNat ∧
    observe (s.regs.rdi.toNat + 56) 8 = some 0 ∧
    observe (s.regs.rdi.toNat + 64) 8 = some 0 ∧
    observe (s.regs.rdi.toNat + 72) 4 = some 2 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [tail_observe, tail_observe_zero]
  all_goals
    simp (disch := first | simpa only [UInt64.toNat_toBitVec] using bound | omega | decide) only
      [tagged_memory, errorTailReady, errorTailMem, limitReady, limitMem, limitHeadMem,
        UInt64.toBitVec_ofNat, observe_apart, BoolCodec.observe_store64, UInt64.toNat_toBitVec]
  all_goals
    first
    | rfl
    | rw [observe_same _ _ _ _ _ (by decide)]; decide

theorem limit_frame (s : MachineData) (pointer payload : BitVec 64) (a : BitVec 64)
    (outside : ∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) :
    (tagged (errorTailReady (limitReady s pointer payload))).dmem.get? a = s.dmem.get? a := by
  simp (disch := first | assumption | omega | decide) only
    [tagged_memory, errorTailReady, errorTailMem, limitReady, limitMem, limitHeadMem,
      UInt64.toBitVec_ofNat, BoolCodec.store_frame (limit := 76)]

theorem limit_result (s : MachineData) (pointer payload : BitVec 64)
    (expected actual : Nat) (bound : s.regs.rdi.toNat + 76 ≤ 2^64)
    (expectedPair : SszNative.NatMemory.Pair
      (widthLoad (tagged (errorTailReady (limitReady s pointer payload))).dmem)
      pointer payload expected)
    (actualPair : SszNative.NatMemory.Pair
      (widthLoad (tagged (errorTailReady (limitReady s pointer payload))).dmem)
      s.regs.rsi.toBitVec s.regs.r15.toBitVec actual) :
    SszNative.UintCodec.errorAt
      (widthLoad (tagged (errorTailReady (limitReady s pointer payload))).dmem)
      s.regs.rdi.toNat 2 expected actual := by
  obtain ⟨tag, errorTag, index, ep, en, ap, an, zp, zn, reason⟩ :=
    limit_fields s pointer payload bound
  refine ⟨tag, errorTag, index, ?_, ?_, Or.inl ⟨⟨zp, ?_⟩, by decide⟩, reason⟩
  · apply SszNative.NatMemory.Pair.at _ pointer payload expected _ expectedPair ep
    simpa only [Nat.add_assoc, Nat.reduceAdd] using en
  · apply SszNative.NatMemory.Pair.at _ s.regs.rsi.toBitVec s.regs.r15.toBitVec
      actual _ actualPair ap
    simpa only [Nat.add_assoc, Nat.reduceAdd, UInt64.toNat_toBitVec] using an
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using zn

end SszX86.Delimited
