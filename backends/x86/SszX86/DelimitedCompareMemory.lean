import SszX86.DelimitedSmallPhase
import SszX86.DelimitedFinishMemory

namespace SszX86.Delimited
open UintCodec

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Extract the original header words without canonicalizing a Large capacity. -/
theorem option_header_words (s : MachineData) (cap : Nat)
    (option : SszNative.NatMemory.OptionAt (widthLoad s.dmem) s.regs.rsi.toNat (some cap)) :
    ∃ pointer payload : BitVec 64,
      widthLoad s.dmem (s.regs.rsi.toNat + 8) 8 = some pointer.toNat ∧
      widthLoad s.dmem (s.regs.rsi.toNat + 16) 8 = some payload.toNat := by
  rcases option.2 with ⟨⟨pointer, payload⟩, bound⟩ | ⟨p, words, repr, value⟩
  · refine ⟨0#64, BitVec.ofNat 64 cap, pointer, ?_⟩
    simpa only [Nat.add_assoc, Nat.reduceAdd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using payload
  · obtain ⟨positive, bound, aligned, room, pointer, payload, limbs⟩ := repr
    have countBound : words.length < 2^64 := by omega
    refine ⟨BitVec.ofNat 64 p, BitVec.ofNat 64 words.length, ?_, ?_⟩
    · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using pointer
    · simpa only [Nat.add_assoc, Nat.reduceAdd, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt countBound] using payload

/-- The lower work prefix cannot change a protected load in the original
104-byte activation's complement. Empty spans impose no pointer restriction. -/
theorem work_observe (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (active : UsesActivation data) (m n : DataMem) (sp : BitVec 64)
    (stack : sp = s.regs.rsp.toBitVec - 88)
    (written : ∀ a : BitVec 64, (∀ i < 56, a ≠ (sp - 16#64) + BitVec.ofNat 64 i) →
      n.get? a = m.get? a)
    (pointer count : Nat) (bound : pointer + count ≤ 2^64)
    (apart : Body.Apart pointer count (s.regs.rsp.toNat - 104) (activationBytes data)) :
    widthLoad n pointer count = widthLoad m pointer count := by
  have low := h.stack_low active
  simp only [activationBytes, ite_eq_left active, Body.Apart,
    ← UInt64.toNat_toBitVec] at apart low
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  apply written
  intro j hj
  rw [stack]
  bv_omega

theorem Ready.work_resources {s t : MachineData} {limit : Option Nat} {data : Ssz.Bytes}
    {address capacity used ra : BitVec 64} {ready : SszNative.Delimited.Prepared}
    (h : Owned s limit data address capacity used ra)
    (state : Ready s t limit data address capacity used ready) (active : UsesActivation data)
    (m : DataMem)
    (written : ∀ a : BitVec 64,
      (∀ i < 56, a ≠ (t.regs.rsp.toBitVec - 16#64) + BitVec.ofNat 64 i) →
        m.get? a = t.dmem.get? a) :
    Frame s m data ready.allocation ∧ SszNative.Delimited.PreparedAt (widthLoad m) ready ∧
      widthLoad m (s.regs.r8.toNat + 16) 8 = some ready.used := by
  refine ⟨frame_work s limit data address capacity used ra h active t.dmem m
    t.regs.rsp.toBitVec state.active.sp ready.allocation state.frame written, ?_, ?_⟩
  · have stored := state.stored
    cases allocated : ready.allocation with
    | none => simpa only [SszNative.Delimited.PreparedAt, allocated] using stored
    | some reservation =>
      have bounds := allocation_bounds s limit data address capacity used ra h reservation
        (state.allocation.trans allocated)
      have separated := h.arena_stack
      have usedBound := h.used_bound
      simp only [SszNative.Delimited.PreparedAt, allocated] at stored ⊢
      constructor
      · rw [work_observe s limit data address capacity used ra h active t.dmem m
          t.regs.rsp.toBitVec state.active.sp written reservation.pointer 8 (by omega)
          (by unfold Body.Apart at *; omega)]
        exact stored.1
      · rw [work_observe s limit data address capacity used ra h active t.dmem m
          t.regs.rsp.toBitVec state.active.sp written (reservation.pointer+8) 8 (by omega)
          (by unfold Body.Apart at *; omega)]
        exact stored.2
  · have bound := h.header_bound
    have separated := h.header_stack
    rw [work_observe s limit data address capacity used ra h active t.dmem m
      t.regs.rsp.toBitVec state.active.sp written (s.regs.r8.toNat+16) 8 (by omega)
      (by unfold Body.Apart at *; omega)]
    exact state.cursor

theorem compare_call_frame (t : MachineData) (pointer payload : BitVec 64) (base : Int64)
    (a : BitVec 64)
    (outside : ∀ i < 56, a ≠ (t.regs.rsp.toBitVec - 16#64) + BitVec.ofNat 64 i) :
    (callState (compareState t pointer payload) base).dmem.get? a = t.dmem.get? a :=
  (call_work_frame (compareState t pointer payload) base a outside).trans
    (compare_work_frame t pointer payload a outside)

theorem compare_call_spills (t : MachineData) (pointer payload : BitVec 64) (base : Int64) :
    let m := (callState (compareState t pointer payload) base).dmem
    Mem.loadInt m t.regs.rsp.toBitVec 8 = some (payload.toNat : Int) ∧
    Mem.loadInt m (t.regs.rsp.toBitVec + 8#64) 8 = some (pointer.toNat : Int) ∧
    Mem.loadInt m (t.regs.rsp.toBitVec + 16#64) 8 = some (t.regs.rdx.toNat : Int) ∧
    Mem.loadInt m (t.regs.rsp.toBitVec + 24#64) 8 = some (t.regs.rdi.toNat : Int) ∧
    Mem.loadInt m (t.regs.rsp.toBitVec + 32#64) 8 = some (t.regs.r14.toNat : Int) := by
  have previous := compare_spill_loads t pointer payload
  have preserved (distance : BitVec 64) (within : distance.toNat + 8 ≤ 40) :
      Mem.loadInt (callState (compareState t pointer payload) base).dmem
          (t.regs.rsp.toBitVec + distance) 8 =
        Mem.loadInt (compareMem t pointer payload) (t.regs.rsp.toBitVec + distance) 8 :=
    call_local_load _ _ distance _ within
  have zero : Mem.loadInt (callState (compareState t pointer payload) base).dmem t.regs.rsp.toBitVec 8 =
      Mem.loadInt (compareMem t pointer payload) t.regs.rsp.toBitVec 8 := by
    simpa only [BitVec.add_zero] using preserved 0#64 (by decide)
  exact ⟨zero.trans previous.1,
    (preserved 8#64 (by decide)).trans previous.2.1,
    (preserved 16#64 (by decide)).trans previous.2.2.1,
    (preserved 24#64 (by decide)).trans previous.2.2.2.1,
    (preserved 32#64 (by decide)).trans previous.2.2.2.2⟩

end SszX86.Delimited
