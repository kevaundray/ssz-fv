import SszX86.DelimitedCountPhase
import SszX86.DelimitedWorkMemory
import SszX86.DelimitedTailMemory

namespace SszX86.Delimited
open UintCodec

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Compose a terminal output-only write footprint with the actual prefix. -/
theorem frame_output (s : MachineData) (m n : DataMem) (data : Ssz.Bytes)
    (allocation : Option SszNative.Arena.Reservation)
    (bound : s.regs.rdi.toNat + 76 ≤ 2^64) (before : Frame s m data allocation)
    (written : ∀ a : BitVec 64, (∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) →
      n.get? a = m.get? a) : Frame s n data allocation := by
  intro a output activation arena
  rw [written a (fun i hi => Body.outside_byte s.regs.rdi.toBitVec a 76 i bound output hi)]
  exact before a output activation arena

/-- Local comparison writes fit the actual lower56 bytes, not the saved words. -/
theorem frame_work (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (active : UsesActivation data) (m n : DataMem) (sp : BitVec 64)
    (stack : sp = s.regs.rsp.toBitVec - 88)
    (allocation : Option SszNative.Arena.Reservation) (before : Frame s m data allocation)
    (written : ∀ a : BitVec 64, (∀ i < 56, a ≠ (sp - 16#64) + BitVec.ofNat 64 i) →
      n.get? a = m.get? a) : Frame s n data allocation := by
  intro a output activation arena
  have base : sp - 16#64 = s.regs.rsp.toBitVec - 104 := by rw [stack]; bv_omega
  rw [written a (by
    intro i hi
    rw [base]
    exact activation_outside s limit data address capacity used ra h active a activation i (by omega))]
  exact before a output activation arena

theorem activation_output_disjoint (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (active : UsesActivation data) :
    Large.Disjoint (s.regs.rsp.toBitVec - 104) s.regs.rdi.toBitVec 104 76 := by
  have low := h.stack_low active
  have start : (s.regs.rsp.toBitVec - 104).toNat = s.regs.rsp.toNat - 104 := by
    simp only [← UInt64.toNat_toBitVec] at low ⊢
    bv_omega
  apply Body.apart_bytes
  · rw [start]
    have bound := s.regs.rsp.toBitVec.isLt
    simp only [UInt64.toNat_toBitVec] at bound
    omega
  · exact h.output_bound
  · simpa only [start, activationBytes, ite_eq_left active, UInt64.toNat_toBitVec]
      using h.output_stack.symm

theorem savedAt_output (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (active : UsesActivation data) (m n : DataMem) (sp : BitVec 64)
    (stack : sp = s.regs.rsp.toBitVec - 88) (saved : SavedAt m sp s)
    (written : ∀ a : BitVec 64, (∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) →
      n.get? a = m.get? a) : SavedAt n sp s := by
  have separated := activation_output_disjoint s limit data address capacity used ra h active
  apply savedAt_congr m n sp s _ saved
  intro i hi
  apply written
  intro j hj
  have location : sp + 40#64 + BitVec.ofNat 64 i =
      (s.regs.rsp.toBitVec - 104) + BitVec.ofNat 64 (56+i) := by rw [stack]; bv_omega
  rw [location]
  exact separated (56+i) (by omega) j hj

theorem output_observe (m n : DataMem) (out : BitVec 64)
    (output : out.toNat + 76 ≤ 2^64)
    (written : ∀ a : BitVec 64, (∀ i < 76, a ≠ out + BitVec.ofNat 64 i) → n.get? a = m.get? a)
    (pointer count : Nat) (bound : pointer + count ≤ 2^64)
    (apart : Body.Apart pointer count out.toNat 76) :
    widthLoad n pointer count = widthLoad m pointer count := by
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  apply written
  intro j hj
  unfold Body.Apart at apart
  bv_omega

theorem Ready.stored_output {s t : MachineData} {limit : Option Nat} {data : Ssz.Bytes}
    {address capacity used ra : BitVec 64} {ready : SszNative.Delimited.Prepared}
    (h : Owned s limit data address capacity used ra)
    (state : Ready s t limit data address capacity used ready) (m : DataMem)
    (written : ∀ a : BitVec 64, (∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) →
      m.get? a = t.dmem.get? a) : SszNative.Delimited.PreparedAt (widthLoad m) ready := by
  have stored := state.stored
  cases allocated : ready.allocation with
  | none => simpa only [SszNative.Delimited.PreparedAt, allocated] using stored
  | some reservation =>
    have bounds := allocation_bounds s limit data address capacity used ra h reservation
      (state.allocation.trans allocated)
    have separated := h.arena_output
    have usedBound := h.used_bound
    simp only [SszNative.Delimited.PreparedAt, allocated] at stored ⊢
    constructor
    · rw [output_observe t.dmem m s.regs.rdi.toBitVec h.output_bound written
        reservation.pointer 8 (by omega)
        (by unfold Body.Apart at *; simp only [UInt64.toNat_toBitVec] at *; omega)]
      exact stored.1
    · rw [output_observe t.dmem m s.regs.rdi.toBitVec h.output_bound written
        (reservation.pointer+8) 8 (by omega)
        (by unfold Body.Apart at *; simp only [UInt64.toNat_toBitVec] at *; omega)]
      exact stored.2

theorem Ready.cursor_output {s t : MachineData} {limit : Option Nat} {data : Ssz.Bytes}
    {address capacity used ra : BitVec 64} {ready : SszNative.Delimited.Prepared}
    (h : Owned s limit data address capacity used ra)
    (state : Ready s t limit data address capacity used ready) (m : DataMem)
    (written : ∀ a : BitVec 64, (∀ i < 76, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) →
      m.get? a = t.dmem.get? a) :
    widthLoad m (s.regs.r8.toNat + 16) 8 = some ready.used := by
  have bound := h.header_bound
  have separated := h.header_output
  rw [output_observe t.dmem m s.regs.rdi.toBitVec h.output_bound written
    (s.regs.r8.toNat+16) 8 (by omega)
    (by unfold Body.Apart at *; simp only [UInt64.toNat_toBitVec] at *; omega)]
  exact state.cursor

end SszX86.Delimited
