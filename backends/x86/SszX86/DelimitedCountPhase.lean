import SszX86.DelimitedPrepared
import SszX86.DelimitedEntry
import SszX86.DelimitedCount

namespace SszX86.Delimited
open UintCodec

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

structure Counted (s t : MachineData) (data : Ssz.Bytes) : Prop where
  active : Active s t data
  optionAddress : t.regs.rsi = s.regs.rsi
  arenaAddress : t.regs.r8 = s.regs.r8
  low : t.regs.r14.toBitVec =
    (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)).low
  high : t.regs.rbp.toBitVec =
    (SszNative.Delimited.countWords data.size (Ssz.highestBit data[data.size - 1]!)).high
  frame : Frame s t.dmem data none

theorem activation_outside (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (active : UsesActivation data) (a : BitVec 64)
    (outside : Body.Outside a.toNat (s.regs.rsp.toNat - 104) (activationBytes data)) :
    ∀ i < 104, a ≠ (s.regs.rsp.toBitVec - 104) + BitVec.ofNat 64 i := by
  have low := h.stack_low active
  simp only [activationBytes, ite_eq_left active, Body.Outside,
    ← UInt64.toNat_toBitVec] at outside low
  intro i hi
  bv_omega

theorem frame_weaken_none (s : MachineData) (m : DataMem) (data : Ssz.Bytes)
    (frame : Frame s m data none) (allocation : Option SszNative.Arena.Reservation) :
    Frame s m data allocation := by
  intro a output activation _
  exact frame a output activation (by intro reservation impossible; cases impossible)

theorem prologue_any_mapped (s : MachineData) (base : BitVec 64) (count : Nat)
    (hm : Large.Mapped s.dmem base count) : Large.Mapped (prologueMem s) base count := by
  unfold prologueMem pushedMem
  repeat' first | exact hm | apply Large.mapped_store

private def countedState (s : MachineData) (data : Ssz.Bytes)
    (byteFlags prologueFlags countFlags : StatusFlags) : MachineData :=
  countState
    (prologueState (byteState s data[data.size - 1]! byteFlags)
      (Ssz.highestBit data[data.size - 1]!) prologueFlags) countFlags

private theorem counted_state (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (active : UsesActivation data) (byteFlags prologueFlags countFlags : StatusFlags) :
    Counted s (countedState s data byteFlags prologueFlags countFlags) data := by
  have physical : data.size < 2^64 := by rw [h.length]; exact s.regs.rcx.toBitVec.isLt
  have length : s.regs.rcx = UInt64.ofNat data.size := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_ofNat', h.length, ← UInt64.toNat_toBitVec,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have preceding : s.regs.rcx.toBitVec - 1#64 = BitVec.ofNat 64 (data.size - 1) := by
    have positive := active.1
    rw [length, UInt64.toBitVec_ofNat']
    bv_omega
  have predecessor : UInt64.ofBitVec (s.regs.rcx.toBitVec - 1#64) =
      UInt64.ofNat (data.size - 1) := by
    rw [preceding, UInt64.ofBitVec_ofNat, uint64_literal]
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, length, predecessor, rfl, ?_, rfl, ?_, ?_⟩
    · exact prologue_saved s
    · exact prologue_any_mapped s s.regs.rdi.toBitVec 76 h.output_mapped
    · exact prologue_mapped s (h.stack_mapped active)
  · simp only [countedState, countState, prologueState, byteState,
      UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat', preceding,
      SszNative.Delimited.countWords, BitVec.ofNat_eq_ofNat, BitVec.add_comm]
  · simp only [countedState, countState, prologueState, byteState,
      UInt64.toBitVec_ofBitVec, preceding, SszNative.Delimited.countWords]
  · intro a _ outside _
    exact prologue_frame s a (activation_outside s limit data address capacity used ra h active a outside)

/-- The native threshold and shared two-word representation agree for every
representable byte count, including lengths whose usize sign bit is set. -/
theorem count_high_zero (length highest : Nat) (physical : length < 2^64) (bit : highest < 8) :
    (SszNative.Delimited.countWords length highest).high = 0#64 ↔ ¬ 2^61 < length := by
  rw [SszNative.Delimited.CountWords.high_zero_iff,
    SszNative.Delimited.countWords_value length highest physical bit]
  have threshold := count_large length highest bit
  omega

/-- The actual nonzero-byte entry reaches the checked count checkpoint without
assuming an initialized stack snapshot or a count computation oracle. -/
theorem count_phase_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (byteFlags : StatusFlags) (P : MachineState → Prop)
    (hp : ∀ t, Counted s t data → Eventually (step e) P
      (t, if (SszNative.Delimited.countWords data.size
        (Ssz.highestBit data[data.size - 1]!)).high = 0#64 then base + 133 else base + 269)) :
    Eventually (step e) P (byteState s data[data.size - 1]! byteFlags, base + 22) := by
  have active : UsesActivation data := ⟨nonempty, delimiter⟩
  have physical : data.size < 2^64 := by rw [h.length]; exact s.regs.rcx.toBitVec.isLt
  have threshold := count_high_zero data.size (Ssz.highestBit data[data.size - 1]!) physical
    (SszNative.BitView.highestBit_lt _)
  apply prologue_cps e base hc (byteState s data[data.size - 1]! byteFlags)
    data[data.size - 1]! delimiter
  · simp only [byteState, UInt64.toBitVec_ofBitVec]
    bv_omega
  · exact h.stack_mapped active
  intro prologueFlags
  apply count_cps e base hc
  intro countFlags
  have finished := hp (countedState s data byteFlags prologueFlags countFlags)
    (counted_state s limit data address capacity used ra h active byteFlags prologueFlags countFlags)
  by_cases large : 2^61 < data.size
  · have high : (SszNative.Delimited.countWords data.size
        (Ssz.highestBit data[data.size - 1]!)).high ≠ 0#64 := fun zero => threshold.mp zero large
    simpa only [countedState, prologueState, byteState, ← h.length, large, high, ↓reduceIte] using finished
  · have high := threshold.mpr large
    simpa only [countedState, prologueState, byteState, ← h.length, large, high, ↓reduceIte] using finished

end SszX86.Delimited
