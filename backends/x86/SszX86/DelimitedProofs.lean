import SszX86.DelimitedEarlyProofs
import SszX86.DelimitedComparePhase
import SszX86.DelimitedReservePhase

namespace SszX86.Delimited
open UintCodec

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

private theorem ready_finish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hcompare : NatCompare.CodeAt e (base + Int64.ofInt compareOffset))
    (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! ≠ 0)
    (ready : SszNative.Delimited.Prepared) (state : Ready s t limit data address capacity used ready)
    (optionAddress : t.regs.rsi = s.regs.rsi)
    (pointer : t.regs.r8.toBitVec = BitVec.ofNat 64 ready.pointer) :
    Eventually (step e) (Post s limit data address capacity used ra)
      (t, if limit.isSome then base + 374 else base + 523) := by
  cases limit with
  | none =>
    change Eventually (step e) (Post s none data address capacity used ra) (t, base + 523)
    exact success_phase_cps e base hc s t none data address capacity used ra h nonempty delimiter
      ready state (by intro cap impossible; cases impossible) _ (fun _ post => post)
  | some cap =>
    change Eventually (step e) (Post s (some cap) data address capacity used ra) (t, base + 374)
    apply compare_phase_cps e base hc hcompare s t cap data address capacity used ra h
      nonempty delimiter ready state optionAddress pointer
    intro u capPointer capPayload compared actualPointer spillPointer spillPayload originalPointer originalPayload
    by_cases greater : compare ready.count.value cap = .gt
    · rw [ite_eq_left greater]
      have rejected : ¬ ready.count.value ≤ cap := by
        have above := Nat.compare_eq_gt.mp greater
        omega
      exact over_limit_phase_cps e base hc s u cap data address capacity used ra h nonempty delimiter
        ready compared rejected capPointer capPayload actualPointer spillPointer spillPayload
        originalPointer originalPayload _ (fun _ post => post)
    · rw [ite_eq_right greater]
      have bounded : ∀ other, some cap = some other → ready.count.value ≤ other := by
        intro other equal
        cases equal
        apply Nat.le_of_not_gt
        intro above
        exact greater (Nat.compare_eq_gt.mpr above)
      exact success_phase_cps e base hc s u (some cap) data address capacity used ra h nonempty delimiter
        ready compared bounded _ (fun _ post => post)

/-- Complete execution of the actual linked decode_delimited entry through its
actual RET, including the sole linked Nat.compare callee. Only code images and
caller-owned physical memory are premises. No codec, comparison, allocation,
relocation, signed-length, or canonical-capacity hypothesis is assumed.

The postcondition retains exact shared-model results/resources, borrowed input,
original capacity representation, saved registers/SP/return slot, and the
76-byte output,104-byte activation, cursor, and exact new two-word scratch frame.
This is the callee theorem, not an outer-dispatch-wrapper theorem. -/
theorem decode_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hcompare : NatCompare.CodeAt e (base + Int64.ofInt compareOffset))
    (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (owned : Owned s limit data address capacity used ra) :
    Eventually (step e) (Post s limit data address capacity used ra) (s, base + Int64.ofNat entry) := by
  rw [show Int64.ofNat entry = 0 by decide, Int64.add_zero]
  apply validation_cps e base hc s limit data address capacity used ra owned
  intro flags nonempty delimiter
  apply count_phase_cps e base hc s limit data address capacity used ra owned nonempty delimiter flags
  intro t counted
  by_cases small : (SszNative.Delimited.countWords data.size
      (Ssz.highestBit data[data.size - 1]!)).high = 0#64
  · rw [ite_eq_left small]
    apply small_prepare_cps e base hc s t limit data address capacity used ra owned counted
      nonempty delimiter small
    intro u ready prepared optionAddress pointer
    exact ready_finish e base hc hcompare s u limit data address capacity used ra owned
      nonempty delimiter ready prepared optionAddress pointer
  · rw [ite_eq_right small]
    apply reserve_return_cps e base hc s t limit data address capacity used ra owned nonempty delimiter
      counted small _ _ (fun _ post => post)
    intro u ready prepared optionAddress pointer
    apply (ready_option_cps e base hc s u limit data address capacity used ra owned ready
      prepared optionAddress pointer _ _).2
    intro v state optionAt countPointer
    exact ready_finish e base hc hcompare s v limit data address capacity used ra owned
      nonempty delimiter ready state optionAt countPointer

/-- Shared native-model refinement, preserving the resource failure separately
from semantic SSZ errors rather than assuming scratch availability. -/
theorem Post.outcome {s : MachineData} {limit : Option Nat} {data : Ssz.Bytes}
    {address capacity used ra : BitVec 64} {t : MachineState}
    (owned : Owned s limit data address capacity used ra)
    (post : Post s limit data address capacity used ra t) :
    if SszNative.Delimited.Exhausted data ⟨address.toNat, capacity.toNat, used.toNat⟩ then
      SszNative.UintCodec.errorAt (widthLoad t.1.dmem) s.regs.rdi.toNat 32768 0 0
    else SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
      (SszNative.BitView.delimitedOutcome limit data) := by
  have physical : data.size < 2^64 := by rw [owned.length]; exact s.regs.rcx.toBitVec.isLt
  by_cases exhausted : SszNative.Delimited.Exhausted data ⟨address.toNat, capacity.toNat, used.toNat⟩
  · rw [ite_eq_left exhausted]
    have result := (SszNative.Delimited.run_scratch_iff limit data
      ⟨address.toNat, capacity.toNat, used.toNat⟩ physical).mpr exhausted
    simpa only [SszNative.Delimited.ResultAt, result] using post.observed
  · rw [ite_eq_right exhausted]
    exact SszNative.Delimited.result_refines _ _ _ _ limit data
      ⟨address.toNat, capacity.toNat, used.toNat⟩ physical exhausted post.observed

theorem Post.refines {s : MachineData} {limit : Option Nat} {data : Ssz.Bytes}
    {address capacity used ra : BitVec 64} {t : MachineState}
    (owned : Owned s limit data address capacity used ra)
    (post : Post s limit data address capacity used ra t) :
    if SszNative.Delimited.Exhausted data ⟨address.toNat, capacity.toNat, used.toNat⟩ then
      SszNative.UintCodec.errorAt (widthLoad t.1.dmem) s.regs.rdi.toNat 32768 0 0
    else SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
      (Ssz.deserialize (.progressiveBitList limit) data) := by
  simpa only [SszNative.BitView.progressive_outcome_eq_deserialize] using post.outcome owned

theorem Post.bitList {s : MachineData} {capacityNat : Nat} {data : Ssz.Bytes}
    {address capacity used ra : BitVec 64} {t : MachineState}
    (owned : Owned s (some capacityNat) data address capacity used ra)
    (post : Post s (some capacityNat) data address capacity used ra t) :
    if SszNative.Delimited.Exhausted data ⟨address.toNat, capacity.toNat, used.toNat⟩ then
      SszNative.UintCodec.errorAt (widthLoad t.1.dmem) s.regs.rdi.toNat 32768 0 0
    else SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
      (Ssz.deserialize (.bitList capacityNat) data) := by
  simpa only [SszNative.BitView.list_outcome_eq_deserialize] using post.outcome owned

end SszX86.Delimited
