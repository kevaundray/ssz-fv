import SszX86.NatAddReserveMemory
import SszX86.NatAddSmallPhase

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The native cursor/low/carry store sequence is precisely the shared complete
written list, not merely the normalized result's retained prefix. -/
theorem small_commit_memory (s t : MachineData) (left right : NatOperand)
    (address capacity used : BitVec 64)
    (ready : SumReady (pushedState s) t left right) (r : Arena.Reservation) (flags : StatusFlags)
    (model : SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r [(SszNative.NatAdd.sumWide left right).setWidth 64, 1#64]) :
    (Reservation.Small.reservedState t address used flags).dmem =
      Large.fillMem (cursorMem s t.dmem (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used)
        (BitVec.ofNat 64 r.pointer) 0
        (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written := by
  have allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have geometry := SszNative.NatAdd.allocation_geometry left right address.toNat capacity.toNat used.toNat r allocated
  have written : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written =
      [(SszNative.NatAdd.sumWide left right).setWidth 64, 1#64] := by rw [model]; rfl
  have finish : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used =
      Arena.start address.toNat used.toNat + 16 := by
    simpa only [Arena.finish, written, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceMul] using geometry.2.2.1
  have arena : t.regs.r9.toBitVec = s.regs.r9.toBitVec := by rw [ready.frame.arena]; rfl
  have one : (1#64).toInt = 1 := by decide
  simp only [Reservation.Small.reservedState, written, finish, geometry.2.1,
    Large.fillMem, cursorMem, ready.low, arena, Nat.mul_zero, Nat.zero_add,
    Nat.reduceMul, BitVec.add_zero, one]

/-- Complete post-reservation ownership facts, before its real750 publication. -/
theorem small_commit_resources (s t : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (ready : SumReady (pushedState s) t left right) (r : Arena.Reservation) (flags : StatusFlags)
    (model : SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r [(SszNative.NatAdd.sumWide left right).setWidth 64, 1#64]) :
    WorkFrame s (Reservation.Small.reservedState t address used flags).dmem
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat) ∧
    NatMemory.wordsAt (widthLoad (Reservation.Small.reservedState t address used flags).dmem) r.pointer
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written ∧
    widthLoad (Reservation.Small.reservedState t address used flags).dmem (s.regs.r9.toNat+16) 8 =
      some (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used := by
  have allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have geometry := SszNative.NatAdd.allocation_geometry left right address.toNat capacity.toNat used.toNat r allocated
  have pointerNat := allocated_pointer_nat s left right address capacity used ra owned r allocated
  have bounds := allocation_bounds s left right address capacity used ra owned r allocated
  have extent : (BitVec.ofNat 64 r.pointer).toNat +
      8*(SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length ≤ 2^64 := by
    rw [pointerNat]
    exact bounds.2.2.2.2.2
  rw [small_commit_memory s t left right address capacity used ready r flags model]
  refine ⟨?_, ?_, ?_⟩
  · exact ((ready.frame.work _).cursor_store owned r allocated).fill owned r allocated
  · simpa only [pointerNat] using Large.fill_wordsAt
      (cursorMem s t.dmem (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used)
      (BitVec.ofNat 64 r.pointer)
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written extent
  · have buffer : ∀ a : BitVec 64,
        Body.Outside a.toNat r.pointer
          (8*(SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length) →
        (Large.fillMem (cursorMem s t.dmem (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used)
          (BitVec.ofNat 64 r.pointer) 0
          (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written).get? a =
        (cursorMem s t.dmem (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used).get? a := by
      intro a outside
      apply Large.fill_frame
      intro i low high
      apply Body.outside_byte (BitVec.ofNat 64 r.pointer) a _ i extent
      · simpa only [pointerNat] using outside
      · simpa only [Nat.zero_add] using high
    rw [cursor_after_buffer s left right address capacity used ra owned _ _ r allocated buffer]
    apply cursor_store_value
    rw [geometry.2.2.1]
    exact geometry.1.2.2.2.2.1

end SszX86.NatAdd
