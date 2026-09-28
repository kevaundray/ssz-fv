import SszArm.NatAddLargeCorrectAllocation

namespace SszArm.NatAdd.LargeCorrect

open SszNative
open UintCodec (widthLoad)
open Delimited (Protected MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- All words are already present at PC2044. Execute the real normalization
scan, descriptor/status stores, and RET, preserving every allocated word. -/
theorem finish_run (s u : ArmState) (base : BitVec 64) (left right : NatOperand)
    (reservation : Arena.Reservation) (owned : Owned s left right)
    (allocated : Allocation s left right reservation) (leftNonzero : left.wordCount ≠ 0)
    (hc : CodeAt u base) (he : read_err u = .None) (ha : CheckSPAlignment u)
    (hp : read_pc u = base + 2044#64)
    (frame : Frame s u)
    (memory : MemoryFrame (writesFor s (outcome s left right)) s u)
    (cursor : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) u = BitVec.ofNat 64 reservation.used)
    (h8 : r (.GPR 8#5) u = BitVec.ofNat 64 (SszNative.NatAdd.count left right))
    (h9 : r (.GPR 9#5) u = BitVec.ofNat 64 reservation.pointer)
    (h10 : r (.GPR 10#5) u = BitVec.ofNat 64 reservation.pointer)
    (h11 : r (.GPR 11#5) u = (SszNative.NatAdd.writtenWords left right)[0]?.getD 0#64)
    (words : NatCompare.Words u (BitVec.ofNat 64 reservation.pointer)
      (SszNative.NatAdd.writtenWords left right)) :
    ∃ fuel t, run fuel u = t ∧ Post s t left right := by
  let written := SszNative.NatAdd.writtenWords left right
  let pointer := BitVec.ofNat 64 reservation.pointer
  have pointerNat : pointer.toNat = reservation.pointer := by
    simp only [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt allocated.pointer_bound]
  have len : written.length = SszNative.NatAdd.count left right + 1 :=
    SszNative.NatAdd.writtenWords_length left right
  have bound : written.length + 1 < 2^64 := by
    rw [len]
    have hl := count_bound s left owned.leftAt
    have hr := count_bound s right owned.rightAt
    simp only [SszNative.NatAdd.count]
    omega
  have nonzero : Limbs.sigWords written ≠ 0 := written_nonzero left right leftNonzero
  obtain ⟨normFuel, v, vrun, vf, vm, v0, vp, pair, vwords⟩ :=
    Normalize.normalize_run u base pointer written (SszNative.NatAdd.count left right)
      hc he ha hp h8 h9 h10 h11 len bound words
  have vp' : read_pc v = base + 2080#64 := by simpa only [nonzero, ↓reduceIte] using vp
  have pair' := pair nonzero
  have rootFrame : Frame s v := frame.trans (compare_frame vf v0)
  have returnOwned := rootFrame.return_owned owned.return_owned
  have vlocal : localWrites v = localWrites s := by
    simp only [localWrites, rootFrame.out, rootFrame.sp]
  have inputAt : (NatOperand.fromWords pointer written).At (widthLoad v) := by
    apply NatOperand.fromWords_at
    refine ⟨?_, ?_, ?_, words_at v pointer written vwords⟩
    · simpa only [pointerNat] using allocated.positive
    · simpa only [pointerNat] using allocated.aligned
    · simpa only [pointerNat, len] using allocated.physical
  have outputLocal : Protected (localWrites v) pointer.toNat (8 * written.length) := by
    simpa only [vlocal, pointerNat, len] using allocated.output_local
  have outputValue : Protected (valueWrites v) pointer.toNat (8 * written.length) := by
    apply protected_of_contained outputLocal
    intro inner member
    simp only [valueWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨((r (.GPR 0#5) v).toNat, 68), by simp [localWrites], by omega, by omega⟩
    · exact ⟨((r (.GPR 0#5) v).toNat, 68), by simp [localWrites], by omega, by omega⟩
    · exact ⟨((r (.GPR 31#5) v).toNat - 16, 16), by simp [localWrites], by omega, by omega⟩
  let t := valueResult .large base v
  have trun : run 12 v = t := value_run .large v base ((compare_frame vf v0).code hc)
    (vf.error.trans he) (vf.aligned ha) vp'
  have image := value_success_image .large v base returnOwned (NatOperand.fromWords pointer written)
    (by simpa only [valuePointer] using pair'.1)
    (by simpa only [valuePayload] using pair'.2)
    inputAt (fromWords_owned (valueWrites v) pointer written outputValue)
  have localMemory : MemoryFrame (localWrites s) v t := by
    simpa only [vlocal] using value_local_frame .large v base returnOwned
  have finalMemory : MemoryFrame (writesFor s (outcome s left right)) s t := by
    apply memory.trans
    have tail : MemoryFrame (writesFor s (outcome s left right)) v t :=
      localMemory.weaken (by
        intro span member
        rw [allocated.writes]
        exact List.mem_append_left _ member)
    intro a outside
    exact (tail a outside).trans (congrFun vm a)
  have finalWords : NatCompare.Words t pointer written := by
    intro i
    have hi := i.isLt
    have hiCount : i.val < SszNative.NatAdd.count left right + 1 := by omega
    have physical := allocated.physical
    have address : (pointer + BitVec.ofNat 64 (8 * i.val)).toNat =
        pointer.toNat + 8 * i.val := by rw [pointerNat]; bv_omega
    rw [(value_local_frame .large v base returnOwned).read _ 8
      (by rw [address, pointerNat]; omega)
      (by rw [address]; exact outputLocal.subspan (8 * i.val) 8 (by omega))]
    exact vwords i
  have finalWritten : WrittenAt (widthLoad t) (outcome s left right) := by
    intro actual same
    have eq : reservation = actual := by
      simpa only [allocated.outcomeEq, NatArithmetic.committed, Option.some.injEq] using same
    subst actual
    simpa only [allocated.outcomeEq, NatArithmetic.committed, ← pointerNat] using
      words_at t pointer written finalWords
  have cursorAddress : (r (.GPR 5#5) s + 16#64).toNat =
      (r (.GPR 5#5) s).toNat + 16 := by have := owned.arenaBound; bv_omega
  have finalCursor : (read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t).toNat =
      (outcome s left right).used := by
    rw [localMemory.read _ 8 (by rw [cursorAddress]; have := owned.arenaBound; omega)
      (by rw [cursorAddress]; exact owned.arenaLocal.subspan 16 8 (by decide))]
    rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp vm, cursor]
    simp only [allocated.outcomeEq, NatArithmetic.committed, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt allocated.usedBound]
  refine ⟨normFuel + 12, t, ?_, post_of_frame s t left right owned
    (rootFrame.returned (value_returned .large v base (vf.error.trans he)))
    ?_ finalWritten finalCursor finalMemory⟩
  · rw [run_plus, vrun, trun]
  · simpa only [allocated.outcomeEq, NatArithmetic.committed, rootFrame.out] using image

end SszArm.NatAdd.LargeCorrect
