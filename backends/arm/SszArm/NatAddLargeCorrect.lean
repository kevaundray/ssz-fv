import SszArm.NatAddLargeCorrectWords
import SszArm.NatAddLargeCorrectFinish
import SszArm.NatAddLargeCorrectError

namespace SszArm.NatAdd

open SszNative
open Delimited (Protected MemoryFrame)
open LargeCorrect

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Complete multiword Nat.add from the actual maximum-selection entry through
RET. It includes checked layout and allocation failure, both physical operand
tags, arbitrary-length carry loops, all scratch writes, and normalization. -/
theorem large_correct (s : ArmState) (base : BitVec 64) (left right : NatOperand)
    (owned : Owned s left right) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 128#64)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (large : ¬ (left.wordCount ≤ 1 ∧ right.wordCount ≤ 1))
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 left.wordCount)
    (h10 : r (.GPR 10#5) s = BitVec.ofNat 64 right.wordCount) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  have leftBound := count_bound s left owned.leftAt
  have rightBound := count_bound s right owned.rightAt
  have countBound : SszNative.NatAdd.count left right + 1 < 2^64 := by
    simp only [SszNative.NatAdd.count]
    omega
  obtain ⟨runMax, maxFrame, maxOut, max8, _, _, maxPC⟩ :=
    maximum_select s base left.wordCount right.wordCount hc he ha hp
      (by omega) (by omega) countBound h8 h10
  let u := block base [.p128, .p132, .p136, .p140] s
  have uf : LargeCorrect.Frame s u := compare_frame maxFrame maxOut
  have um : MemoryFrame (localWrites s) s u := scan_memory maxFrame owned.stackBound
  have ownedU : Owned u left right := owned.transport maxFrame maxOut
  have arenaEq : arenaOf u = arenaOf s := arena_eq_of_scan owned maxFrame
  have u8 : (r (.GPR 8#5) u).toNat = SszNative.NatAdd.count left right := by
    rw [max8]
    exact BitVec.toNat_ofNat_of_lt (by omega)
  have u5 := uf.registers 5#5 (by decide)
  have headerSeparate : (r (.GPR 5#5) u).toNat + 24 ≤ (r (.GPR 31#5) u).toNat - 16 ∨
      (r (.GPR 31#5) u).toNat ≤ (r (.GPR 5#5) u).toNat := by
    rcases ownedU.arenaLocal with empty | separate
    · omega
    · have apart := separate ((r (.GPR 31#5) u).toNat - 16, 16) (by simp [localWrites])
      have stack := ownedU.stackBound
      simp only [Prod.fst, Prod.snd] at apart
      omega
  obtain ⟨arenaFuel, v, runArena, arenaFrame, failed | committed⟩ :=
    arena_big_layout_reservation_runs u base
      (read_mem_bytes 8 (r (.GPR 5#5) u) u)
      (read_mem_bytes 8 (r (.GPR 5#5) u + 8#64) u)
      (read_mem_bytes 8 (r (.GPR 5#5) u + 16#64) u)
      (uf.code hc) (uf.error.trans he) (uf.aligned ha) maxPC ownedU.stackBound
      rfl rfl rfl ownedU.arenaBound headerSeparate
  · obtain ⟨notReserved, vp, arenaMemory⟩ := failed
    have reserveNone : Arena.reserve (arenaOf s).base (arenaOf s).capacity (arenaOf s).used
        (SszNative.NatAdd.count left right + 1) = none := by
      change Arena.reserve (arenaOf u).base (arenaOf u).capacity (arenaOf u).used
        ((r (.GPR 8#5) u).toNat + 1) = none at notReserved
      simpa only [arenaEq, u8] using notReserved
    have result : outcome s left right =
        NatArithmetic.unchanged (arenaOf s).used (.error .scratchExhausted) := by
      rw [large_outcome s left right owned leftNonzero rightNonzero large, reserveNone]
    have vf := uf.trans (arena_frame arenaFrame)
    have vm : MemoryFrame (localWrites s) s v := um.trans (arenaMemory.weaken (by
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      simp only [uf.sp]
      simp [localWrites]))
    obtain ⟨tailFuel, t, runTail, post⟩ := error_finish s v base left right owned result
      (vf.code hc) (vf.error.trans he) (vf.aligned ha) vp vf vm
    refine ⟨4 + arenaFuel + tailFuel, t, ?_, post⟩
    rw [run_plus, run_plus, runMax, runArena, runTail]
  · obtain ⟨reservation, reserved, vp, pointer, _, cursor, arenaMemory, width, allocationPointer⟩ := committed
    have reservedRoot : Arena.reserve (arenaOf s).base (arenaOf s).capacity (arenaOf s).used
        (SszNative.NatAdd.count left right + 1) = some reservation := by
      change Arena.reserve (arenaOf u).base (arenaOf u).capacity (arenaOf u).used
        ((r (.GPR 8#5) u).toNat + 1) = some reservation at reserved
      simpa only [arenaEq, u8] using reserved
    have allocated := allocation s left right owned leftNonzero rightNonzero large reservation reservedRoot
    have vf := uf.trans (arena_frame arenaFrame)
    have cursorAddress : (r (.GPR 5#5) s + 16#64).toNat =
        (r (.GPR 5#5) s).toNat + 16 := by have := owned.arenaBound; bv_omega
    have vm : MemoryFrame (writesFor s (outcome s left right)) s v := by
      apply (local_frame (outcome s left right) um).trans
      apply memory_of_contained arenaMemory
      intro inner member
      simp only [List.mem_cons, List.mem_singleton] at member
      rcases member with rfl | rfl
      · refine ⟨((r (.GPR 31#5) s).toNat - 16, 16), ?_, ?_, ?_⟩
        · rw [allocated.writes]; simp [localWrites]
        · simp only [uf.sp]; omega
        · simp only [uf.sp]; omega
      · refine ⟨((r (.GPR 5#5) s).toNat + 16, 8), ?_, ?_, ?_⟩
        · rw [allocated.writes]; simp
        · simp only [u5, cursorAddress]; omega
        · simp only [u5, cursorAddress]; omega
    have v8 : r (.GPR 8#5) v = BitVec.ofNat 64 (SszNative.NatAdd.count left right) :=
      width.trans max8
    have v9 : r (.GPR 9#5) v = BitVec.ofNat 64 reservation.pointer := by
      apply BitVec.eq_of_toNat_eq
      rw [pointer, BitVec.toNat_ofNat_of_lt allocated.pointer_bound]
    have v10 : r (.GPR 10#5) v = BitVec.ofNat 64 reservation.pointer :=
      allocationPointer.trans v9
    have vcursor : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) v =
        BitVec.ofNat 64 reservation.used := by simpa only [u5] using cursor
    obtain ⟨wordsFuel, w, runWords, wf, wm, scratchMemory, wp, w8, w9, w10, w11, words⟩ :=
      words_run s v base left right reservation owned allocated leftNonzero rightNonzero large
        (vf.code hc) (vf.error.trans he) (vf.aligned ha) vp vf vm v8 v9 v10
    have cursorProtected : Protected
        (LargeLoop.suffixWrites (r (.GPR 31#5) s) (BitVec.ofNat 64 reservation.pointer)
          0 (SszNative.NatAdd.count left right + 1))
        (r (.GPR 5#5) s + 16#64).toNat 8 := by
      have localCursor := owned.arenaLocal.subspan 16 8 (by decide)
      have pointerNat : (BitVec.ofNat 64 reservation.pointer).toNat = reservation.pointer :=
        BitVec.toNat_ofNat_of_lt allocated.pointer_bound
      right
      intro span member
      simp only [LargeLoop.suffixWrites, List.mem_cons, List.mem_singleton,
        pointerNat, Nat.mul_zero, Nat.add_zero] at member
      rcases member with rfl | rfl
      · rcases localCursor with empty | apart
        · omega
        · rw [cursorAddress]
          exact apart _ (by simp [localWrites])
      · have fresh := allocated.fresh
        rcases fresh with empty | apart
        · omega
        · have separate := apart ((r (.GPR 5#5) s).toNat, 24) (by simp)
          rw [cursorAddress]
          simp only [Prod.fst, Prod.snd] at *
          omega
    have wcursor : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) w =
        BitVec.ofNat 64 reservation.used := by
      rw [scratchMemory.read _ 8 (by rw [cursorAddress]; have := owned.arenaBound; omega) cursorProtected]
      exact vcursor
    obtain ⟨finishFuel, t, runFinish, post⟩ := finish_run s w base left right reservation owned
      allocated leftNonzero (wf.code hc) (wf.error.trans he) (wf.aligned ha) wp wf wm
      wcursor w8 w9 w10 w11 words
    refine ⟨4 + arenaFuel + wordsFuel + finishFuel, t, ?_, post⟩
    rw [run_plus, run_plus, run_plus, runMax, runArena, runWords, runFinish]

end SszArm.NatAdd
