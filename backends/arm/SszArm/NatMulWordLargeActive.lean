import SszArm.NatMulWordLargeFinish

namespace SszArm.NatMulWord.Large

open Delimited (MemoryFrame)
open SszNative.NatArithmetic

theorem setup_frame_full (s u : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) (factor : BitVec 64) (owned : Owned s operand factor)
    (reservation : SszNative.Arena.Reservation)
    (model : outcome s operand factor = committed reservation (SszNative.NatMul.wordWritten operand factor))
    (abi : SmallABI s u) (pc : read_pc u = base + 452#64) :
    MemoryFrame (writesFor s (outcome s operand factor)) u (block base Reserve.firstOps u) := by
  have header := owned.arenaBound
  have address : (r (.GPR 4#5) u + 16#64).toNat = (r (.GPR 4#5) s).toNat + 16 := by
    rw [abi.arena]
    bv_omega
  apply (Reserve.first_memory u base pc (by rw [address]; omega)).1.weaken
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  simp [writesFor, model, committed, address]

theorem first_frame_active {s u t : ArmState} {base : BitVec 64}
    (reservation : SszNative.Arena.Reservation) (words : List (BitVec 64))
    (positive : 0 < words.length) (bound : reservation.pointer < 2^64)
    (abi : SmallABI s u) (output : r (.GPR 10#5) u = BitVec.ofNat 64 reservation.pointer)
    (post : FirstPost u t base) : MemoryFrame (activeWrites s reservation words) u t := by
  intro a outside
  apply post.frame a
  have stack := outside ((r (.GPR 31#5) s).toNat - 48, 48)
    (by simp [activeWrites, localWrites, committed])
  have destination := outside (reservation.pointer, 8 * words.length) (by simp [activeWrites])
  intro span member
  simp only [abi.sp, output, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp only [Prod.fst, Prod.snd] at * <;> omega

theorem finish_frame_active {s u t : ArmState} (reservation : SszNative.Arena.Reservation)
    (words : List (BitVec 64)) (bound : reservation.pointer < 2^64)
    (stackBound : 48 ≤ (r (.GPR 31#5) s).toNat) (abi : SmallABI s u)
    (frame : MemoryFrame (finishWrites u (BitVec.ofNat 64 reservation.pointer) words.length) u t) :
    MemoryFrame (activeWrites s reservation words) u t := by
  intro a outside
  apply frame a
  have stack := outside ((r (.GPR 31#5) s).toNat - 48, 48)
    (by simp [activeWrites, localWrites, committed])
  have destination := outside (reservation.pointer, 8 * words.length) (by simp [activeWrites])
  have output := outside ((r (.GPR 0#5) s).toNat, 16) (by simp [activeWrites, localWrites, committed])
  have status := outside ((r (.GPR 0#5) s).toNat + 64, 4)
    (by simp [activeWrites, localWrites, committed])
  intro span member
  simp only [finishWrites, NatMul.loopWrites, valueWrites, NatAdd.valueWrites,
    abi.sp, abi.out, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | (rfl | rfl | rfl) <;>
    simp only [Prod.fst, Prod.snd] at * <;> omega

end SszArm.NatMulWord.Large
