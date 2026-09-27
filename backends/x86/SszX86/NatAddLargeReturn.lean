import SszX86.NatAddLargeCarryReturn
import SszX86.NatAddFailureReturn
import SszX86.NatAddSelectPhase

namespace SszX86.NatAdd
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Every reachable large arithmetic branch from the actual maximum/count guard
executes through RET. Physical operand extents discharge count-overflow; arena
failure remains an explicit branch, without a signed capacity restriction. -/
theorem large_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (ready : CountReady (pushedState s) t left right)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (large : ¬ (left.wordCount ≤ 1 ∧ right.wordCount ≤ 1)) :
    Eventually (step e) (Post s left right address capacity used ra) (t,base+397) := by
  have leftBound := operand_count_bound s.dmem left owned.left_at
  have rightBound := operand_count_bound s.dmem right owned.right_at
  have leftNat : t.regs.rax.toNat = left.wordCount := by
    change t.regs.rax.toBitVec.toNat = left.wordCount
    have eq := congrArg BitVec.toNat ready.left_count
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : left.wordCount < 2^64)] using eq
  have rightNat : t.regs.r11.toNat = right.wordCount := by
    change t.regs.r11.toBitVec.toNat = right.wordCount
    have eq := congrArg BitVec.toNat ready.right_count
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : right.wordCount < 2^64)] using eq
  have countBound : SszNative.NatAdd.count left right+2 < 2^64 := by
    unfold SszNative.NatAdd.count
    omega
  have wide : 2 ≤ SszNative.NatAdd.count left right := by
    unfold SszNative.NatAdd.count
    omega
  have fits : SszNative.NatAdd.count left right+1 < 2^64 := by omega
  have model := SszNative.NatAdd.run_large left right address.toNat capacity.toNat used.toNat
    leftNonzero rightNonzero large
  simp only [fits, ↓reduceIte] at model
  have count (flags : StatusFlags) :
      (Reservation.Large.maxState t flags).regs.rax.toNat = SszNative.NatAdd.count left right := by
    unfold SszNative.NatAdd.count
    by_cases lt : t.regs.rax.toNat < t.regs.r11.toNat
    · simp only [Reservation.Large.maxState, lt, ↓reduceIte]
      rw [rightNat]
      exact (Nat.max_eq_right (by omega)).symm
    · simp only [Reservation.Large.maxState, lt, ↓reduceIte]
      rw [leftNat]
      exact (Nat.max_eq_left (by omega)).symm
  apply Reservation.large_cps e base hc t address capacity used (ready.frame.large_header owned)
  · intro overflow flags
    rw [leftNat, rightNat] at overflow
    unfold SszNative.NatAdd.count at countBound
    exact False.elim (by omega)
  · intro notOverflow flags final post
    have initialFrame : ControlFrame (pushedState s) (Reservation.Large.maxState t flags) :=
      ready.frame.trans ⟨rfl, rfl, rfl, rfl, rfl⟩
    rcases final with ⟨u, pc⟩
    rcases post with ⟨frame, failed | success⟩
    · rcases failed with ⟨unreserved, rfl, memory⟩
      rw [count flags] at unreserved
      have failureModel := model
      rw [unreserved] at failureModel
      apply reserve_failure_finish_cps e base hc s u left right address capacity used ra owned
        (initialFrame.trans (frame.control memory))
      · rw [failureModel]
        rfl
      · rw [failureModel]
        rfl
    · rcases success with ⟨r, reserved, rfl, resultFlags, rfl⟩
      rw [count flags] at reserved
      have successModel := model
      rw [reserved] at successModel
      exact large_carry_finish_cps e base hc s (Reservation.Large.maxState t flags)
        left right address capacity used ra owned initialFrame
        ready.left_pointer ready.left_payload ready.right_pointer ready.right_payload
        leftNonzero rightNonzero wide (count flags) r resultFlags successModel

end SszX86.NatAdd
