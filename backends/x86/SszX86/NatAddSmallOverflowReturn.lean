import SszX86.NatAddSmallCommitMemory
import SszX86.NatAddSmallOutcome
import SszX86.NatAddFailureReturn
import SszX86.NatAddOverflowOutput

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Execute every reserve2 guard, both committed limb stores, exact success or
error publication, ABI restores and RET. No reservation-success assumption. -/
theorem small_overflow_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (ready : SumReady (pushedState s) t left right)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (small : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1)
    (overflow : ¬ (SszNative.NatAdd.sumWide left right).toNat < 2^64) :
    Eventually (step e) (Post s left right address capacity used ra) (t,base+676) := by
  have model := one_word_overflow left right address.toNat capacity.toNat used.toNat
    leftNonzero rightNonzero small overflow
  apply Reservation.small_cps e base hc t address capacity used
    (ready.frame.small_header owned) (ready.frame.arena_mapped owned)
  intro final post
  rcases final with ⟨u, pc⟩
  rcases post with ⟨frame, failed | success⟩
  · rcases failed with ⟨unreserved, rfl, memory⟩
    apply reserve_failure_finish_cps e base hc s u left right address capacity used ra owned
      (ready.frame.trans (frame.control memory))
    · rw [model, unreserved]
      rfl
    · rw [model, unreserved]
      rfl
  · rcases success with ⟨r, reserved, rfl, flags, rfl⟩
    rw [reserved] at model
    let u := Reservation.Small.reservedState t address used flags
    change Eventually (step e) (Post s left right address capacity used ra) (u,base+750)
    have allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r := by
      rw [model]
      rfl
    have geometry := SszNative.NatAdd.allocation_geometry left right address.toNat capacity.toNat used.toNat r allocated
    have resources := small_commit_resources s t left right address capacity used ra owned ready r flags model
    have outputMapped : OutputMapped u := by
      change Large.Mapped u.dmem u.regs.rdi.toBitVec 68
      dsimp only [u, Reservation.Small.reservedState]
      repeat' first | exact ready.frame.output_mapped owned | apply Large.mapped_store
    apply overflow_publish_cps e base hc u outputMapped
    have out : u.regs.rdi.toBitVec = s.regs.rdi.toBitVec := by
      change t.regs.rdi.toBitVec = s.regs.rdi.toBitVec
      rw [ready.frame.output]
      rfl
    have pointer : u.regs.rsi.toBitVec = BitVec.ofNat 64 r.pointer := by
      simp only [u, Reservation.Small.reservedState, UInt64.toBitVec_ofBitVec, geometry.2.1]
    have two : (2 : BitVec 64) = 2#64 := by decide
    rw [out, pointer, two]
    have result : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).result =
        .ok (.large (BitVec.ofNat 64 r.pointer) [(SszNative.NatAdd.sumWide left right).setWidth 64, 1#64]) := by
      rw [model]
      simp only [NatArithmetic.committed, fromWords_carry]
    have returned := success_memory_finish_cps e base hc s u left right address capacity used ra owned
      resources.1 (fun r' allocated' => by
        rw [model] at allocated'
        have same : r = r' := Option.some.inj allocated'
        cases same
        exact resources.2.1)
      resources.2.2 ready.frame.sp ready.frame.original_simd _ result
    simpa only [NatOperand.pointer, NatOperand.payload, List.length_cons,
      List.length_nil, Nat.reduceAdd] using returned

end SszX86.NatAdd
