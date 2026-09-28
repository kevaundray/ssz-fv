import SszX86.NatMulEntry
import SszX86.NatMulReserveFailureReturn
import SszX86.NatMulMemoryInitializedSetup
import SszX86.NatMulProductOperands
import SszX86.NatMulProductReturn

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem large_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemsetCall.MemsetCodeAt e (base+148928))
    (s current : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (hl : 1 < left.wordCount) (hr : 1 < right.wordCount)
    (ready : CountReady (bodyState s) current left right) :
    Eventually (step e) (Post s left right address capacity used ra) (current, base+275) := by
  obtain ⟨lp, lw, rfl⟩ := Product.large_of_count left hl
  obtain ⟨rp, rw, rfl⟩ := Product.large_of_count right hr
  have leftBound := NatAdd.operand_count_bound s.dmem (.large lp lw) owned.left_at
  have rightBound := NatAdd.operand_count_bound s.dmem (.large rp rw) owned.right_at
  have lc : current.regs.r12.toNat = Limbs.sigWords lw := by
    change current.regs.r12.toBitVec.toNat = Limbs.sigWords lw
    rw [ready.left_count]
    exact Nat.mod_eq_of_lt (by omega)
  have rc : current.regs.r13.toNat = Limbs.sigWords rw := by
    change current.regs.r13.toBitVec.toNat = Limbs.sigWords rw
    rw [ready.right_count]
    exact Nat.mod_eq_of_lt (by omega)
  have counts : Reservation.total current = Limbs.sigWords lw+Limbs.sigWords rw := by
    simp only [Reservation.total, lc, rc]
  have stack : current.regs.rsp = s.regs.rsp-88 := ready.frame.stack.trans (body_stack s)
  have stackWord : current.regs.rsp.toBitVec = s.regs.rsp.toBitVec-88 := by
    simp only [stack, UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
  apply Reservation.complete_cps e base hc helper s current (.large lp lw) (.large rp rw)
    address capacity used ra owned ready.frame.memory stackWord ready.frame.arena lc rc hl hr
  · intro t failed outcome
    exact reservation_failure_finish_cps e base hc s current (.large lp lw) (.large rp rw)
      address capacity used ra owned ready.frame.memory ready.frame.output stack ready.frame.simd t failed outcome
  · intro r guardFlags fillFlags t outcome initialized
    have initialized' : MemsetCall.Post
        (Reservation.initializedState current address used guardFlags fillFlags)
        (base+493).toBitVec (8*Reservation.total current) t := by
      simpa only [counts] using initialized
    have initializedMemory := initialized_memory s current (.large lp lw) (.large rp rw)
      address capacity used ra owned ready.frame.memory stackWord ready.frame.arena counts r outcome
      base guardFlags fillFlags t initialized'
    have registers := Reservation.initialized_registers current base address used guardFlags fillFlags t initialized'
    obtain ⟨pcEq, sp, vectors, leftReg, rightReg, countdownReg, rightCopy, lastIndex, totalReg,
      indexZero, bufferReg, resultReg⟩ := registers
    rcases t with ⟨t, pc⟩
    dsimp only at pcEq
    rw [pcEq]
    have pointerNat := allocated_pointer_nat s (.large lp lw) (.large rp rw) address capacity used ra owned r
      (by rw [outcome]; rfl)
    have afterSetup := initializedMemory.setup owned stackWord counts outcome rp (base+512)
    apply Product.setup_cps e base hc t rp
    · have pointerNatEq := congrArg BitVec.toNat ready.right_pointer
      simpa only [initializedMemory.stack, pointerNatEq] using initializedMemory.slot32
    · rw [initializedMemory.stack]
      exact Large.mapped_load _ _ 40 8 8 initializedMemory.locals_mapped (by decide)
    let u := Product.setupState t rp
    apply product_finish_cps e base hc s u lp rp lw rw address capacity used ra owned r outcome
      afterSetup.1.work (by omega) (by omega)
    · simpa only [outcome, NatArithmetic.committed] using afterSetup.1.cursor
    · exact afterSetup.1.output_mapped
    · simpa only [afterSetup.1.stack, ready.frame.output] using afterSetup.1.slot24
    · exact afterSetup.1.stack.trans stack
    · exact vectors.trans ready.frame.simd
    · rfl
    · exact initializedMemory.destination
    · simpa only [u, Product.setupState, leftReg] using ready.left_count
    · simpa only [u, Product.setupState, rightReg] using ready.right_count
    · change t.regs.r14.toBitVec = _
      rw [totalReg, ready.left_count, ready.right_count]
      bv_omega
    · simpa only [u, Product.setupState, indexZero]
    · change t.regs.rbp.toBitVec = _
      rw [lastIndex, ready.left_count, ready.right_countdown]
      bv_omega
    · refine ⟨?_, ?_, ?_⟩
      · have payloadNat := congrArg BitVec.toNat ready.left_payload
        simpa only [afterSetup.1.stack, payloadNat] using afterSetup.1.slot0
      · simpa only [afterSetup.1.stack, pointerNat] using afterSetup.2
      · have sourceNat := congrArg BitVec.toNat ready.left_pointer
        simpa only [afterSetup.1.stack, sourceNat] using afterSetup.1.slot16
    · simpa only [counts] using afterSetup.1.zero_words
    · simpa only [counts] using afterSetup.1.destination_mapped

end SszX86.NatMul
