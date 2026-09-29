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
  change 1 < Limbs.sigWords lw at hl
  change 1 < Limbs.sigWords rw at hr
  have leftBound := NatAdd.operand_count_bound s.dmem (.large lp lw) owned.left_at
  have rightBound := NatAdd.operand_count_bound s.dmem (.large rp rw) owned.right_at
  change Limbs.sigWords lw + 2 < 2^64 at leftBound
  change Limbs.sigWords rw + 2 < 2^64 at rightBound
  have leftCount : current.regs.r12.toBitVec = BitVec.ofNat 64 (Limbs.sigWords lw) := ready.left_count
  have rightCount : current.regs.r13.toBitVec = BitVec.ofNat 64 (Limbs.sigWords rw) := ready.right_count
  have rightCountdown : current.regs.r10.toBitVec = 1 - BitVec.ofNat 64 (Limbs.sigWords rw) :=
    ready.right_countdown
  have currentOutput : current.regs.rdi = s.regs.rdi := ready.frame.output
  have lc : current.regs.r12.toNat = Limbs.sigWords lw := by
    change current.regs.r12.toBitVec.toNat = Limbs.sigWords lw
    rw [leftCount]
    exact Nat.mod_eq_of_lt (by omega)
  have rc : current.regs.r13.toNat = Limbs.sigWords rw := by
    change current.regs.r13.toBitVec.toNat = Limbs.sigWords rw
    rw [rightCount]
    exact Nat.mod_eq_of_lt (by omega)
  have counts : Reservation.total current = Limbs.sigWords lw+Limbs.sigWords rw := by
    simp only [Reservation.total, lc, rc]
  have stack : current.regs.rsp = s.regs.rsp-88 := ready.frame.stack.trans (body_stack s)
  have stackWord : current.regs.rsp.toBitVec = s.regs.rsp.toBitVec-88 := by
    word_simpa [UInt64.toBitVec_sub] using congrArg UInt64.toBitVec stack
  apply Reservation.complete_cps e base hc helper s current (.large lp lw) (.large rp rw)
    address capacity used ra owned ready.frame.memory stackWord ready.frame.arena lc rc hl hr
  · intro t failed outcome
    exact reservation_failure_finish_cps e base hc s current (.large lp lw) (.large rp rw)
      address capacity used ra owned ready.frame.memory ready.frame.output stack ready.frame.simd t failed outcome
  · intro r guardFlags fillFlags t outcome initialized
    have initialized' : MemsetCall.Post
        (Reservation.initializedState current address used guardFlags fillFlags)
        (base+493).toBitVec (8*Reservation.total current) t := by
      simpa only [counts, NatOperand.wordCount, NatOperand.words] using initialized
    have initializedMemory := initialized_memory s current (.large lp lw) (.large rp rw)
      address capacity used ra owned ready.frame.memory stackWord ready.frame.arena counts r outcome
      base guardFlags fillFlags t initialized'
    have registers := Reservation.initialized_registers current base address used guardFlags fillFlags t initialized'
    obtain ⟨pcEq, sp, vectors, leftReg, rightReg, countdownReg, rightCopy, lastIndex, totalReg,
      indexZero, bufferReg, resultReg⟩ := registers
    rcases t with ⟨t, pc⟩
    dsimp only at pcEq sp vectors leftReg rightReg countdownReg rightCopy lastIndex totalReg indexZero bufferReg resultReg
    rw [pcEq]
    have pointerNat := allocated_pointer_nat s (.large lp lw) (.large rp rw) address capacity used ra owned r
      (by rw [outcome]; rfl)
    have afterSetup := initializedMemory.setup owned stackWord counts outcome rp (base+512)
    apply Product.setup_cps e base hc t rp
    · have pointerNatEq : current.regs.rcx.toNat = rp.toNat := congrArg BitVec.toNat ready.right_pointer
      simpa only [sp, pointerNatEq] using initializedMemory.slot32
    · rw [initializedMemory.stack]
      exact Large.mapped_load _ _ 40 8 8 initializedMemory.locals_mapped (by decide)
    let u := Product.setupState t rp
    have setupMemory : Initialized s current (.large lp lw) (.large rp rw)
        address capacity used r (u, base+512) := afterSetup.1
    have setupStack : u.regs.rsp = current.regs.rsp := setupMemory.stack
    apply product_finish_cps e base hc s u lp rp lw rw address capacity used ra owned r outcome
      setupMemory.work (by omega) (by omega)
    · simpa only [outcome, NatArithmetic.committed] using setupMemory.cursor
    · exact setupMemory.output_mapped
    · rw [setupStack]
      simpa only [currentOutput] using setupMemory.slot24
    · exact setupStack.trans stack
    · exact vectors.trans ready.frame.simd
    · rfl
    · exact initializedMemory.destination
    · change t.regs.r12.toBitVec = _
      rw [leftReg]
      exact leftCount
    · change t.regs.r13.toBitVec = _
      rw [rightReg]
      exact rightCount
    · change t.regs.r14.toBitVec = _
      rw [totalReg, leftCount, rightCount]
      simp only [BitVec.ofNat_add, BitVec.add_comm]
    · change t.regs.r15.toBitVec = 0#64
      word_simpa [] using congrArg UInt64.toBitVec indexZero
    · change t.regs.rbp.toBitVec = _
      rw [lastIndex, leftCount, rightCountdown]
      simp only [BitVec.ofNat_add]
      rw [BitVec.sub_eq_add_neg, BitVec.neg_sub,
        BitVec.add_comm (-1) (BitVec.ofNat 64 (Limbs.sigWords rw)),
        ← BitVec.add_assoc, ← BitVec.sub_eq_add_neg]
    · refine ⟨?_, ?_, ?_⟩
      · have payloadNat : current.regs.rax.toNat = (BitVec.ofNat 64 lw.length).toNat :=
          congrArg BitVec.toNat ready.left_payload
        rw [setupStack]
        simpa only [payloadNat] using setupMemory.slot0
      · have storedPointer : Mem.loadInt u.dmem (current.regs.rsp.toBitVec+8#64) 8 =
            some (r.pointer : Int) := afterSetup.2
        rw [setupStack]
        simpa only [pointerNat] using storedPointer
      · have sourceNat : current.regs.rsi.toNat = lp.toNat := congrArg BitVec.toNat ready.left_pointer
        rw [setupStack]
        simpa only [sourceNat] using setupMemory.slot16
    · simpa only [counts] using setupMemory.zero_words
    · simpa only [counts] using setupMemory.destination_mapped

end SszX86.NatMul
