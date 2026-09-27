import SszX86.NatDivisionWideProofCall

namespace SszX86.NatDivision
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- A zero high quotient word executes the no-allocation success tail. -/
theorem wide_small_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (count : operand.wordCount ≤ 2)
    (called : WideCalled s operand divisor address capacity used t)
    (high : t.regs.rdx.toBitVec = 0) (flags : StatusFlags) :
    Eventually (step e) (Post s operand divisor address capacity used ra)
      (narrowState t flags, base + 358) := by
  have quotient : Udivti3.value t.regs.rax.toBitVec 0 = operand.value / divisor.toNat := by
    simpa only [high] using called.quotient
  have outcome := phase_wide_small operand divisor t.regs.rax.toBitVec
    address.toNat capacity.toNat used.toNat count owned.divisor_nonzero owned.divisor_ne_one quotient
  have physical : WidePublication s operand divisor address capacity used (narrowState t flags) := by
    refine ⟨called.frame _, ?_, called.saved, called.stack, called.vectors, called.output, called.mapped⟩
    change widthLoad t.dmem (s.regs.r8.toNat + 16) 8 =
      some (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).used
    rw [outcome]
    exact called.cursor
  apply wide_publish_success e base hc s (narrowState t flags) operand
    (.small t.regs.rax.toBitVec) divisor address capacity used ra
    (operand.words[0]?.getD 0 - t.regs.rax.toBitVec * divisor) owned physical
  · exact called.reason
  · rfl
  · rfl
  · change t.regs.r15.toBitVec - t.regs.rax.toBitVec * t.regs.r13.toBitVec = _
    rw [called.low, called.divisor_reg]
  · simp only [outcome, NatArithmetic.unchanged]
  · trivial
  · simp [outcome, NatArithmetic.unchanged]

/-- A failed real reservation has no cursor or payload writes.  Caller-saved
register changes do not weaken the exact publication and return contract. -/
theorem wide_reservation_failure_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t u : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (count : operand.wordCount ≤ 2)
    (called : WideCalled s operand divisor address capacity used t)
    (high : t.regs.rdx.toBitVec ≠ 0)
    (failure : Arena.reserve address.toNat capacity.toNat used.toNat 2 = none)
    (frame : Reservation.Small.Frame t u) (memory : u.dmem = t.dmem) :
    Eventually (step e) (Post s operand divisor address capacity used ra) (u, base + 379) := by
  have outcome := phase_wide_failure operand divisor t.regs.rax.toBitVec t.regs.rdx.toBitVec
    address.toNat capacity.toNat used.toNat count owned.divisor_nonzero owned.divisor_ne_one
    high called.quotient failure
  have output : u.regs.rbx = t.regs.rbx := UInt64.toBitVec_inj.mp
    (frame.2 .rbx (by decide) (by decide) (by decide) (by decide))
  have stack : u.regs.rsp.toBitVec = t.regs.rsp.toBitVec :=
    frame.2 .rsp (by decide) (by decide) (by decide) (by decide)
  apply wide_publish_error e base hc s u operand divisor address capacity used ra owned
    (outcome := outcome)
  refine ⟨?_, ?_, ?_, stack.trans called.stack, frame.1.trans called.vectors,
    output.trans called.output, ?_⟩
  · rw [memory]
    exact called.frame _
  · rw [memory, outcome]
    exact called.cursor
  · rw [memory]
    exact called.saved
  · change Large.Mapped u.dmem u.regs.rbx.toBitVec 68
    rw [memory, output]
    exact called.mapped

end SszX86.NatDivision
