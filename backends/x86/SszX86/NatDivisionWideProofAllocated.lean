import SszX86.NatDivisionWideProofCall
import SszX86.NatDivisionReserveWideResources

namespace SszX86.NatDivision
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Both real quotient stores precede publication.  The complete two-word
allocation survives the output writes and the actual return sequence. -/
theorem wide_reserved_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (count : operand.wordCount ≤ 2)
    (called : WideCalled s operand divisor address capacity used t)
    (high : t.regs.rdx.toBitVec ≠ 0)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r)
    (flags : StatusFlags) :
    Eventually (step e) (Post s operand divisor address capacity used ra)
      (Reservation.Small.reservedState t address used flags, base + 358) := by
  let u := Reservation.Small.reservedState t address used flags
  let quotient := NatOperand.large (BitVec.ofNat 64 r.pointer)
    [t.regs.rax.toBitVec, t.regs.rdx.toBitVec]
  let remainder := operand.words[0]?.getD 0 - t.regs.rax.toBitVec * divisor
  have outcome := phase_wide_reserved operand divisor t.regs.rax.toBitVec t.regs.rdx.toBitVec
    address.toNat capacity.toNat used.toNat count owned.divisor_nonzero owned.divisor_ne_one
    high called.quotient r reserved
  have arena : t.regs.r12.toBitVec = s.regs.r8.toBitVec := congrArg UInt64.toBitVec called.arena
  have bounds := Reservation.reserve_bounds s operand divisor address capacity used ra owned
    2 (by decide) r reserved
  have pointerNat : (BitVec.ofNat 64 r.pointer).toNat = r.pointer :=
    Nat.mod_eq_of_lt (by omega)
  have ptr : r.pointer = address.toNat + Arena.start address.toNat used.toNat := by
    obtain ⟨checks, shape⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
    rw [shape]
  have physical : WidePublication s operand divisor address capacity used u := by
    refine ⟨?_, ?_, ?_, called.stack, called.vectors, called.output, ?_⟩
    · exact Reservation.Small.reserved_frame_owned s t operand divisor address capacity used ra
        owned arena r reserved _ (by rw [outcome]) (by rw [outcome]) (called.frame _) flags
    · rw [outcome]
      exact Reservation.Small.reserved_cursor_owned s t operand divisor address capacity used ra
        owned arena r reserved flags
    · exact Reservation.Small.reserved_saved_owned s t operand divisor address capacity used ra
        owned arena r reserved called.saved flags
    · exact Reservation.Small.reserved_mapped t address used t.regs.rbx.toBitVec flags 68 called.mapped
  have stored := Reservation.Small.reserved_words_owned s t operand divisor address capacity used ra
    owned r reserved flags
  have apart : Body.Apart r.pointer (8 * [t.regs.rax.toBitVec, t.regs.rdx.toBitVec].length)
      s.regs.rdi.toNat 68 := by
    have separation := owned.arena_output
    simp only [List.length_cons, List.length_nil] at *
    unfold Body.Apart at *
    omega
  have published : NatMemory.wordsAt
      (widthLoad (resultSuccessMem u.dmem s.regs.rdi.toBitVec quotient.pointer quotient.payload remainder))
      r.pointer [t.regs.rax.toBitVec, t.regs.rdx.toBitVec] := by
    apply result_success_preserves_words
    · exact owned.output_bound
    · simpa only [List.length_cons, List.length_nil] using bounds.2.2.2.2.2.1
    · exact apart
    · exact stored
  apply wide_publish_success e base hc s u operand quotient divisor address capacity used ra remainder
    owned physical
  · exact called.reason
  · change BitVec.ofNat 64 (address.toNat + Arena.start address.toNat used.toNat) =
      BitVec.ofNat 64 r.pointer
    rw [ptr]
  · rfl
  · change t.regs.r15.toBitVec - t.regs.rax.toBitVec * t.regs.r13.toBitVec = remainder
    rw [called.low, called.divisor_reg]
  · rw [outcome]
  · change 0 < (BitVec.ofNat 64 r.pointer).toNat ∧
      (BitVec.ofNat 64 r.pointer).toNat % 8 = 0 ∧
      (BitVec.ofNat 64 r.pointer).toNat + 8 * [t.regs.rax.toBitVec, t.regs.rdx.toBitVec].length ≤ 2^64 ∧ _
    rw [pointerNat]
    exact ⟨bounds.1, bounds.2.1, by simpa using bounds.2.2.2.2.2.1, published⟩
  · intro allocation allocated
    rw [outcome] at allocated ⊢
    have same : allocation = r := Option.some.inj allocated |>.symm
    subst allocation
    exact published

end SszX86.NatDivision
