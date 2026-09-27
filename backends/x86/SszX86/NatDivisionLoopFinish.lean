import SszX86.NatDivisionLoopPreserve
import SszX86.NatDivisionNormalizeFinish

namespace SszX86.NatDivision
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Physical copied-buffer handoff at the first reverse-loop load. -/
structure LoopReady (s : MachineData) (operand : NatOperand)
    (divisor address capacity used : BitVec 64) (reservation : Arena.Reservation)
    (t : MachineData) : Prop where
  large : 2 < operand.wordCount
  reserved : Arena.reserve address.toNat capacity.toNat used.toNat operand.wordCount = some reservation
  divisor_reg : t.regs.rbx.toBitVec = divisor
  count : t.regs.r13.toBitVec = BitVec.ofNat 64 (operand.wordCount+1)
  destination : t.regs.r14.toBitVec = BitVec.ofNat 64 reservation.pointer
  index : t.regs.rbp.toBitVec = BitVec.ofNat 64 (8*(operand.wordCount-1))
  remainder : t.regs.r15.toBitVec = 0
  stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 56
  vectors : t.zmms = s.zmms
  loaded : Loop.WordsAt t.dmem t.regs.r14.toBitVec (Limbs.trim operand.words)
  hm : Large.Mapped t.dmem s.regs.rdi.toBitVec 68
  frame : Frame s t.dmem
    (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat)
  cursor : widthLoad t.dmem (s.regs.r8.toNat+16) 8 = some reservation.used
  spill : Mem.loadInt t.dmem t.regs.rsp.toBitVec 8 = some (s.regs.rdi.toNat : Int)
  saved : SavedAt t.dmem t.regs.rsp.toBitVec s
  slot : ∃ old, Mem.loadInt t.dmem (t.regs.rsp.toBitVec-8) 8 = some old

/-- Execute every reverse limb, the real wide-divider calls, normalization,
private result stores, callee-save restoration and RET. -/
theorem loop_finish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base + 160352))
    (s t : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64) (reservation : Arena.Reservation)
    (owned : Owned s operand divisor address capacity used ra)
    (ready : LoopReady s operand divisor address capacity used reservation t) :
    Eventually (step e) (Post s operand divisor address capacity used ra) (t, base + 768) := by
  let input := Limbs.trim operand.words
  let divided := LimbDivision.divideWords divisor input
  have inputLength : input.length = operand.wordCount := Limbs.trim_length _
  have positive : 0 < operand.wordCount := by have := ready.large; omega
  have bounds := Reservation.reserve_bounds s operand divisor address capacity used ra owned
    operand.wordCount positive reservation ready.reserved
  have pointerBound : reservation.pointer < 2^64 := by omega
  have pointerNat : (BitVec.ofNat 64 reservation.pointer).toNat = reservation.pointer := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound]
  have phase := SszNative.NatDivision.phase_reserved operand divisor address.toNat capacity.toNat
    used.toNat owned.divisor_nonzero owned.divisor_ne_one ready.large reservation ready.reserved
  have outputLength : divided.1.length = operand.wordCount :=
    (LimbDivision.divideWords_length divisor input).trans inputLength
  have entryStack := ready.stack
  change t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 56#64 at entryStack
  apply Loop.loop_cps e base hc hdiv t input (by rw [inputLength]; exact positive)
  · simpa [Loop.get, Reg64s.get64, ready.remainder, ready.divisor_reg] using
      Nat.lt_of_lt_of_le (show 0 < 2 by decide) owned.divisor_lower
  · simpa only [Loop.get, Reg64s.get64, inputLength] using ready.index
  · simp only [Loop.get, Reg64s.get64, ready.destination, pointerNat, inputLength]
    exact bounds.2.2.2.2.2.1
  · exact ready.loaded
  · exact ready.slot
  · intro i hi j hj equal
    have apart := owned.arena_stack
    have low := owned.stack_low
    simp only [Loop.get, Reg64s.get64, ready.destination, entryStack] at equal
    rw [inputLength] at hi
    simp only [Body.Apart, ← UInt64.toNat_toBitVec] at apart low
    bv_omega
  intro u finished
  have quotient : Loop.WordsAt u.dmem (BitVec.ofNat 64 reservation.pointer) divided.1 := by
    simpa [Loop.get, Reg64s.get64, ready.destination, ready.divisor_reg, ready.remainder,
      divided, LimbDivision.divideWords] using finished.written
  have remainderNat : u.regs.r15.toBitVec.toNat = divided.2 := by
    simpa [Loop.get, Reg64s.get64, ready.divisor_reg, ready.remainder,
      divided, LimbDivision.divideWords] using finished.remainder
  have remainder : u.regs.r15.toBitVec = BitVec.ofNat 64 divided.2 := by
    apply BitVec.eq_of_toNat_eq
    rw [remainderNat, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (Nat.lt_trans
      (LimbDivision.divideWords_remainder_lt divisor input owned.divisor_nonzero) divisor.isLt)).symm
  have destination : u.regs.r14.toBitVec = BitVec.ofNat 64 reservation.pointer := by
    simpa [Loop.get, Reg64s.get64, ready.destination] using finished.destination
  have stack : u.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 56#64 := by
    simpa [Loop.get, Reg64s.get64, entryStack] using finished.stack
  have count : u.regs.r13.toBitVec = BitVec.ofNat 64 (divided.1.length+1) := by
    simpa [Loop.get, Reg64s.get64, ready.count, outputLength] using finished.count
  have loopFrame : Loop.Frame t.dmem u.dmem (BitVec.ofNat 64 reservation.pointer)
      (s.regs.rsp.toBitVec-56#64) operand.wordCount := by
    simpa [Loop.get, Reg64s.get64, ready.destination, entryStack, inputLength] using finished.frame
  have outputSame := Loop.owned_region s operand divisor address capacity used ra owned
    t.dmem u.dmem operand.wordCount positive reservation ready.reserved loopFrame s.regs.rdi.toBitVec 68
    (by simpa only [UInt64.toNat_toBitVec] using owned.output_bound)
    (by have h := owned.arena_output; simp only [Body.Apart, UInt64.toNat_toBitVec] at *; omega)
    (by simpa only [UInt64.toNat_toBitVec] using owned.output_stack)
  have headerSame := Loop.owned_region s operand divisor address capacity used ra owned
    t.dmem u.dmem operand.wordCount positive reservation ready.reserved loopFrame s.regs.r8.toBitVec 24
    (by simpa only [UInt64.toNat_toBitVec] using owned.header_bound)
    (by have h := owned.arena_header; simp only [Body.Apart, UInt64.toNat_toBitVec] at *; omega)
    (by simpa only [UInt64.toNat_toBitVec] using owned.header_stack)
  apply normalize_finish e base hc s u operand divisor address capacity used ra divided.1 reservation owned
  constructor
  · simp only [phase]
  · simp only [phase, divided, input]
  · simp only [phase, destination, remainder, divided, input]
  · simp only [← UInt64.toNat_toBitVec, destination, pointerNat]
  · change 0 < u.regs.r14.toBitVec.toNat ∧ u.regs.r14.toBitVec.toNat % 8 = 0 ∧
      u.regs.r14.toBitVec.toNat + 8*divided.1.length ≤ 2^64 ∧
      NatMemory.wordsAt (widthLoad u.dmem) u.regs.r14.toBitVec.toNat divided.1
    rw [destination, pointerNat, outputLength]
    refine ⟨bounds.1, bounds.2.1, bounds.2.2.2.2.2.1, ?_⟩
    intro i
    have loaded := quotient i.val i.isLt
    simpa only [widthLoad, BitVec.ofNat_add, Option.map_some, Int.toNat_natCast, Fin.getElem_fin] using
      congrArg (Option.map Int.toNat) loaded
  · have apart := owned.arena_output
    simp only [Body.Apart, ← UInt64.toNat_toBitVec, destination, pointerNat, outputLength] at *
    omega
  · exact count
  · rw [stack, Loop.owned_spill s operand divisor address capacity used ra owned
      t.dmem u.dmem operand.wordCount positive reservation ready.reserved loopFrame]
    simpa only [entryStack] using ready.spill
  · intro i hi
    rw [outputSame i hi]
    exact ready.hm i hi
  · apply Loop.owned_frame s operand divisor address capacity used ra owned t.dmem u.dmem
      operand.wordCount positive reservation ready.reserved _ _ _ ready.frame loopFrame
    · simp only [phase]
    · simpa only [phase, divided, input] using outputLength
  · have same : widthLoad u.dmem (s.regs.r8.toNat+16) 8 =
        widthLoad t.dmem (s.regs.r8.toNat+16) 8 := by
      unfold widthLoad
      congr 1
      apply memmove_loadInt_congr
      intro i hi
      rw [← UInt64.toNat_toBitVec, width_address, memmove_addr_add]
      exact headerSame (16+i) (by omega)
    rw [same, ready.cursor]
    simp only [phase]
  · rw [stack]
    apply Loop.owned_saved s operand divisor address capacity used ra owned t.dmem u.dmem
      operand.wordCount positive reservation ready.reserved loopFrame
    simpa only [entryStack] using ready.saved
  · exact stack
  · exact finished.vectors.trans ready.vectors

end SszX86.NatDivision
