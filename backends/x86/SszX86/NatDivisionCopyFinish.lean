import SszX86.NatDivisionCopyEntry
import SszX86.NatDivisionLoopFinish

namespace SszX86.NatDivision.Copy
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Transfer the actual copied memory and protected activation into the reverse
loop's data-only handoff. All preservation is proved from the copy byte frame. -/
theorem loop_ready (s t u : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (large : 2 < operand.wordCount) (reservation : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat operand.wordCount = some reservation)
    (entry : CopyReady s operand divisor address capacity used ra reservation t)
    (copied : Ready t u (BitVec.ofNat 64 reservation.pointer) operand.words operand.wordCount) :
    LoopReady s operand divisor address capacity used reservation u := by
  have model := reservation_model s operand divisor address capacity used ra owned large reservation reserved
  have bounds := allocation_bounds s operand divisor address capacity used ra owned reservation model.1
  rw [model.2] at bounds
  have pointerBound : reservation.pointer < 2^64 := by omega
  have pointerNat : (BitVec.ofNat 64 reservation.pointer).toNat = reservation.pointer := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound]
  have physical : (BitVec.ofNat 64 reservation.pointer).toNat + 8*operand.wordCount ≤ 2^64 := by
    rw [pointerNat]
    exact bounds.2.2.2.2.2
  have stack : u.regs.rsp.toBitVec = s.regs.rsp.toBitVec-56#64 :=
    copied.stack.trans entry.stack
  have stackApart : Large.Disjoint (s.regs.rsp.toBitVec-64#64)
      (BitVec.ofNat 64 reservation.pointer) 64 (8*operand.wordCount) := by
    intro i hi j hj equal
    have apart := owned.arena_stack
    have low := owned.stack_low
    simp only [Body.Apart, ← UInt64.toNat_toBitVec] at apart low
    bv_omega
  have spillApart : Large.Disjoint (s.regs.rsp.toBitVec-56#64)
      (BitVec.ofNat 64 reservation.pointer) 56 (8*operand.wordCount) := by
    intro i hi j hj equal
    have contradiction := stackApart (8+i) (by omega) j hj
    apply contradiction
    have same : s.regs.rsp.toBitVec-64#64+BitVec.ofNat 64 (8+i) =
        s.regs.rsp.toBitVec-56#64+BitVec.ofNat 64 i := by bv_omega
    rw [same]
    exact equal
  have cursorApart : Large.Disjoint (s.regs.r8.toBitVec+16#64)
      (BitVec.ofNat 64 reservation.pointer) 8 (8*operand.wordCount) := by
    intro i hi j hj equal
    have apart := owned.arena_header
    have header := owned.header_bound
    simp only [Body.Apart, ← UInt64.toNat_toBitVec] at apart header
    bv_omega
  refine {
    large := large
    reserved := reserved
    divisor_reg := copied.divisor.trans entry.divisor_reg
    count := copied.significant.trans entry.significant
    destination := copied.destination
    index := ?_
    remainder := copied.remainder
    stack := stack
    vectors := copied.vectors.trans entry.vectors
    loaded := ?_
    hm := copied.mapped entry.output_mapped
    frame := copied.outcome_frame s _ reservation model.1 pointerNat model.2 physical entry.frame
    cursor := ?_
    spill := ?_
    saved := ?_
    slot := ?_ }
  · change get u .rbp = _
    rw [copied.index, entry.index, BitVec.neg_neg]
  · intro i hi
    have hiCount : i < operand.wordCount := by
      simpa only [Limbs.trim_length, NatOperand.wordCount] using hi
    have hiLength : i < operand.words.length :=
      Nat.lt_of_lt_of_le hiCount (Limbs.sigWords_le_length _)
    change Mem.loadInt u.dmem (get u .r14 + BitVec.ofNat 64 (8*i)) 8 = _
    rw [copied.destination]
    have hl := copied.load physical i hiCount
    simpa [limb, List.getElem?_eq_getElem hiLength, Limbs.trim_eq_take] using hl
  · have same := copied.load_apart (s.regs.r8.toBitVec+16#64) 8 cursorApart
    have observed : widthLoad u.dmem (s.regs.r8.toNat+16) 8 =
        widthLoad t.dmem (s.regs.r8.toNat+16) 8 := by
      unfold widthLoad
      congr 1
    exact observed.trans entry.cursor
  · rw [stack, copied.load_apart (s.regs.rsp.toBitVec-56#64) 8
      (fun i hi j hj => spillApart i (by omega) j hj)]
    exact entry.spill
  · rw [stack]
    exact copied.saved s (s.regs.rsp.toBitVec-56#64) spillApart entry.saved
  · rw [stack]
    change ∃ old, Mem.loadInt u.dmem (s.regs.rsp.toBitVec-56#64-8#64) 8 = some old
    have slotAddress : s.regs.rsp.toBitVec-56#64-8#64 = s.regs.rsp.toBitVec-64#64 := by bv_omega
    rw [slotAddress, copied.load_apart (s.regs.rsp.toBitVec-64#64) 8
      (fun i hi j hj => stackApart i (by omega) j hj)]
    exact entry.callslot

/-- Complete successful allocated path from the cursor commit through copying,
all reverse divisions, normalization, output stores, register restoration and RET. -/
theorem copy_finish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base+160352))
    (s t : MachineData) (operand : NatOperand) (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (large : 2 < operand.wordCount) (reservation : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat operand.wordCount = some reservation)
    (ready : CopyReady s operand divisor address capacity used ra reservation t) :
    Eventually (step e) (Post s operand divisor address capacity used ra) (t, base+627) := by
  apply entry_copy_cps e base hc s t operand divisor address capacity used ra owned large reservation
    reserved ready (Post s operand divisor address capacity used ra)
  intro u copied
  exact loop_finish e base hc hdiv s u operand divisor address capacity used ra reservation owned
    (loop_ready s t u operand divisor address capacity used ra owned large reservation reserved ready copied)

end SszX86.NatDivision.Copy
