import SszX86.NatDivisionCopyResources

namespace SszX86.NatDivision.Copy
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Physical data at PC627, after the successful used-cursor update. -/
structure CopyReady (s : MachineData) (operand : NatOperand)
    (divisor address capacity used _ra : BitVec 64) (reservation : Arena.Reservation)
    (t : MachineData) : Prop where
  count : get t .rax = BitVec.ofNat 64 operand.wordCount
  length : get t .rdx = BitVec.ofNat 64 operand.words.length
  source : get t .rsi = operand.pointer
  redundant : get t .r8 = BitVec.ofNat 64 (operand.words.length-operand.wordCount)
  mask : get t .rcx = 2305843009213693950#64
  destination : get t .r9 = BitVec.ofNat 64 reservation.pointer
  arena : get t .r14 + get t .rdi = BitVec.ofNat 64 reservation.pointer
  index : get t .rbp = -BitVec.ofNat 64 (8*(operand.wordCount-1))
  divisor_reg : get t .rbx = divisor
  significant : get t .r13 = BitVec.ofNat 64 (operand.wordCount+1)
  stack : get t .rsp = s.regs.rsp.toBitVec-56#64
  vectors : t.zmms = s.zmms
  destination_mapped : Large.Mapped t.dmem (BitVec.ofNat 64 reservation.pointer) (8*operand.wordCount)
  output_mapped : Large.Mapped t.dmem s.regs.rdi.toBitVec 68
  frame : SszX86.NatDivision.Frame s t.dmem
    (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat)
  saved : SavedAt t.dmem (s.regs.rsp.toBitVec-56#64) s
  spill : Mem.loadInt t.dmem (s.regs.rsp.toBitVec-56#64) 8 = some (s.regs.rdi.toNat : Int)
  callslot : ∃ old, Mem.loadInt t.dmem (s.regs.rsp.toBitVec-64#64) 8 = some old
  cursor : widthLoad t.dmem (s.regs.r8.toNat+16) 8 = some reservation.used

/-- Exact output footprint follows from the shared large-division phase. -/
theorem reservation_model (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (large : 2 < operand.wordCount) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat operand.wordCount = some r) :
    (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).allocation = some r ∧
    (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).written.length =
      operand.wordCount := by
  rw [SszNative.NatDivision.phase_reserved operand divisor address.toNat capacity.toNat used.toNat
    owned.divisor_nonzero owned.divisor_ne_one large r reserved]
  exact ⟨rfl, (LimbDivision.divideWords_length _ _).trans (Limbs.trim_length _)⟩

/-- The original operand, not a normalized replacement, supplies every copy load. -/
theorem CopyReady.loads {s t : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64} {r : Arena.Reservation}
    (entry : CopyReady s operand divisor address capacity used ra r t)
    (owned : Owned s operand divisor address capacity used ra) (large : 2 < operand.wordCount) :
    operand.words.length < 2^64 ∧
    (∀ i, i < operand.words.length →
      Mem.loadInt t.dmem (get t .rsi + BitVec.ofNat 64 (8*i)) 8 =
        some ((limb operand.words i).toNat : Int)) := by
  have stored := operand_preserved s operand divisor address capacity used ra owned t.dmem entry.frame
  cases operand with
  | small value =>
    have count := Limbs.sigWords_le_length [value]
    simp only [NatOperand.wordCount, NatOperand.words, List.length_singleton] at large count
    omega
  | large pointer words =>
    obtain ⟨positive, aligned, bound, limbs⟩ := stored
    constructor
    · change words.length < 2^64
      omega
    · intro i hi
      change i < words.length at hi
      rw [entry.source]
      change Mem.loadInt t.dmem (pointer + BitVec.ofNat 64 (8*i)) 8 =
        some ((words[i]?.getD 0#64).toNat : Int)
      rw [List.getElem?_eq_getElem hi]
      change Mem.loadInt t.dmem (pointer + BitVec.ofNat 64 (8*i)) 8 =
        some (words[i].toNat : Int)
      simpa only [width_address] using
        widthLoad_eq t.dmem (pointer.toNat + 8*i) 8 (words[i].toNat) (limbs ⟨i, hi⟩)

/-- Source/copy separation follows from ownership of the free arena suffix. -/
theorem CopyReady.source_apart {s t : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64} {r : Arena.Reservation}
    (entry : CopyReady s operand divisor address capacity used ra r t)
    (owned : Owned s operand divisor address capacity used ra) (large : 2 < operand.wordCount)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat operand.wordCount = some r) :
    Large.Disjoint (get t .rsi) (BitVec.ofNat 64 r.pointer)
      (8*operand.words.length) (8*operand.wordCount) := by
  have model := reservation_model s operand divisor address capacity used ra owned large r reserved
  have bounds := allocation_bounds s operand divisor address capacity used ra owned r model.1
  rw [model.2] at bounds
  have pointerBound : r.pointer < 2^64 := by omega
  rw [entry.source]
  cases operand with
  | small value =>
    have count := Limbs.sigWords_le_length [value]
    simp only [NatOperand.wordCount, NatOperand.words, List.length_singleton] at large count
    omega
  | large pointer words =>
    have source := owned.operand_owned
    change Protected s address capacity used pointer.toNat (8*words.length) at source
    apply Body.apart_bytes
    · exact source.bound
    · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound] using bounds.2.2.2.2.2
    · have apart := source.arena
      simp only [NatOperand.pointer, NatOperand.words, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt pointerBound]
      unfold Body.Apart at *
      omega

/-- Reserved-entry execution delegates only the post-copy continuation. -/
theorem entry_copy_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (large : 2 < operand.wordCount) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat operand.wordCount = some r)
    (entry : CopyReady s operand divisor address capacity used ra r t)
    (P : MachineState → Prop)
    (next : ∀ u, Ready t u (BitVec.ofNat 64 r.pointer) operand.words operand.wordCount →
      Eventually (step e) P (u, base+768)) :
    Eventually (step e) P (t, base+627) := by
  have model := reservation_model s operand divisor address capacity used ra owned large r reserved
  have bounds := allocation_bounds s operand divisor address capacity used ra owned r model.1
  rw [model.2] at bounds
  have pointerBound : r.pointer < 2^64 := by omega
  have countBound : operand.wordCount < 2^61 := by omega
  have loads := entry.loads owned large
  have lengthCount : operand.wordCount ≤ operand.words.length := Limbs.sigWords_le_length _
  apply copy_cps e base hc t (BitVec.ofNat 64 r.pointer) operand.words operand.wordCount
    (by omega) countBound
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound] using bounds.2.2.2.2.2
  · exact loads.1
  · exact entry.count
  · exact entry.length
  · exact entry.mask
  · exact entry.destination
  · exact entry.arena
  · rw [entry.length, entry.redundant]
    bv_omega
  · exact loads.2
  · exact entry.destination_mapped
  · exact entry.source_apart owned large reserved
  · exact next

end SszX86.NatDivision.Copy
