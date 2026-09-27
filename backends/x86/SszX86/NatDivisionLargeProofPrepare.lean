import SszX86.NatDivisionSelect
import SszX86.NatDivisionPrologueMemory
import SszX86.NatDivisionFrame
import SszX86.DelimitedWorkMemory

namespace SszX86.NatDivision
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The real large-path output spill, before either reservation outcome. -/
def largeSpillMem (s : MachineData) : DataMem :=
  Mem.storeInt (pushedMem s) (s.regs.rsp.toBitVec - 56) 8 s.regs.rdi.toBitVec.toInt

/-- The second scan retains the original borrowed representation and records
its significant prefix separately from its physical length. -/
def largeCountedState (s : MachineData) (operand : NatOperand)
    (flags : StatusFlags) : MachineData :=
  { prologueState s with
    dmem := largeSpillMem s
    regs := { (prologueState s).regs with
      rax := UInt64.ofNat operand.wordCount
      rcx := UInt64.ofNat operand.wordCount
      rbx := s.regs.rcx
      rbp := UInt64.ofBitVec (-BitVec.ofNat 64 (8*(operand.wordCount-1)))
      r8 := UInt64.ofNat (operand.words.length-operand.wordCount)
      r13 := UInt64.ofNat (operand.wordCount+1)
      r15 := 0 }
    status := flags }

theorem large_spill_frame (s : MachineData) (low : 64 ≤ s.regs.rsp.toNat)
    (outcome : NatArithmetic.Outcome (NatOperand × BitVec 64)) :
    Frame s (largeSpillMem s) outcome :=
  (pushed_outcome_frame s low outcome).store_stack low 56 8 _ (by decide) (by decide)

theorem large_spill_mapped (s : MachineData) (pointer : BitVec 64) (count : Nat)
    (hm : Large.Mapped s.dmem pointer count) :
    Large.Mapped (largeSpillMem s) pointer count :=
  Large.mapped_store _ _ _ _ _ _ (pushed_mapped s pointer count hm)

theorem large_spill_output (s : MachineData) :
    Mem.loadInt (largeSpillMem s) (s.regs.rsp.toBitVec - 56) 8 =
      some (s.regs.rdi.toNat : Int) := by
  simpa only [largeSpillMem, UInt64.toNat_toBitVec] using
    Delimited.stored_word_load (pushedMem s) (s.regs.rsp.toBitVec - 56)
      s.regs.rdi.toBitVec

/-- The physical operand supplies every rescan load even if it aliases the
consumed arena prefix. Only the disjoint activation has been written. -/
theorem large_spill_operand {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    operand.At (widthLoad (largeSpillMem s)) :=
  operand_preserved s operand divisor address capacity used ra owned _
    (large_spill_frame s owned.stack_low _)

/-- Execute output spill and the entire positive-count rescan, PC83 through
PC160. No canonical-input or successful-allocation hypothesis is used. -/
theorem large_counted_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (count : 2 < operand.wordCount) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (largeCountedState s operand flags, base + 160)) :
    Eventually (step e) P
      (scanState (prologueState s) (BitVec.ofNat 64 operand.wordCount)
        (BitVec.ofNat 64 operand.wordCount) flags, base + 83) := by
  have large : ∃ pointer words, operand = .large pointer words := by
    cases operand with
    | small limb =>
      have bound := Limbs.sigWords_le_length [limb]
      simp only [NatOperand.wordCount, NatOperand.words, List.length_singleton] at count bound
      omega
    | large pointer words => exact ⟨pointer, words, rfl⟩
  obtain ⟨pointer, words, rfl⟩ := large
  have physical := owned.operand_at
  obtain ⟨positive, aligned, bound, limbs⟩ := physical
  have lengthBound : words.length + 1 < 2^64 := by omega
  have countBound := Limbs.sigWords_le_length words
  apply large_start_cps e base hc
  · exact activation_load _ s.regs.rsp.toBitVec 56 owned.prologue_activation_mapped
      (by decide) (by decide)
  intro startFlags
  let t := largeStart
    (scanState (prologueState s) (BitVec.ofNat 64 (NatOperand.large pointer words).wordCount)
      (BitVec.ofNat 64 (NatOperand.large pointer words).wordCount) flags) startFlags
  have loaded := operand_view (largeSpillMem s) (.large pointer words) (large_spill_operand owned)
  have loads : ∀ i : Fin words.length,
      Mem.loadInt t.dmem (t.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int) := by
    rcases loaded with impossible | ⟨_, _, _, loads⟩
    · have zero : pointer = 0 := impossible.1
      simp [zero] at positive
    · simpa only [t, largeStart, scanState, prologueState, pushedState,
        largeSpillMem, owned.operand_pointer, NatOperand.pointer, NatOperand.words] using loads
  have initial : countState t (BitVec.ofNat 64 (words.length+1))
      t.regs.rbp.toBitVec t.regs.r8.toBitVec t.regs.r13.toBitVec startFlags = t := by
    have payload := owned.operand_payload
    simp only [NatOperand.payload] at payload
    simp [t, countState, largeStart, scanState, prologueState, pushedState,
      payload, BitVec.ofNat_add]
  change Eventually (step e) P (t, base + 128)
  rw [← initial]
  apply count_scan e base hc t words lengthBound loads P words.length (by omega)
    (by exact Nat.lt_trans (by decide : 0 < 2) count)
  intro finishFlags
  have payload := owned.operand_payload
  simp only [NatOperand.payload] at payload
  have indexEq : -(BitVec.ofNat 64 words.length * 8#64) +
      BitVec.ofNat 64 (8*(words.length-Limbs.sigWords words+1)) =
        -BitVec.ofNat 64 (8*(Limbs.sigWords words-1)) := by
    have positiveCount : 0 < Limbs.sigWords words := by exact Nat.lt_trans (by decide : 0 < 2) count
    have distance : 8*(words.length-Limbs.sigWords words+1) +
        8*(Limbs.sigWords words-1) = 8*words.length := by omega
    simp only [← BitVec.ofNat_mul]
    bv_omega
  have skipEq : -1#64 + BitVec.ofNat 64 (words.length-Limbs.sigWords words+1) =
      BitVec.ofNat 64 (words.length-Limbs.sigWords words) := by bv_omega
  have indexReg : t.regs.rbp.toBitVec +
      BitVec.ofNat 64 (8*(words.length-Limbs.sigWords words+1)) =
        -BitVec.ofNat 64 (8*(Limbs.sigWords words-1)) := by
    change -(s.regs.rdx.toBitVec * 8#64) + _ = _
    rw [payload]
    exact indexEq
  have skippedReg : t.regs.r8.toBitVec +
      BitVec.ofNat 64 (words.length-Limbs.sigWords words+1) =
        BitVec.ofNat 64 (words.length-Limbs.sigWords words) := skipEq
  change Eventually (step e) P
    (countState t (BitVec.ofNat 64 (Limbs.sigWords words))
      (t.regs.rbp.toBitVec + BitVec.ofNat 64 (8*(words.length-Limbs.sigWords words+1)))
      (t.regs.r8.toBitVec + BitVec.ofNat 64 (words.length-Limbs.sigWords words+1))
      (BitVec.ofNat 64 (Limbs.sigWords words+1)) finishFlags, base + 160)
  rw [indexReg, skippedReg]
  exact next finishFlags

end SszX86.NatDivision
