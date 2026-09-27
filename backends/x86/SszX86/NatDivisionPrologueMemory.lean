import SszX86.NatDivisionProtected
import SszX86.NatDivisionStack

namespace SszX86.NatDivision
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Lift the modular activation-only byte frame to an absolute, nonwrapping
load outside the entire 64-byte activation. -/
theorem activation_load_congr (s : MachineData) (low : 64 ≤ s.regs.rsp.toNat)
    (m n : DataMem)
    (written : ∀ a : BitVec 64,
      (∀ i < 64, a ≠ (s.regs.rsp.toBitVec - 64) + BitVec.ofNat 64 i) →
        n.get? a = m.get? a)
    (pointer count : Nat) (bound : pointer + count ≤ 2^64)
    (apart : Body.Apart pointer count (s.regs.rsp.toNat - 64) 64) :
    Mem.loadInt n (BitVec.ofNat 64 pointer) count =
      Mem.loadInt m (BitVec.ofNat 64 pointer) count := by
  simp only [Body.Apart, ← UInt64.toNat_toBitVec] at apart low
  apply memmove_loadInt_congr
  intro i hi
  apply written
  intro j hj
  bv_omega

theorem pushed_load_apart (s : MachineData) (low : 64 ≤ s.regs.rsp.toNat)
    (pointer count : Nat) (bound : pointer + count ≤ 2^64)
    (apart : Body.Apart pointer count (s.regs.rsp.toNat - 64) 64) :
    Mem.loadInt (pushedMem s) (BitVec.ofNat 64 pointer) count =
      Mem.loadInt s.dmem (BitVec.ofNat 64 pointer) count :=
  activation_load_congr s low s.dmem (pushedMem s) (pushed_activation_frame s)
    pointer count bound apart

/-- Prologue stores satisfy the complete run's frame for every model outcome. -/
theorem pushed_outcome_frame (s : MachineData) (low : 64 ≤ s.regs.rsp.toNat)
    (outcome : NatArithmetic.Outcome (NatOperand × BitVec 64)) :
    Frame s (pushedMem s) outcome := by
  intro a output activation allocation
  apply pushed_activation_frame s a
  intro i hi
  simp only [Body.Outside, ← UInt64.toNat_toBitVec] at activation low
  bv_omega

/-- All 24 arena-descriptor bytes survive the pushes, including its cursor. -/
theorem Owned.pushed_header_load {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra)
    (off count : Nat) (inside : off + count ≤ 24) :
    Mem.loadInt (pushedMem s) (s.regs.r8.toBitVec + BitVec.ofNat 64 off) count =
      Mem.loadInt s.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 off) count := by
  have bound := owned.header_bound
  have apart := owned.header_stack
  have preserved := pushed_load_apart s owned.stack_low (s.regs.r8.toNat + off) count
    (by omega) (by unfold Body.Apart at *; omega)
  simpa only [← UInt64.toNat_toBitVec, width_address] using preserved

theorem Owned.prologue_operand_at {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    operand.At (widthLoad (prologueState s).dmem) :=
  operand_preserved s operand divisor address capacity used ra owned (pushedMem s)
    (pushed_outcome_frame s owned.stack_low _)

theorem Owned.prologue_operand_view {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    NatCompare.View (prologueState s).dmem operand.pointer operand.payload operand.words :=
  operand_view _ operand owned.prologue_operand_at

/-- The entry argument pair survives unchanged, despite saves into RBX/R12/R13. -/
theorem Owned.prologue_operand_registers {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    (prologueState s).regs.rsi.toBitVec = operand.pointer ∧
      (prologueState s).regs.rdx.toBitVec = operand.payload :=
  ⟨owned.operand_pointer, owned.operand_payload⟩

theorem Owned.prologue_retained_divisor {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    (prologueState s).regs.r13.toBitVec = divisor :=
  owned.divisor_register

theorem Owned.prologue_address_load {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    Mem.loadInt (prologueState s).dmem (prologueState s).regs.r12.toBitVec 8 =
      some (address.toNat : Int) := by
  change Mem.loadInt (pushedMem s) s.regs.r8.toBitVec 8 = _
  have preserved := owned.pushed_header_load 0 8 (by decide)
  simp only [BitVec.add_zero] at preserved
  exact preserved.trans owned.address_load

theorem Owned.prologue_capacity_load {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    Mem.loadInt (prologueState s).dmem ((prologueState s).regs.r12.toBitVec + 8) 8 =
      some (capacity.toNat : Int) :=
  (owned.pushed_header_load 8 8 (by decide)).trans owned.capacity_load

theorem Owned.prologue_used_load {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    Mem.loadInt (prologueState s).dmem ((prologueState s).regs.r12.toBitVec + 16) 8 =
      some (used.toNat : Int) :=
  (owned.pushed_header_load 16 8 (by decide)).trans owned.used_load

theorem Owned.prologue_output_mapped {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    Large.Mapped (prologueState s).dmem (prologueState s).regs.rbx.toBitVec 68 :=
  pushed_mapped s s.regs.rdi.toBitVec 68 owned.output_mapped

theorem Owned.prologue_arena_mapped {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    Large.Mapped (prologueState s).dmem address capacity.toNat :=
  pushed_mapped s address capacity.toNat owned.arena_mapped

/-- Mapping includes the lower CALL slot, not merely the seven saved words. -/
theorem Owned.prologue_activation_mapped {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    Large.Mapped (prologueState s).dmem (s.regs.rsp.toBitVec - 64) 64 :=
  pushed_mapped s (s.regs.rsp.toBitVec - 64) 64 owned.stack_mapped

theorem Owned.prologue_return_load {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) :
    Mem.loadInt (prologueState s).dmem ((prologueState s).regs.rsp.toBitVec + 56) 8 =
      some (Int.ofBytes (wordBytes ra)) := by
  simpa only [prologueState, pushedState, UInt64.toBitVec_ofBitVec,
    BitVec.sub_add_cancel] using (pushed_return_slot s).trans owned.return_load

theorem prologue_saved (s : MachineData) :
    SavedAt (prologueState s).dmem (prologueState s).regs.rsp.toBitVec s := by
  simpa only [prologueState, pushedState, UInt64.toBitVec_ofBitVec] using pushed_saved s

end SszX86.NatDivision
