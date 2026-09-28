import SszX86.NatMulWordMemory
import SszX86.NatMulWordStack
import SszX86.NatAddStackMemory

namespace SszX86.NatMulWord
open SszNative UintCodec

theorem pushed_mapped (s : MachineData) (p : BitVec 64) (n : Nat)
    (hm : Large.Mapped s.dmem p n) : Large.Mapped (pushedMem s) p n := by
  unfold pushedMem NatAdd.pushedMem Delimited.pushedMem
  repeat' first | exact hm | apply Large.mapped_store

theorem pushed_model_frame (s : MachineData) (outcome : NatArithmetic.Outcome NatOperand)
    (low : 64 ≤ s.regs.rsp.toNat) : Frame s (pushedMem s) outcome := by
  intro a _ outside _
  apply NatAdd.pushed_frame
  intro i hi
  change 64 ≤ s.regs.rsp.toBitVec.toNat at low
  change Body.Outside a.toNat (s.regs.rsp.toBitVec.toNat-64) 64 at outside
  unfold Body.Outside at outside
  bv_omega

theorem pushed_operand (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra) :
    operand.At (widthLoad (pushedMem s)) := by
  exact operand_preserved s operand factor address capacity used ra owned _
    (pushed_model_frame s _ owned.stack_low)

theorem pushed_header (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra) :
    Mem.loadInt (pushedMem s) s.regs.r8.toBitVec 8 = some (address.toNat : Int) ∧
      Mem.loadInt (pushedMem s) (s.regs.r8.toBitVec + 8) 8 = some (capacity.toNat : Int) ∧
      Mem.loadInt (pushedMem s) (s.regs.r8.toBitVec + 16) 8 = some (used.toNat : Int) := by
  have unchanged (off : Nat) (inside : off+8 ≤ 24) :
      Mem.loadInt (pushedMem s) (s.regs.r8.toBitVec + BitVec.ofNat 64 off) 8 =
        Mem.loadInt s.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 off) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    apply NatAdd.pushed_frame
    intro j hj
    have low := owned.stack_low
    have bound := owned.header_bound
    have apart := owned.header_stack
    change 64 ≤ s.regs.rsp.toBitVec.toNat at low
    change s.regs.r8.toBitVec.toNat + 24 ≤ 2^64 at bound
    change Body.Apart s.regs.r8.toBitVec.toNat 24 (s.regs.rsp.toBitVec.toNat-64) 64 at apart
    unfold Body.Apart at apart
    bv_omega
  refine ⟨?_, ?_, ?_⟩
  · have same := unchanged 0 (by decide)
    simp only [BitVec.add_zero] at same
    exact same.trans owned.address_load
  · exact (unchanged 8 (by decide)).trans owned.capacity_load
  · exact (unchanged 16 (by decide)).trans owned.used_load

/-- After the six pushes, only the two lower spill slots may be overwritten;
the saved-register region is protected even though the public frame allows
all 64 activation bytes to differ from entry. -/
def WorkFrame (s : MachineData) (m : DataMem) (outcome : NatArithmetic.Outcome NatOperand) : Prop :=
  ∀ a : BitVec 64,
    ResultOutside outcome.result s.regs.rdi.toNat a.toNat →
    Body.Outside a.toNat (s.regs.rsp.toNat - 64) 16 →
    (∀ r, outcome.allocation = some r →
      Body.Outside a.toNat (s.regs.r8.toNat+16) 8 ∧
      Body.Outside a.toNat r.pointer (8*outcome.written.length)) →
    m.get? a = (pushedMem s).get? a

theorem WorkFrame.initial (s : MachineData) (outcome : NatArithmetic.Outcome NatOperand) :
    WorkFrame s (pushedMem s) outcome := by
  intro a output locals scratch
  rfl

theorem WorkFrame.to_frame {s : MachineData} {m : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (low : 64 ≤ s.regs.rsp.toNat)
    (frame : WorkFrame s m outcome) : Frame s m outcome := by
  intro a output activation scratch
  have localOutside : Body.Outside a.toNat (s.regs.rsp.toNat-64) 16 := by
    unfold Body.Outside at *
    omega
  rw [frame a output localOutside scratch]
  exact pushed_model_frame s outcome low a output activation scratch

theorem WorkFrame.stack {s : MachineData} {operand : NatOperand}
    {factor address capacity used ra : BitVec 64} (owned : Owned s operand factor address capacity used ra)
    {m : DataMem} (frame : WorkFrame s m
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat))
    (i : Nat) (inside : i < 48) :
    m.get? ((s.regs.rsp.toBitVec-48) + BitVec.ofNat 64 i) =
      (pushedMem s).get? ((s.regs.rsp.toBitVec-48) + BitVec.ofNat 64 i) := by
  have low := owned.stack_low
  have natural : ((s.regs.rsp.toBitVec-48) + BitVec.ofNat 64 i).toNat = s.regs.rsp.toNat-48+i := by
    change 64 ≤ s.regs.rsp.toBitVec.toNat at low
    change ((s.regs.rsp.toBitVec-48) + BitVec.ofNat 64 i).toNat = s.regs.rsp.toBitVec.toNat-48+i
    bv_omega
  apply frame
  · apply ResultOutside.of_outside
    rw [natural]
    have apart := owned.output_stack
    unfold Body.Outside Body.Apart at *
    omega
  · rw [natural]
    unfold Body.Outside
    omega
  · intro r allocated
    rw [natural]
    have bounds := allocation_bounds s operand factor address capacity used ra owned r allocated
    have apartHeader := owned.header_stack
    have apartArena := owned.arena_stack
    have usedBound := owned.used_bound
    unfold Body.Outside Body.Apart at *
    constructor <;> omega

theorem WorkFrame.saved {s : MachineData} {operand : NatOperand}
    {factor address capacity used ra : BitVec 64} (owned : Owned s operand factor address capacity used ra)
    {m : DataMem} (frame : WorkFrame s m
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat)) :
    SavedAt m (s.regs.rsp.toBitVec-48) s := by
  have loads (off : Nat) (inside : off+8 ≤ 48) :
      Mem.loadInt m ((s.regs.rsp.toBitVec-48) + BitVec.ofNat 64 off) 8 =
        Mem.loadInt (pushedMem s) ((s.regs.rsp.toBitVec-48) + BitVec.ofNat 64 off) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact frame.stack owned (off+i) (by omega)
  have saved := NatAdd.pushed_saved s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have same := loads 0 (by decide)
    simp only [BitVec.add_zero] at same
    exact same.trans saved.rbx
  · exact (loads 8 (by decide)).trans saved.r12
  · exact (loads 16 (by decide)).trans saved.r13
  · exact (loads 24 (by decide)).trans saved.r14
  · exact (loads 32 (by decide)).trans saved.r15
  · exact (loads 40 (by decide)).trans saved.rbp

end SszX86.NatMulWord
