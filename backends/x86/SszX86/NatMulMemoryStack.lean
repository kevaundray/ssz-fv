import SszX86.NatMulMemory
import SszX86.NatMulStack
import SszX86.NatAddStackMemory

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem Owned.push_mapped {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra) :
    Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48 := by
  have hmSub := Delimited.Reservation.mapped_subrange s.dmem (s.regs.rsp.toBitVec - 96)
    96 48 48 owned.stack_mapped (by decide)
  have pointer : s.regs.rsp.toBitVec - 96 + BitVec.ofNat 64 48 = s.regs.rsp.toBitVec - 48 := by
    bv_omega
  rwa [pointer] at hmSub

/-- All existing mapped storage remains mapped after the six real pushes. -/
theorem pushed_mapped (s : MachineData) (p : BitVec 64) (n : Nat)
    (hm : Large.Mapped s.dmem p n) : Large.Mapped (pushedMem s) p n := by
  unfold pushedMem NatAdd.pushedMem Delimited.pushedMem
  repeat' first | exact hm | apply Large.mapped_store

/-- The current RSP after pushes and local reservation is original RSP-88;
its memset return slot and five local slots are the lower 48 envelope bytes. -/
theorem Owned.local_mapped {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra) :
    Large.Mapped (pushedMem s) ((s.regs.rsp.toBitVec - 88) - 8) 48 := by
  have hm := pushed_mapped s _ _ owned.stack_mapped
  have lower := Delimited.Reservation.mapped_subrange (pushedMem s)
    (s.regs.rsp.toBitVec - 96) 96 0 48 hm (by decide)
  have pointer : (s.regs.rsp.toBitVec - 88) - 8 = s.regs.rsp.toBitVec - 96 := by bv_omega
  simpa only [pointer, BitVec.add_zero] using lower

theorem pushed_model_frame (s : MachineData) (outcome : NatArithmetic.Outcome NatOperand)
    (low : 96 ≤ s.regs.rsp.toNat) : Frame s (pushedMem s) outcome := by
  intro a _ outside _
  apply NatAdd.pushed_frame
  intro i hi
  change 96 ≤ s.regs.rsp.toBitVec.toNat at low
  change Body.Outside a.toNat (s.regs.rsp.toBitVec.toNat-96) 96 at outside
  unfold Body.Outside at outside
  bv_omega

theorem pushed_operands (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra) :
    left.At (widthLoad (pushedMem s)) ∧ right.At (widthLoad (pushedMem s)) := by
  have frame := pushed_model_frame s
    (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat) owned.stack_low
  exact ⟨operand_preserved s left right left address capacity used ra owned _ frame
      owned.left_at owned.left_owned,
    operand_preserved s left right right address capacity used ra owned _ frame
      owned.right_at owned.right_owned⟩

theorem pushed_header (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra) :
    Mem.loadInt (pushedMem s) s.regs.r9.toBitVec 8 = some (address.toNat : Int) ∧
      Mem.loadInt (pushedMem s) (s.regs.r9.toBitVec + 8) 8 = some (capacity.toNat : Int) ∧
      Mem.loadInt (pushedMem s) (s.regs.r9.toBitVec + 16) 8 = some (used.toNat : Int) := by
  have unchanged (off : Nat) (inside : off + 8 ≤ 24) :
      Mem.loadInt (pushedMem s) (s.regs.r9.toBitVec + BitVec.ofNat 64 off) 8 =
        Mem.loadInt s.dmem (s.regs.r9.toBitVec + BitVec.ofNat 64 off) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    apply NatAdd.pushed_frame
    intro j hj
    have low := owned.stack_low
    have bound := owned.header_bound
    have apart := owned.header_stack
    change 96 ≤ s.regs.rsp.toBitVec.toNat at low
    change s.regs.r9.toBitVec.toNat + 24 ≤ 2^64 at bound
    change Body.Apart s.regs.r9.toBitVec.toNat 24 (s.regs.rsp.toBitVec.toNat-96) 96 at apart
    unfold Body.Apart at apart
    bv_omega
  refine ⟨?_, ?_, ?_⟩
  · have eq := unchanged 0 (by decide)
    simp only [BitVec.add_zero] at eq
    exact eq.trans owned.address_load
  · exact (unchanged 8 (by decide)).trans owned.capacity_load
  · exact (unchanged 16 (by decide)).trans owned.used_load

/-- Post-prologue writes can use locals and the nested-call return slot, but not
the upper 48 bytes holding the original callee-saved registers. -/
def WorkFrame (s : MachineData) (m : DataMem) (outcome : NatArithmetic.Outcome NatOperand) : Prop :=
  ∀ a : BitVec 64,
    ResultOutside outcome.result s.regs.rdi.toNat a.toNat →
    Body.Outside a.toNat (s.regs.rsp.toNat - 96) 48 →
    (∀ r, outcome.allocation = some r →
      Body.Outside a.toNat (s.regs.r9.toNat+16) 8 ∧
      Body.Outside a.toNat r.pointer (8*outcome.written.length)) →
    m.get? a = (pushedMem s).get? a

theorem WorkFrame.to_frame {s : MachineData} {m : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (low : 96 ≤ s.regs.rsp.toNat)
    (frame : WorkFrame s m outcome) : Frame s m outcome := by
  intro a output activation scratch
  have localOutside : Body.Outside a.toNat (s.regs.rsp.toNat-96) 48 := by
    unfold Body.Outside at *
    omega
  rw [frame a output localOutside scratch]
  exact pushed_model_frame s outcome low a output activation scratch

theorem WorkFrame.stack {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    {m : DataMem} (frame : WorkFrame s m
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat))
    (i : Nat) (inside : i < 48) :
    m.get? ((s.regs.rsp.toBitVec-48) + BitVec.ofNat 64 i) =
      (pushedMem s).get? ((s.regs.rsp.toBitVec-48) + BitVec.ofNat 64 i) := by
  have low := owned.stack_low
  have natural : ((s.regs.rsp.toBitVec-48) + BitVec.ofNat 64 i).toNat = s.regs.rsp.toNat-48+i := by
    change 96 ≤ s.regs.rsp.toBitVec.toNat at low
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
    have bounds := allocation_bounds s left right address capacity used ra owned r allocated
    have apartHeader := owned.header_stack
    have apartArena := owned.arena_stack
    have usedBound := owned.used_bound
    unfold Body.Outside Body.Apart at *
    constructor <;> omega

theorem WorkFrame.saved {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    {m : DataMem} (frame : WorkFrame s m
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat)) :
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
  · have eq := loads 0 (by decide)
    simp only [BitVec.add_zero] at eq
    exact eq.trans saved.rbx
  · exact (loads 8 (by decide)).trans saved.r12
  · exact (loads 16 (by decide)).trans saved.r13
  · exact (loads 24 (by decide)).trans saved.r14
  · exact (loads 32 (by decide)).trans saved.r15
  · exact (loads 40 (by decide)).trans saved.rbp

end SszX86.NatMul
