import SszX86.NatAddStackMemory

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- After the prologue no instruction writes the saved-register activation. -/
def WorkFrame (s : MachineData) (m : DataMem) (outcome : NatArithmetic.Outcome NatOperand) : Prop :=
  ∀ a : BitVec 64,
    Body.Outside a.toNat s.regs.rdi.toNat 68 →
    (∀ r, outcome.allocation = some r →
      Body.Outside a.toNat (s.regs.r9.toNat + 16) 8 ∧
      Body.Outside a.toNat r.pointer (8 * outcome.written.length)) →
    m.get? a = (pushedMem s).get? a

theorem WorkFrame.to_frame {s : MachineData} {m : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (low : 48 ≤ s.regs.rsp.toNat)
    (frame : WorkFrame s m outcome) : Frame s m outcome := by
  intro a output activation scratch
  rw [frame a output scratch]
  exact pushed_model_frame s outcome low a output activation scratch

/-- Every byte of the actual saved area survives output and allocated writes. -/
theorem WorkFrame.stack {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    {m : DataMem} (frame : WorkFrame s m
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat))
    (i : Nat) (inside : i < 48) :
    m.get? ((s.regs.rsp.toBitVec - 48) + BitVec.ofNat 64 i) =
      (pushedMem s).get? ((s.regs.rsp.toBitVec - 48) + BitVec.ofNat 64 i) := by
  have low := owned.stack_low
  have natural : ((s.regs.rsp.toBitVec - 48) + BitVec.ofNat 64 i).toNat =
      s.regs.rsp.toNat - 48 + i := by
    change 48 ≤ s.regs.rsp.toBitVec.toNat at low
    change ((s.regs.rsp.toBitVec - 48) + BitVec.ofNat 64 i).toNat =
      s.regs.rsp.toBitVec.toNat - 48 + i
    bv_omega
  apply frame
  · rw [natural]
    have apart := owned.output_stack
    unfold Body.Outside Body.Apart at *
    omega
  · intro r allocated
    rw [natural]
    have bounds := allocation_bounds s left right address capacity used ra owned r allocated
    have apartHeader := owned.header_stack
    have apartArena := owned.arena_stack
    have headerBound := owned.header_bound
    have usedBound := owned.used_bound
    unfold Body.Outside Body.Apart at *
    constructor <;> omega

theorem WorkFrame.saved {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    {m : DataMem} (frame : WorkFrame s m
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat)) :
    SavedAt m (s.regs.rsp.toBitVec - 48) s := by
  have loads (off : Nat) (inside : off+8 ≤ 48) :
      Mem.loadInt m ((s.regs.rsp.toBitVec - 48) + BitVec.ofNat 64 off) 8 =
        Mem.loadInt (pushedMem s) ((s.regs.rsp.toBitVec - 48) + BitVec.ofNat 64 off) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact frame.stack owned (off+i) (by omega)
  have saved := pushed_saved s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have eq := loads 0 (by decide)
    simp only [BitVec.add_zero] at eq
    exact eq.trans saved.rbx
  · exact (loads 8 (by decide)).trans saved.r12
  · exact (loads 16 (by decide)).trans saved.r13
  · exact (loads 24 (by decide)).trans saved.r14
  · exact (loads 32 (by decide)).trans saved.r15
  · exact (loads 40 (by decide)).trans saved.rbp

theorem WorkFrame.return_slot {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    {m : DataMem} (frame : WorkFrame s m
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat)) :
    Mem.loadInt m s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)) := by
  have unchanged : Mem.loadInt m s.regs.rsp.toBitVec 8 = Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 := by
    apply memmove_loadInt_congr
    intro i hi
    have bound := owned.return_bound
    have low := owned.stack_low
    have natural : (s.regs.rsp.toBitVec + BitVec.ofNat 64 i).toNat = s.regs.rsp.toNat+i := by
      change s.regs.rsp.toBitVec.toNat + 8 ≤ 2^64 at bound
      change (s.regs.rsp.toBitVec + BitVec.ofNat 64 i).toNat = s.regs.rsp.toBitVec.toNat+i
      bv_omega
    have totalFrame := frame.to_frame low
    apply totalFrame
    · rw [natural]
      have apart := owned.output_return
      unfold Body.Outside Body.Apart at *
      omega
    · rw [natural]
      unfold Body.Outside
      omega
    · intro r allocated
      rw [natural]
      have bounds := allocation_bounds s left right address capacity used ra owned r allocated
      have apartCursor := owned.cursor_return
      have apartArena := owned.arena_return
      have usedBound := owned.used_bound
      unfold Body.Outside Body.Apart at *
      constructor <;> omega
  exact unchanged.trans owned.return_load

end SszX86.NatAdd
