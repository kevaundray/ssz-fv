import SszX86.NatAddAllocationOwnership

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem large_commit_memory (s t : MachineData) (left right : NatOperand)
    (address capacity used : BitVec 64)
    (frame : ControlFrame (pushedState s) t)
    (count : t.regs.rax.toNat = SszNative.NatAdd.count left right)
    (r : Arena.Reservation) (flags : StatusFlags)
    (model : SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatAdd.writtenWords left right)) :
    (Reservation.Large.reservedState t address used flags).dmem =
      cursorMem s t.dmem (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used := by
  have allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have geometry := SszNative.NatAdd.allocation_geometry left right address.toNat capacity.toNat used.toNat r allocated
  have length : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length =
      SszNative.NatAdd.count left right+1 := by
    rw [model]
    exact SszNative.NatAdd.writtenWords_length left right
  have finish : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used =
      Arena.start address.toNat used.toNat + 8*(SszNative.NatAdd.count left right+1) := by
    simpa only [Arena.finish, length] using geometry.2.2.1
  have arena : t.regs.r9.toBitVec = s.regs.r9.toBitVec := by rw [frame.arena]; rfl
  simp only [Reservation.Large.reservedState, cursorMem, count, finish, arena]

/-- The actual large allocator writes only its cursor before the carry loop.
Every original limb remains owned, including aliases in the used arena prefix. -/
theorem large_commit_resources (s t : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (frame : ControlFrame (pushedState s) t)
    (count : t.regs.rax.toNat = SszNative.NatAdd.count left right)
    (r : Arena.Reservation) (flags : StatusFlags)
    (model : SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatAdd.writtenWords left right)) :
    let u := Reservation.Large.reservedState t address used flags
    WorkFrame s u.dmem (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat) ∧
      left.At (widthLoad u.dmem) ∧ right.At (widthLoad u.dmem) ∧
      widthLoad u.dmem (s.regs.r9.toNat+16) 8 =
        some (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used ∧
      Large.Mapped u.dmem (BitVec.ofNat 64 r.pointer) (8*(SszNative.NatAdd.count left right+1)) ∧
      OutputMapped u := by
  dsimp only
  have allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have geometry := SszNative.NatAdd.allocation_geometry left right address.toNat capacity.toNat used.toNat r allocated
  have memory := large_commit_memory s t left right address capacity used frame count r flags model
  have work : WorkFrame s (Reservation.Large.reservedState t address used flags).dmem
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat) := by
    rw [memory]
    exact (frame.work _).cursor_store owned r allocated
  have totalFrame := work.to_frame owned.stack_low
  refine ⟨work, ?_, ?_, ?_, ?_, ?_⟩
  · exact operand_preserved s left right left address capacity used ra owned _ totalFrame owned.left_at owned.left_owned
  · exact operand_preserved s left right right address capacity used ra owned _ totalFrame owned.right_at owned.right_owned
  · rw [memory]
    apply cursor_store_value
    rw [geometry.2.2.1]
    exact geometry.1.2.2.2.2.1
  · have hm : Large.Mapped (Reservation.Large.reservedState t address used flags).dmem address capacity.toNat := by
      rw [memory]
      exact Large.mapped_store _ _ _ _ _ _ (frame.arena_mapped owned)
    have bounded := allocated_mapped left right address capacity used _ hm r allocated
    simpa only [model, NatArithmetic.committed, SszNative.NatAdd.writtenWords_length] using bounded
  · change Large.Mapped (Reservation.Large.reservedState t address used flags).dmem t.regs.rdi.toBitVec 68
    rw [memory]
    exact Large.mapped_store _ _ _ _ _ _ (frame.output_mapped owned)

end SszX86.NatAdd
