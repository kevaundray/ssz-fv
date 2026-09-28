import SszX86.NatMulWordLargeMemoryFrame

namespace SszX86.NatMulWord
open SszNative UintCodec

theorem large_destination_mapped (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (m : DataMem) (hm : Large.Mapped m (address+used) (capacity.toNat-used.toNat))
    (r : Arena.Reservation) (words : List (BitVec 64))
    (model : SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r words) :
    Large.Mapped m (BitVec.ofNat 64 r.pointer) (8*words.length) := by
  have allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have hmDst := allocated_mapped s operand factor address capacity used ra owned m hm r allocated
  simpa only [model, NatArithmetic.committed] using hmDst

/-- Row stores preserve the actual committed arena cursor. -/
theorem buffer_cursor_load (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r)
    (before after : DataMem) (buffer : NatMul.BufferFrame before after r.pointer
      (8*(SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length)) :
    widthLoad after (s.regs.r8.toNat+16) 8 = widthLoad before (s.regs.r8.toNat+16) 8 := by
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  apply buffer
  have headerBound := owned.header_bound
  have bounds := allocation_bounds s operand factor address capacity used ra owned r allocated
  have apart := owned.arena_header
  have usedBound := owned.used_bound
  have natural : (BitVec.ofNat 64 (s.regs.r8.toNat+16)+BitVec.ofNat 64 i).toNat = s.regs.r8.toNat+16+i := by
    bv_omega
  rw [natural]
  unfold Body.Outside Body.Apart at *
  omega

/-- In particular offset zero preserves the low product used by normalization. -/
theorem buffer_stack_load (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r)
    (before after : DataMem) (buffer : NatMul.BufferFrame before after r.pointer
      (8*(SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length))
    (off count : Nat) (inside : off+count ≤ 64) :
    Mem.loadInt after ((s.regs.rsp.toBitVec-64)+BitVec.ofNat 64 off) count =
      Mem.loadInt before ((s.regs.rsp.toBitVec-64)+BitVec.ofNat 64 off) count := by
  have low := owned.stack_low
  have natural : ((s.regs.rsp.toBitVec-64)+BitVec.ofNat 64 off).toNat = s.regs.rsp.toNat-64+off := by
    change 64 ≤ s.regs.rsp.toBitVec.toNat at low
    change ((s.regs.rsp.toBitVec-64)+BitVec.ofNat 64 off).toNat = s.regs.rsp.toBitVec.toNat-64+off
    bv_omega
  apply buffer.load
  · rw [natural]
    have bound := s.regs.rsp.toBitVec.isLt
    change s.regs.rsp.toNat < 2^64 at bound
    omega
  · rw [natural]
    have bounds := allocation_bounds s operand factor address capacity used ra owned r allocated
    have apart := owned.arena_stack
    have usedBound := owned.used_bound
    unfold Body.Apart at *
    omega

theorem buffer_output_mapped (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r)
    (before after : DataMem) (buffer : NatMul.BufferFrame before after r.pointer
      (8*(SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length))
    (hm : Large.Mapped before s.regs.rdi.toBitVec 72) : Large.Mapped after s.regs.rdi.toBitVec 72 := by
  apply buffer.mapped _ _ hm owned.output_bound
  have bounds := allocation_bounds s operand factor address capacity used ra owned r allocated
  have apart := owned.arena_output
  have usedBound := owned.used_bound
  change Body.Apart s.regs.rdi.toNat 72 r.pointer _
  unfold Body.Apart at *
  omega

theorem large_publish_cursor (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (before after : DataMem) (result : Except NatArithmetic.Failure NatOperand)
    (publish : NatMul.PublishFrame s before after result) :
    widthLoad after (s.regs.r8.toNat+16) 8 = widthLoad before (s.regs.r8.toNat+16) 8 := by
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  apply publish
  apply NatMul.ResultOutside.of_outside
  have bound := owned.header_bound
  have apart := owned.header_output
  have natural : (BitVec.ofNat 64 (s.regs.r8.toNat+16)+BitVec.ofNat 64 i).toNat = s.regs.r8.toNat+16+i := by
    bv_omega
  rw [natural]
  unfold Body.Outside Body.Apart at *
  omega

theorem large_publish_written (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (before after : DataMem) (result : Except NatArithmetic.Failure NatOperand)
    (publish : NatMul.PublishFrame s before after result) (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r)
    (stored : NatMemory.wordsAt (widthLoad before) r.pointer
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written) :
    NatMemory.wordsAt (widthLoad after) r.pointer
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written := by
  intro index
  have unchanged : widthLoad after (r.pointer+8*index.val) 8 = widthLoad before (r.pointer+8*index.val) 8 := by
    unfold widthLoad
    congr 1
    apply memmove_loadInt_congr
    intro i hi
    apply publish
    apply NatMul.ResultOutside.of_outside
    have bounds := allocation_bounds s operand factor address capacity used ra owned r allocated
    have apart := owned.arena_output
    have usedBound := owned.used_bound
    have ix := index.isLt
    have natural : (BitVec.ofNat 64 (r.pointer+8*index.val)+BitVec.ofNat 64 i).toNat = r.pointer+8*index.val+i := by
      bv_omega
    rw [natural]
    unfold Body.Outside Body.Apart at *
    omega
  exact unchanged.trans (stored index)

/-- The two stack spills follow the cursor commit but cannot change it. -/
theorem cursor_after_local (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (m : DataMem) (off count : Nat) (inside : off+count ≤ 16) (value : Int) :
    widthLoad (Mem.storeInt m ((s.regs.rsp.toBitVec-64)+BitVec.ofNat 64 off) count value)
        (s.regs.r8.toNat+16) 8 = widthLoad m (s.regs.r8.toNat+16) 8 := by
  unfold widthLoad
  congr 1
  apply BoolCodec.load_store_disjoint
  intro i hi j hj equal
  have low := owned.stack_low
  have bound := owned.header_bound
  have apart := owned.header_stack
  change 64 ≤ s.regs.rsp.toBitVec.toNat at low
  change s.regs.r8.toBitVec.toNat+24 ≤ 2^64 at bound
  change Body.Apart s.regs.r8.toBitVec.toNat 24 (s.regs.rsp.toBitVec.toNat-64) 64 at apart
  change (BitVec.ofNat 64 (s.regs.r8.toBitVec.toNat+16)+BitVec.ofNat 64 i) =
    ((s.regs.rsp.toBitVec-64)+BitVec.ofNat 64 off)+BitVec.ofNat 64 j at equal
  unfold Body.Apart at apart
  bv_omega

theorem local_spill_load (m : DataMem) (sp : BitVec 64) (readOff writeOff : Nat)
    (readBound : readOff+8 ≤ 16) (writeBound : writeOff+8 ≤ 16)
    (apart : readOff+8 ≤ writeOff ∨ writeOff+8 ≤ readOff) (value : Int) :
    Mem.loadInt (Mem.storeInt m (sp+BitVec.ofNat 64 writeOff) 8 value)
        (sp+BitVec.ofNat 64 readOff) 8 = Mem.loadInt m (sp+BitVec.ofNat 64 readOff) 8 := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  bv_omega

end SszX86.NatMulWord
