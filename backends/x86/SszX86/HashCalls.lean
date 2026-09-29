import SszX86.HashContracts
import SszX86.NatMulMemset

namespace SszX86.Hash

abbrev callState := Emit.callState

/-- Actual 6-byte CALL and the mapped return slot it writes. -/
theorem finalize_call69_cps (e : Executable) (base : Int64) (hc : Finalize.CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (slot : Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (callState s (base + 75).toBitVec, base + Int64.ofInt (128192))) :
    Eventually (step e) P (s, base + 69) := by
  have slotLoaded : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      UintCodec.Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 slot (by decide)
  hash_finalize_step 20 using hc
  apply Delimited.store_cps
  · exact slotLoaded
  · simpa [callState, Emit.callState, Effects.All, Int64.add_assoc] using next

/-- Actual 5-byte CALL and the mapped return slot it writes. -/
theorem finalize_call82_cps (e : Executable) (base : Int64) (hc : Finalize.CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (slot : Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (callState s (base + 87).toBitVec, base - 656)) :
    Eventually (step e) P (s, base + 82) := by
  have slotLoaded : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      UintCodec.Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 slot (by decide)
  hash_finalize_step 23 using hc
  apply Delimited.store_cps
  · exact slotLoaded
  · simpa [callState, Emit.callState, Effects.All, Int64.add_assoc, Int64.sub_eq_add_neg] using next

/-- Actual 6-byte CALL and the mapped return slot it writes. -/
theorem finalize_call110_cps (e : Executable) (base : Int64) (hc : Finalize.CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (slot : Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (callState s (base + 116).toBitVec, base + Int64.ofInt (128192))) :
    Eventually (step e) P (s, base + 110) := by
  have slotLoaded : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      UintCodec.Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 slot (by decide)
  hash_finalize_step 30 using hc
  apply Delimited.store_cps
  · exact slotLoaded
  · simpa [callState, Emit.callState, Effects.All, Int64.add_assoc] using next

/-- Actual 5-byte CALL and the mapped return slot it writes. -/
theorem finalize_call138_cps (e : Executable) (base : Int64) (hc : Finalize.CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (slot : Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (callState s (base + 143).toBitVec, base - 656)) :
    Eventually (step e) P (s, base + 138) := by
  have slotLoaded : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      UintCodec.Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 slot (by decide)
  hash_finalize_step 37 using hc
  apply Delimited.store_cps
  · exact slotLoaded
  · simpa [callState, Emit.callState, Effects.All, Int64.add_assoc, Int64.sub_eq_add_neg] using next

/-- Actual 5-byte CALL and the mapped return slot it writes. -/
theorem combine_call198_cps (e : Executable) (base : Int64) (hc : Combine.CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (slot : Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (callState s (base + 203).toBitVec, base - 912)) :
    Eventually (step e) P (s, base + 198) := by
  have slotLoaded : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      UintCodec.Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 slot (by decide)
  hash_combine_step 36 using hc
  apply Delimited.store_cps
  · exact slotLoaded
  · simpa [callState, Emit.callState, Effects.All, Int64.add_assoc, Int64.sub_eq_add_neg] using next

/-- Actual 6-byte CALL and the mapped return slot it writes. -/
theorem combine_call228_cps (e : Executable) (base : Int64) (hc : Combine.CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (slot : Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (callState s (base + 234).toBitVec, base + Int64.ofInt (127872))) :
    Eventually (step e) P (s, base + 228) := by
  have slotLoaded : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      UintCodec.Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 slot (by decide)
  hash_combine_step 44 using hc
  apply Delimited.store_cps
  · exact slotLoaded
  · simpa [callState, Emit.callState, Effects.All, Int64.add_assoc] using next

/-- Actual 6-byte CALL and the mapped return slot it writes. -/
theorem combine_call278_cps (e : Executable) (base : Int64) (hc : Combine.CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (slot : Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (callState s (base + 284).toBitVec, base + Int64.ofInt (127872))) :
    Eventually (step e) P (s, base + 278) := by
  have slotLoaded : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      UintCodec.Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 slot (by decide)
  hash_combine_step 57 using hc
  apply Delimited.store_cps
  · exact slotLoaded
  · simpa [callState, Emit.callState, Effects.All, Int64.add_assoc] using next

/-- Actual 5-byte CALL and the mapped return slot it writes. -/
theorem combine_call317_cps (e : Executable) (base : Int64) (hc : Combine.CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (slot : Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (callState s (base + 322).toBitVec, base - 912)) :
    Eventually (step e) P (s, base + 317) := by
  have slotLoaded : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      UintCodec.Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 slot (by decide)
  hash_combine_step 67 using hc
  apply Delimited.store_cps
  · exact slotLoaded
  · simpa [callState, Emit.callState, Effects.All, Int64.add_assoc, Int64.sub_eq_add_neg] using next

/-- Actual 5-byte CALL and the mapped return slot it writes. -/
theorem combine_call358_cps (e : Executable) (base : Int64) (hc : Combine.CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (slot : Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (callState s (base + 363).toBitVec, base - 912)) :
    Eventually (step e) P (s, base + 358) := by
  have slotLoaded : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      UintCodec.Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 slot (by decide)
  hash_combine_step 75 using hc
  apply Delimited.store_cps
  · exact slotLoaded
  · simpa [callState, Emit.callState, Effects.All, Int64.add_assoc, Int64.sub_eq_add_neg] using next

/-- Actual 6-byte CALL and the mapped return slot it writes. -/
theorem combine_call388_cps (e : Executable) (base : Int64) (hc : Combine.CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (slot : Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (callState s (base + 394).toBitVec, base + Int64.ofInt (127872))) :
    Eventually (step e) P (s, base + 388) := by
  have slotLoaded : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      UintCodec.Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 slot (by decide)
  hash_combine_step 83 using hc
  apply Delimited.store_cps
  · exact slotLoaded
  · simpa [callState, Emit.callState, Effects.All, Int64.add_assoc] using next

/-- Actual 5-byte CALL and the mapped return slot it writes. -/
theorem combine_call407_cps (e : Executable) (base : Int64) (hc : Combine.CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (slot : Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (callState s (base + 412).toBitVec, base - 256)) :
    Eventually (step e) P (s, base + 407) := by
  have slotLoaded : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      UintCodec.Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 slot (by decide)
  hash_combine_step 87 using hc
  apply Delimited.store_cps
  · exact slotLoaded
  · simpa [callState, Emit.callState, Effects.All, Int64.add_assoc, Int64.sub_eq_add_neg] using next

end SszX86.Hash
