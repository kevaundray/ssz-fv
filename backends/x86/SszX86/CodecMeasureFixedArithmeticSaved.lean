import SszX86.CodecMeasureFixedArithmeticSavedCore

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

theorem arithmetic_add_saved (original caller : MachineData) (base : Int64)
    (r : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (address capacity used originalRa ra : BitVec 64) (bytes : Nat)
    (owned : Owned original base r desc address capacity used originalRa bytes)
    (memory : caller.dmem = original.dmem)
    (stack : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (output : caller.regs.rdi.toBitVec = caller.regs.rsp.toBitVec)
    (header : caller.regs.r9.toBitVec = original.regs.rdx.toBitVec)
    (enough : 192 ≤ bytes) (left right : NatOperand) (t : MachineState)
    (post : NatAdd.Post (arithmeticCallState caller ra) left right address capacity used ra t)
    (saved : Output.Saved) (stored : Output.SavedAt caller.dmem caller.regs.rsp.toBitVec saved) :
    Output.SavedAt t.1.dmem caller.regs.rsp.toBitVec saved := by
  have outputNat : caller.regs.rdi.toNat = caller.regs.rsp.toNat := by
    simpa only [UInt64.toNat_toBitVec] using congrArg BitVec.toNat output
  have headerNat : caller.regs.r9.toNat = original.regs.rdx.toNat := by
    simpa only [UInt64.toNat_toBitVec] using congrArg BitVec.toNat header
  apply arithmetic_saved_of_upper_bytes caller.dmem t.1.dmem caller.regs.rsp.toBitVec saved _ stored
  apply arithmetic_upper_bytes original caller base r desc address capacity used originalRa ra bytes 48
    owned memory stack enough (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat)
    t.1.dmem
  · intro a writes
    have bounds := add_writes_geometry left right address.toNat capacity.toNat used.toNat owned.arena_bound a writes
    exact ⟨bounds.1, by omega⟩
  · intro a outOutside stackOutside allocatedOutside
    apply post.frame a
    · change Body.Outside a.toNat caller.regs.rdi.toNat 68
      rw [outputNat]
      unfold Body.Outside at *
      omega
    · simpa only [arithmeticCallState, NatDivision.callState, UInt64.toNat_ofBitVec] using stackOutside
    · intro reservation allocated
      simpa only [arithmeticCallState, NatDivision.callState, headerNat] using allocatedOutside reservation allocated

theorem arithmetic_divide8_saved (original caller : MachineData) (base : Int64)
    (r : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (address capacity used originalRa ra : BitVec 64) (bytes : Nat)
    (owned : Owned original base r desc address capacity used originalRa bytes)
    (memory : caller.dmem = original.dmem)
    (stack : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (output : caller.regs.rdi.toBitVec = caller.regs.rsp.toBitVec)
    (header : caller.regs.r8.toBitVec = original.regs.rdx.toBitVec)
    (enough : 208 ≤ bytes) (operand : NatOperand) (t : MachineState)
    (post : NatDivision.Post (arithmeticCallState caller ra) operand 8 address capacity used ra t)
    (saved : Output.Saved) (stored : Output.SavedAt caller.dmem caller.regs.rsp.toBitVec saved) :
    Output.SavedAt t.1.dmem caller.regs.rsp.toBitVec saved := by
  have outputNat : caller.regs.rdi.toNat = caller.regs.rsp.toNat := by
    simpa only [UInt64.toNat_toBitVec] using congrArg BitVec.toNat output
  have headerNat : caller.regs.r8.toNat = original.regs.rdx.toNat := by
    simpa only [UInt64.toNat_toBitVec] using congrArg BitVec.toNat header
  apply arithmetic_saved_of_upper_bytes caller.dmem t.1.dmem caller.regs.rsp.toBitVec saved _ stored
  apply arithmetic_upper_bytes original caller base r desc address capacity used originalRa ra bytes 64
    owned memory stack enough
    (FixedSize.divisionCall (SszNative.NatDivision.run operand 8 address.toNat capacity.toNat used.toNat)) t.1.dmem
  · intro a writes
    have bounds := divide8_writes_geometry operand address.toNat capacity.toNat used.toNat owned.arena_bound a writes
    exact ⟨bounds.1, by omega⟩
  · intro a outOutside stackOutside allocatedOutside
    apply post.frame a
    · change Body.Outside a.toNat caller.regs.rdi.toNat 68
      rw [outputNat]
      unfold Body.Outside at *
      omega
    · simpa only [arithmeticCallState, NatDivision.callState, UInt64.toNat_ofBitVec] using stackOutside
    · intro reservation allocated
      simpa only [arithmeticCallState, NatDivision.callState, headerNat, FixedSize.divisionCall] using
        allocatedOutside reservation allocated

theorem arithmetic_mul_saved (original caller : MachineData) (base : Int64)
    (r : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (address capacity used originalRa ra : BitVec 64) (bytes : Nat)
    (owned : Owned original base r desc address capacity used originalRa bytes)
    (memory : caller.dmem = original.dmem)
    (stack : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (output : caller.regs.rdi.toBitVec = caller.regs.rsp.toBitVec)
    (header : caller.regs.r9.toBitVec = original.regs.rdx.toBitVec)
    (enough : 240 ≤ bytes) (left right : NatOperand) (t : MachineState)
    (post : NatMul.Post (arithmeticCallState caller ra) left right address capacity used ra t)
    (saved : Output.Saved) (stored : Output.SavedAt caller.dmem caller.regs.rsp.toBitVec saved) :
    Output.SavedAt t.1.dmem caller.regs.rsp.toBitVec saved := by
  have outputNat : caller.regs.rdi.toNat = caller.regs.rsp.toNat := by
    simpa only [UInt64.toNat_toBitVec] using congrArg BitVec.toNat output
  have headerNat : caller.regs.r9.toNat = original.regs.rdx.toNat := by
    simpa only [UInt64.toNat_toBitVec] using congrArg BitVec.toNat header
  apply arithmetic_saved_of_upper_bytes caller.dmem t.1.dmem caller.regs.rsp.toBitVec saved _ stored
  apply arithmetic_upper_bytes original caller base r desc address capacity used originalRa ra bytes 96
    owned memory stack enough (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat)
    t.1.dmem
  · intro a writes
    have bounds := mul_writes_geometry left right address.toNat capacity.toNat used.toNat owned.arena_bound a writes
    exact ⟨bounds.1, by omega⟩
  · intro a outOutside stackOutside allocatedOutside
    apply post.frame a
    · apply NatMul.ResultOutside.of_outside
      change Body.Outside a.toNat caller.regs.rdi.toNat 72
      simpa only [outputNat] using outOutside
    · simpa only [arithmeticCallState, NatDivision.callState, UInt64.toNat_ofBitVec] using stackOutside
    · intro reservation allocated
      simpa only [arithmeticCallState, NatDivision.callState, headerNat] using allocatedOutside reservation allocated

end SszX86.CodecMeasureFixed
