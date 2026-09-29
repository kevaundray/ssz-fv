import SszX86.CodecMeasureFixedArithmeticPostFramesAdd

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

theorem arithmetic_divide8_post_trace (original caller : MachineData) (base : Int64)
    (r : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (address capacity used originalRa ra : BitVec 64) (bytes : Nat)
    (owned : Owned original base r desc address capacity used originalRa bytes)
    (memory : caller.dmem = original.dmem)
    (stack : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (output : caller.regs.rdi.toBitVec = caller.regs.rsp.toBitVec)
    (header : caller.regs.r8.toBitVec = original.regs.rdx.toBitVec)
    (enough : 208 ≤ bytes) (operand : NatOperand) (t : MachineState)
    (post : NatDivision.Post (arithmeticCallState caller ra) operand 8 address capacity used ra t) :
    ArithmeticTracePost original bytes
      (FixedSize.divisionCall (SszNative.NatDivision.run operand 8 address.toNat capacity.toNat used.toNat)) t := by
  have outputNat : caller.regs.rdi.toNat = caller.regs.rsp.toNat := by
    simpa only [UInt64.toNat_toBitVec] using congrArg BitVec.toNat output
  have headerNat : caller.regs.r8.toNat = original.regs.rdx.toNat := by
    simpa only [UInt64.toNat_toBitVec] using congrArg BitVec.toNat header
  refine ⟨?_, ?_, ?_⟩
  · apply arithmetic_frame_lift original caller base r desc address capacity used originalRa ra
      bytes 64 owned memory stack enough _ t.1.dmem
    intro a outOutside stackOutside allocatedOutside
    apply post.frame a
    · change Body.Outside a.toNat caller.regs.rdi.toNat 68
      rw [outputNat]
      unfold Body.Outside at *
      omega
    · simpa only [arithmeticCallState, NatDivision.callState, UInt64.toNat_ofBitVec] using stackOutside
    · intro reservation allocated
      simpa only [arithmeticCallState, NatDivision.callState, headerNat, FixedSize.divisionCall] using
        allocatedOutside reservation allocated
  · intro call member reservation allocated
    have same : call = FixedSize.divisionCall
        (SszNative.NatDivision.run operand 8 address.toNat capacity.toNat used.toNat) :=
      List.mem_singleton.mp member
    subst call
    exact post.written reservation allocated
  · simpa only [arithmeticCallState, NatDivision.callState, headerNat, FixedSize.divisionCall] using post.cursor

end SszX86.CodecMeasureFixed
