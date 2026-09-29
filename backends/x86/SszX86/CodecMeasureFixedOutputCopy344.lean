import SszX86.CodecMeasureFixedOutputCopyMemory

namespace SszX86.CodecMeasureFixed.Output
open BoolCodec UintCodec Serialize.Publish

def copied344 (s : MachineData) (v : Image) : MachineData :=
  {s with regs := {s.regs with
    rdx := UInt64.ofBitVec (v.padding.setWidth 64)
    rsi := UInt64.ofBitVec v.w4},
    dmem := copy344Mem s.dmem s.regs.rbx.toBitVec v}

/-- Raw PC344 cut: preloaded words need only equal the physical image. -/
theorem copy344_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (v : Image)
    (image : ImageAt s.dmem s.regs.rsp.toBitVec v)
    (apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rbx.toBitVec 72 72)
    (mapped : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (r14 : s.regs.r14.toBitVec = v.w0) (r15 : s.regs.r15.toBitVec = v.w1)
    (rcx : s.regs.rcx.toBitVec = v.w2)
    (rax : s.regs.rax.toBitVec = v.tag.setWidth 64)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (copied344 s v, base + 694)) :
    Eventually (step e) P (s, base + 344) := by
  codec_fixed_output_read 87 using hc word image.w7
  codec_fixed_output_store 88 at 56 width 8 using hc mapped mapped
  codec_fixed_output_read 89 using hc word image.w6
  codec_fixed_output_store 90 at 48 width 8 using hc mapped mapped
  codec_fixed_output_read 91 using hc word image.w5
  codec_fixed_output_store 92 at 40 width 8 using hc mapped mapped
  codec_fixed_output_read 93 using hc word image.w3
  codec_fixed_output_read 94 using hc word image.w4
  codec_fixed_output_store 95 at 32 width 8 using hc mapped mapped
  codec_fixed_output_store 96 at 24 width 8 using hc mapped mapped
  codec_fixed_output_read 97 using hc word image.padding
  codec_fixed_output_store 98 at 0 width 8 using hc mapped mapped
  codec_fixed_output_store 99 at 8 width 8 using hc mapped mapped
  codec_fixed_output_store 100 at 16 width 8 using hc mapped mapped
  codec_fixed_output_store 101 at 64 width 4 using hc mapped mapped
  codec_fixed_output_store 102 at 68 width 4 using hc mapped mapped
  codec_measure_fixed_step 103 using hc
  simpa [copied344, copy344Mem, r14, r15, rcx, rax,
    BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_setWidth_of_le] using next

end SszX86.CodecMeasureFixed.Output
