import SszX86.CodecMeasureFixedOutputCopyMemory

namespace SszX86.CodecMeasureFixed.Output
open BoolCodec UintCodec Serialize.Publish

def copied455 (s : MachineData) (v : Image) : MachineData :=
  {s with regs := {s.regs with
    rdi := UInt64.ofBitVec (v.padding.setWidth 64)
    r8 := UInt64.ofBitVec v.w4},
    dmem := copy455Mem s.dmem s.regs.rbx.toBitVec v}

theorem copy455_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (v : Image)
    (image : ImageAt s.dmem s.regs.rsp.toBitVec v)
    (apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rbx.toBitVec 72 72)
    (mapped : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (rcx : s.regs.rcx.toBitVec = v.w0) (rsi : s.regs.rsi.toBitVec = v.w1)
    (rdx : s.regs.rdx.toBitVec = v.w2)
    (rax : s.regs.rax.toBitVec = v.tag.setWidth 64)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (copied455 s v, base + 694)) :
    Eventually (step e) P (s, base + 455) := by
  codec_fixed_output_read 115 using hc word image.w7
  codec_fixed_output_store 116 at 56 width 8 using hc mapped mapped
  codec_fixed_output_read 117 using hc word image.w6
  codec_fixed_output_store 118 at 48 width 8 using hc mapped mapped
  codec_fixed_output_read 119 using hc word image.w5
  codec_fixed_output_store 120 at 40 width 8 using hc mapped mapped
  codec_fixed_output_read 121 using hc word image.w3
  codec_fixed_output_read 122 using hc word image.w4
  codec_fixed_output_store 123 at 32 width 8 using hc mapped mapped
  codec_fixed_output_store 124 at 24 width 8 using hc mapped mapped
  codec_fixed_output_read 125 using hc word image.padding
  codec_fixed_output_store 126 at 8 width 8 using hc mapped mapped
  codec_fixed_output_store 127 at 16 width 8 using hc mapped mapped
  codec_fixed_output_store 128 at 0 width 8 using hc mapped mapped
  codec_fixed_output_store 129 at 64 width 4 using hc mapped mapped
  codec_fixed_output_store 130 at 68 width 4 using hc mapped mapped
  codec_measure_fixed_step 131 using hc
  simpa [copied455, copy455Mem, rcx, rsi, rdx, rax,
    BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_setWidth_of_le] using next

end SszX86.CodecMeasureFixed.Output
