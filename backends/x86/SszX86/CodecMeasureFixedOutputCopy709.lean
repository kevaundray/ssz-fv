import SszX86.CodecMeasureFixedOutputCopyMemory

namespace SszX86.CodecMeasureFixed.Output
open BoolCodec UintCodec Serialize.Publish

def copied709 (s : MachineData) (v : Image) : MachineData :=
  {s with regs := {s.regs with
    rsi := UInt64.ofBitVec (v.padding.setWidth 64)
    rdi := UInt64.ofBitVec v.w4},
    dmem := copy455Mem s.dmem s.regs.rbx.toBitVec v}

theorem copy709_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (v : Image)
    (image : ImageAt s.dmem s.regs.rsp.toBitVec v)
    (apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rbx.toBitVec 72 72)
    (mapped : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (rdx : s.regs.rdx.toBitVec = v.w0) (rcx : s.regs.rcx.toBitVec = v.w1)
    (r8 : s.regs.r8.toBitVec = v.w2)
    (rax : s.regs.rax.toBitVec = v.tag.setWidth 64)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (copied709 s v, base + 694)) :
    Eventually (step e) P (s, base + 709) := by
  codec_fixed_output_read 182 using hc word image.w7
  codec_fixed_output_store 183 at 56 width 8 using hc mapped mapped
  codec_fixed_output_read 184 using hc word image.w6
  codec_fixed_output_store 185 at 48 width 8 using hc mapped mapped
  codec_fixed_output_read 186 using hc word image.w5
  codec_fixed_output_store 187 at 40 width 8 using hc mapped mapped
  codec_fixed_output_read 188 using hc word image.w3
  codec_fixed_output_read 189 using hc word image.w4
  codec_fixed_output_store 190 at 32 width 8 using hc mapped mapped
  codec_fixed_output_store 191 at 24 width 8 using hc mapped mapped
  codec_fixed_output_read 192 using hc word image.padding
  codec_fixed_output_store 193 at 8 width 8 using hc mapped mapped
  codec_fixed_output_store 194 at 16 width 8 using hc mapped mapped
  codec_fixed_output_store 195 at 0 width 8 using hc mapped mapped
  codec_fixed_output_store 196 at 64 width 4 using hc mapped mapped
  codec_fixed_output_store 197 at 68 width 4 using hc mapped mapped
  codec_measure_fixed_step 198 using hc
  simpa [copied709, copy455Mem, rdx, rcx, r8, rax,
    BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_setWidth_of_le] using next

end SszX86.CodecMeasureFixed.Output
