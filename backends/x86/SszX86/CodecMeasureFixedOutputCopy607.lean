import SszX86.CodecMeasureFixedOutputCopyMemory

namespace SszX86.CodecMeasureFixed.Output
open BoolCodec UintCodec Serialize.Publish

def copied607 (s : MachineData) (v : Image) : MachineData :=
  {s with regs := {s.regs with
    rcx := UInt64.ofBitVec (v.padding.setWidth 64)
    rdx := UInt64.ofBitVec v.w3},
    dmem := copy607Mem s.dmem s.regs.rbx.toBitVec v}

theorem copy607_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (v : Image)
    (image : ImageAt s.dmem s.regs.rsp.toBitVec v)
    (apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rbx.toBitVec 72 72)
    (mapped : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (r14 : s.regs.r14.toBitVec = v.w0) (r15 : s.regs.r15.toBitVec = v.w1)
    (rax : s.regs.rax.toBitVec = v.tag.setWidth 64)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (copied607 s v, base + 694)) :
    Eventually (step e) P (s, base + 607) := by
  codec_fixed_output_read 154 using hc word image.w7
  codec_fixed_output_store 155 at 56 width 8 using hc mapped mapped
  codec_fixed_output_read 156 using hc word image.w6
  codec_fixed_output_store 157 at 48 width 8 using hc mapped mapped
  codec_fixed_output_read 158 using hc word image.w5
  codec_fixed_output_store 159 at 40 width 8 using hc mapped mapped
  codec_fixed_output_read 160 using hc word image.w4
  codec_fixed_output_store 161 at 32 width 8 using hc mapped mapped
  codec_fixed_output_read 162 using hc word image.w2
  codec_fixed_output_read 163 using hc word image.w3
  codec_fixed_output_store 164 at 24 width 8 using hc mapped mapped
  codec_fixed_output_store 165 at 16 width 8 using hc mapped mapped
  codec_fixed_output_read 166 using hc word image.padding
  codec_fixed_output_store 167 at 0 width 8 using hc mapped mapped
  codec_fixed_output_store 168 at 8 width 8 using hc mapped mapped
  codec_fixed_output_store 169 at 64 width 4 using hc mapped mapped
  codec_fixed_output_store 170 at 68 width 4 using hc mapped mapped
  codec_measure_fixed_step 171 using hc
  simpa [copied607, copy607Mem, r14, r15, rax,
    BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_setWidth_of_le] using next

end SszX86.CodecMeasureFixed.Output
