import SszX86.CodecMeasureFixedOutputPublish

namespace SszX86.CodecMeasureFixed.Output
open BoolCodec UintCodec
open Serialize.Publish

/-- Native error copy PC344 uses this exact store order. -/
def copy344Mem (m : DataMem) (out : BitVec 64) (v : Image) : DataMem :=
  let m := Mem.storeInt m (out + 56#64) 8 v.w7.toInt
  let m := Mem.storeInt m (out + 48#64) 8 v.w6.toInt
  let m := Mem.storeInt m (out + 40#64) 8 v.w5.toInt
  let m := Mem.storeInt m (out + 32#64) 8 v.w4.toInt
  let m := Mem.storeInt m (out + 24#64) 8 v.w3.toInt
  let m := Mem.storeInt m (out + 0#64) 8 v.w0.toInt
  let m := Mem.storeInt m (out + 8#64) 8 v.w1.toInt
  let m := Mem.storeInt m (out + 16#64) 8 v.w2.toInt
  let m := Mem.storeInt m (out + 64#64) 4 v.tag.toInt
  Mem.storeInt m (out + 68#64) 4 v.padding.toInt

/-- PC455 and PC709 have the same store order despite different registers. -/
def copy455Mem (m : DataMem) (out : BitVec 64) (v : Image) : DataMem :=
  let m := Mem.storeInt m (out + 56#64) 8 v.w7.toInt
  let m := Mem.storeInt m (out + 48#64) 8 v.w6.toInt
  let m := Mem.storeInt m (out + 40#64) 8 v.w5.toInt
  let m := Mem.storeInt m (out + 32#64) 8 v.w4.toInt
  let m := Mem.storeInt m (out + 24#64) 8 v.w3.toInt
  let m := Mem.storeInt m (out + 8#64) 8 v.w1.toInt
  let m := Mem.storeInt m (out + 16#64) 8 v.w2.toInt
  let m := Mem.storeInt m (out + 0#64) 8 v.w0.toInt
  let m := Mem.storeInt m (out + 64#64) 4 v.tag.toInt
  Mem.storeInt m (out + 68#64) 4 v.padding.toInt

def copy607Mem (m : DataMem) (out : BitVec 64) (v : Image) : DataMem :=
  let m := Mem.storeInt m (out + 56#64) 8 v.w7.toInt
  let m := Mem.storeInt m (out + 48#64) 8 v.w6.toInt
  let m := Mem.storeInt m (out + 40#64) 8 v.w5.toInt
  let m := Mem.storeInt m (out + 32#64) 8 v.w4.toInt
  let m := Mem.storeInt m (out + 24#64) 8 v.w3.toInt
  let m := Mem.storeInt m (out + 16#64) 8 v.w2.toInt
  let m := Mem.storeInt m (out + 0#64) 8 v.w0.toInt
  let m := Mem.storeInt m (out + 8#64) 8 v.w1.toInt
  let m := Mem.storeInt m (out + 64#64) 4 v.tag.toInt
  Mem.storeInt m (out + 68#64) 4 v.padding.toInt

macro "codec_fixed_output_read " row:num " using " hc:term " word " hl:term : tactic => `(tactic|
  (codec_measure_fixed_step $row using $hc
   simp (disch := first | assumption | omega | decide)
     [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_assoc,
      Serialize.Publish.remote_read (srcCount := 72) (dstCount := 72),
      ($hl), Delimited.word_cast]))

end SszX86.CodecMeasureFixed.Output
