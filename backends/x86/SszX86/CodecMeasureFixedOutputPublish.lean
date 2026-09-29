import SszX86.CodecMeasureFixedCore
import SszX86.SerializePublishMemory

namespace SszX86.CodecMeasureFixed.Output
open BoolCodec UintCodec

macro "codec_fixed_output_store " row:num " at " off:num " width " count:num
    " using " hc:term:max " mapped " hm:term:max : tactic => do
  let obtainLoad ← if off.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 72) (byteCount := $count))
  else
    `(tactic| apply Large.mapped_load (capacity := 72) («offset» := $off) («width» := $count))
  `(tactic|
    (codec_measure_fixed_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $obtainLoad
       · have mappingBase := $hm
         repeat' first | apply Large.mapped_store | assumption
       · decide
     simp only [Effects.All]))

def someMem (s : MachineData) : DataMem :=
  let out := s.regs.rbx.toBitVec
  let m := Mem.storeInt s.dmem (out + 8#64) 8 s.regs.r14.toBitVec.toInt
  let m := Mem.storeInt m (out + 16#64) 8 s.regs.r15.toBitVec.toInt
  let m := Mem.storeInt m out 8 1
  Mem.storeInt m (out + 64#64) 4 0

def noneMem (s : MachineData) : DataMem :=
  Mem.storeInt (Mem.storeInt s.dmem s.regs.rbx.toBitVec 8 0)
    (s.regs.rbx.toBitVec + 64#64) 4 0

def publishedSome (s : MachineData) : MachineData := {s with dmem := someMem s}
def publishedNone (s : MachineData) : MachineData := {s with dmem := noneMem s}

/-- Some writes only its active Nat pair, discriminator, and status. -/
theorem some_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (publishedSome s, base + 694)) :
    Eventually (step e) P (s, base + 271) := by
  codec_fixed_output_store 70 at 8 width 8 using hc mapped mapped
  codec_fixed_output_store 71 at 16 width 8 using hc mapped mapped
  codec_fixed_output_store 72 at 0 width 8 using hc mapped mapped
  codec_measure_fixed_step 73 using hc
  codec_fixed_output_store 173 at 64 width 4 using hc mapped mapped
  simpa only [publishedSome, someMem, show (1#64).toInt = 1 by decide,
    show (0#32).toInt = 0 by decide] using next

/-- None leaves every inactive payload byte untouched. -/
theorem none_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (publishedNone s, base + 694)) :
    Eventually (step e) P (s, base + 680) := by
  codec_fixed_output_store 172 at 0 width 8 using hc mapped mapped
  codec_fixed_output_store 173 at 64 width 4 using hc mapped mapped
  simpa only [publishedNone, noneMem, show (0#64).toInt = 0 by decide,
    show (0#32).toInt = 0 by decide] using next

end SszX86.CodecMeasureFixed.Output
