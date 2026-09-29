import SszX86.CodecMeasureChildDecode
import SszX86.MeasurePush

namespace SszX86.CodecMeasureChild
open BoolCodec UintCodec

macro "codec_measure_child_push " row:num ", " off:num " using " code:term
    ", " mapped:term : tactic => `(tactic|
  (codec_measure_child_step $row using $code
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · have available := $mapped
     apply SszX86.Dispatch.push_load («offset» := $off)
     · repeat' first | exact available | apply Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

def stackState (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 168)},
    status := memcpySubFlags s.regs.rsp.toBitVec 168}

def bodyState (s : MachineData) : MachineData :=
  let stacked := stackState (Dispatch.savedState s)
  {stacked with regs := {stacked.regs with r14 := s.regs.rcx,
    r13 := s.regs.rsi, rbx := s.regs.rdi}}

/-- The child closure's six saves and its 168-byte local frame are actual
instructions; recursive helper scratch is separately owned below this frame. -/
theorem setup_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (next : Eventually (step e) P (bodyState s, base + 26)) :
    Eventually (step e) P (s, base) := by
  have stackReg : s.regs.rsp - 8 - 8 - 8 - 8 - 8 - 8 = s.regs.rsp - 48 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  suffices run : Eventually (step e) P (s, base + 0) by
    simpa only [Int64.add_zero] using run
  codec_measure_child_push 0, 8 using code, mapped
  codec_measure_child_push 1, 16 using code, mapped
  codec_measure_child_push 2, 24 using code, mapped
  codec_measure_child_push 3, 32 using code, mapped
  codec_measure_child_push 4, 40 using code, mapped
  codec_measure_child_push 5, 48 using code, mapped
  codec_measure_child_step 6 using code
  codec_measure_child_step 7 using code
  codec_measure_child_step 8 using code
  codec_measure_child_step 9 using code
  simpa [bodyState, stackState, Dispatch.savedState, Dispatch.savedMem,
    memcpySubFlags, Width.bytesv, BitVec.sub_sub, stackReg, BitVec.take, BitVec.signed]
    using next

theorem bodyState_sp (s : MachineData) :
    (bodyState s).regs.rsp.toBitVec = s.regs.rsp.toBitVec - 216 := by
  simp only [bodyState, stackState, Dispatch.savedState, UInt64.toBitVec_ofBitVec]
  bv_omega

theorem bodyState_memory (s : MachineData) :
    (bodyState s).dmem = Dispatch.savedMem s := rfl

end SszX86.CodecMeasureChild
