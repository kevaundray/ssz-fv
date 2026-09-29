import SszX86.CodecMeasureFixedDecode
import SszX86.DispatchPush

namespace SszX86.CodecMeasureFixed
open BoolCodec UintCodec

abbrev savedMem := Dispatch.savedMem
abbrev savedState := Dispatch.savedState

macro "codec_measure_fixed_push " row:num ", " off:num " using " hc:term
    ", " hm:term : tactic => `(tactic|
  (codec_measure_fixed_step $row using $hc
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · have hm' := $hm
     apply SszX86.Dispatch.push_load (offset := $off)
     · repeat' first | exact hm' | apply Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

/-- The actual six pushes, at their original measure_fixed PCs. The saved-memory
image is shared with existing checked callees, but instruction fetches use this
routine's complete linked CodeAt, never another function's code assumption. -/
theorem pushes_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (next : Eventually (step e) P (savedState s, base + 10)) :
    Eventually (step e) P (s, base) := by
  have stackReg : s.regs.rsp - 8 - 8 - 8 - 8 - 8 - 8 = s.regs.rsp - 48 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  suffices run : Eventually (step e) P (s, base + 0) by
    simpa only [Int64.add_zero] using run
  codec_measure_fixed_push 0, 8 using hc, hm
  codec_measure_fixed_push 1, 16 using hc, hm
  codec_measure_fixed_push 2, 24 using hc, hm
  codec_measure_fixed_push 3, 32 using hc, hm
  codec_measure_fixed_push 4, 40 using hc, hm
  codec_measure_fixed_push 5, 48 using hc, hm
  simpa [savedState, savedMem, Dispatch.savedState, Dispatch.savedMem,
    Width.bytesv, BitVec.sub_sub, stackReg] using next

def allocatedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 88), rbx := s.regs.rdi}
    status := flags}

/-- The 88-byte local reservation follows the saves; RBX receives the original
hidden result pointer before any schema tag is observed. -/
theorem allocate_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (allocatedState s flags, base + 17)) :
    Eventually (step e) P (s, base + 10) := by
  codec_measure_fixed_step 6 using hc
  codec_measure_fixed_step 7 using hc
  simpa [allocatedState] using next _

end SszX86.CodecMeasureFixed
