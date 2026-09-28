import SszX86.MeasureCore

namespace SszX86.Measure
open BoolCodec UintCodec

abbrev savedMem := Dispatch.savedMem
abbrev savedState := Dispatch.savedState

macro "measure_push " row:num ", " off:num " using " hc:term
    ", " hm:term : tactic => `(tactic|
  (measure_step $row using $hc
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · have hm' := $hm
     apply SszX86.Dispatch.push_load («offset» := $off)
     · repeat' first | exact hm' | apply Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

/-- Six real PUSH instructions, from the original private entry. -/
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
  measure_push 0, 8 using hc, hm
  measure_push 1, 16 using hc, hm
  measure_push 2, 24 using hc, hm
  measure_push 3, 32 using hc, hm
  measure_push 4, 40 using hc, hm
  measure_push 5, 48 using hc, hm
  simpa [Dispatch.savedState, Dispatch.savedMem, Width.bytesv, BitVec.sub_sub, stackReg]
    using next

end SszX86.Measure
