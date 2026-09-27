import SszX86.DelimitedCore

namespace SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- A RET pops the incoming return slot and does not write it. -/
def retState (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8)}}

theorem ret_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hp : P (retState s, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 232) ∧
    Eventually (step e) P (s, base + 662) ∧
    Eventually (step e) P (s, base + 840) := by
  refine ⟨?_, ?_, ?_⟩
  · delimited_step 52 using hc
    simp only [MachineData.load, Effects.All, hr, ofBytes_wordBytes]
    exact Eventually.done _ hp
  · delimited_step 149 using hc
    simp only [MachineData.load, Effects.All, hr, ofBytes_wordBytes]
    exact Eventually.done _ hp
  · delimited_step 183 using hc
    simp only [MachineData.load, Effects.All, hr, ofBytes_wordBytes]
    exact Eventually.done _ hp
end SszX86.Delimited
