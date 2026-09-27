import SszX86.NatAddOutput

namespace SszX86.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Small overflow publishes the newly allocated two-word slice after both
limbs and the cursor have already been committed by the reservation block. -/
theorem overflow_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec 2}, base + 612)) :
    Eventually (step e) P (s, base + 750) := by
  natadd_output 201 at 0 width 8 using hc mapped hm
  natadd_output 202 at 8 width 8 using hc mapped hm
  natadd_step 203 using hc
  natadd_output 157 at 64 width 4 using hc mapped hm
  simpa [successMem, pairMem] using next

end SszX86.NatAdd
