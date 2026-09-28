import SszX86.NatMulWordNormalizeResult
import SszX86.NatMulWordOutput

namespace SszX86.NatMulWord

def resultPairState (s : MachineData) (a count low : BitVec 64) (flags : StatusFlags) : MachineData :=
  let payload := if count = 1#64 then low else count
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec payload
      rbx := UInt64.ofBitVec a
      rcx := UInt64.ofBitVec count
      rdx := UInt64.ofBitVec payload
      r14 := if count = 1#64 then 0 else s.regs.r14}
    status := flags}

/-- The original low product is reloaded from the actual spill slot before the
conditional canonical pair selection; the allocated buffer is not rewritten. -/
theorem result_normalize_publish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a count low : BitVec 64) (flags : StatusFlags)
    (lowLoad : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (low.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (resultPairState s a count low flags, base + 799)) :
    Eventually (step e) P (resultNormalizeState s a count flags, base + 773) := by
  unfold resultNormalizeState
  natmulword_step 6:10 using hc
  constructor <;> natmulword_step 6:11 using hc
  all_goals natmulword_step 6:12 using hc
  all_goals natmulword_load lowLoad
  all_goals natmulword_step 6:13 using hc
  all_goals natmulword_step 6:14 using hc
  all_goals natmulword_step 6:15 using hc
  all_goals natmulword_step 6:16 using hc
  all_goals
    by_cases one : count = 1#64
    · simpa [StatusFlags.from_result, one, resultPairState] using next _
    · simpa [StatusFlags.from_result, one, resultPairState] using next _

theorem result_normalize_zero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r14 := 0}, status := flags}, base + 799)) :
    Eventually (step e) P (s, base + 796) := by
  natmulword_step 6:17 using hc
  constructor <;> exact next _

theorem result_normalize_entry (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rax := 0}, status := flags}, base + 752)) :
    Eventually (step e) P (s, base + 741) := by
  natmulword_step 6:2 using hc
  constructor <;> natmulword_step 6:3 using hc
  all_goals exact next _

/-- Result pointer, payload and status are published through the original
shared scalar store block and then the real allocating-path epilogue. -/
theorem allocated_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec s.regs.r14.toBitVec s.regs.rax.toBitVec},
        base + 687)) :
    Eventually (step e) P (s, base + 799) := by
  natmulword_output 6:18 at 0 width 8 using hc mapped hm
  natmulword_step 6:19 using hc
  natmulword_output 3:11 at 8 width 8 using hc mapped hm
  natmulword_output 3:12 at 64 width 4 using hc mapped hm
  natmulword_step 3:13 using hc
  simpa [successMem, NatAdd.successMem, NatAdd.pairMem] using next

end SszX86.NatMulWord
