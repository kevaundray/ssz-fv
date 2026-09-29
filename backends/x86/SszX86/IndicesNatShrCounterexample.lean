import SszX86.IndicesNatShrCounterexampleReturn

namespace SszX86.IndicesNatShr.Counterexample

open SszNative

/-- Only active Result/Nat fields are observed; all other output bytes are opaque. -/
def ReturnedSmall7 (t : MachineState) : Prop :=
  t.2 = 32768 ∧ t.1.regs.rsp = 16392 ∧
  Mem.loadInt t.1.dmem 4160#64 4 = some 0 ∧
  Mem.loadInt t.1.dmem 4096#64 8 = some 0 ∧
  Mem.loadInt t.1.dmem 4104#64 8 = some 7

/-- The full actual-entry certificate. Every premise concerns code or original
memory, and every path instruction through RET is executed. This is a standalone
shift-64 falsification, not a claim that a specialized caller supplies shift 64. -/
theorem actual_entry (e : Executable) (base : Int64) (hc : CodeAt e base)
    (m : DataMem) (hm : InitialMemory m) (flags : StatusFlags) :
    Eventually (step e) ReturnedSmall7 (initial m flags, base) := by
  apply entry_to117 e base hc m hm flags ReturnedSmall7
  intro flags
  apply scan_to192 e base hc m flags ReturnedSmall7
  intro flags
  apply small_to_return e base hc m hm flags ReturnedSmall7
  intro flags
  apply Eventually.done
  exact ⟨rfl, rfl, returned_tag m, returned_pointer m, returned_payload m⟩

/-- A concrete mapped original caller image witnesses the mismatch with the
shared unrestricted Nat model: machine Small 7, model Small 2. -/
theorem counterexample (e : Executable) (base : Int64) (hc : CodeAt e base)
    (flags : StatusFlags) :
    Eventually (step e) ReturnedSmall7 (initial (witnessMem ∅) flags, base) ∧
      NatShift.shr operand 64 0 0 0 =
        NatArithmetic.unchanged 0 (.ok (.small 2#64)) ∧
      NatShift.shr operand 64 0 0 0 ≠
        NatArithmetic.unchanged 0 (.ok (.small 7#64)) := by
  refine ⟨actual_entry e base hc _ (witness_initial ∅) flags, source_result, ?_⟩
  decide

theorem output_disagrees (t : MachineState) (h : ReturnedSmall7 t) :
    Mem.loadInt t.1.dmem 4104#64 8 ≠ some 2 := by
  rw [h.2.2.2.2]
  decide

end SszX86.IndicesNatShr.Counterexample
