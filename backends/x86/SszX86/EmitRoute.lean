import SszX86.EmitSelect

namespace SszX86.Emit
open SszNative.Serialize

def routed (s : MachineData) (base : Int64) (kind : TableKind) : MachineData :=
  jumped (indexedState (descriptorCompared s) kind) base kind

theorem AtBody.routed {s t : MachineData} (h : AtBody s t) (base : Int64) (kind : TableKind) :
    AtBody s (routed t base kind) := (h.compared.indexed kind).jumped base kind

theorem select_table (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (kind : TableKind) (P : MachineState → Prop)
    (nonzero : s.regs.rax.toBitVec ≠ 0#64)
    (notOne : s.regs.rax.toBitVec.take 32 ≠ 1#32)
    (tag : s.regs.rcx = UInt64.ofNat (kind.index + 2))
    (table : TableAt s.dmem base)
    (next : Eventually (step e) P (routed s base kind, base + Int64.ofNat kind.entry)) :
    Eventually (step e) P (s, base + 32) := by
  apply select_other e base hc s P nonzero notOne
  apply value_index_runs e base hc (descriptorCompared s) kind P tag
  apply jump_runs e base hc (indexedState (descriptorCompared s) kind) kind P rfl table
  exact next

/-- Actual table selection, with both tag facts justified by the logical shape. -/
theorem dispatch_table_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (original s : MachineData) (desc : Desc) (value : Value) (kind : TableKind)
    (anchors : AtBody original s)
    (descriptor : s.regs.rax.toBitVec = BitVec.ofNat 64 (descTag desc))
    (valueKind : s.regs.rcx.toBitVec = BitVec.ofNat 64 (valueTag value))
    (table : TableAt s.dmem base)
    (nonScalar : 2 ≤ descTag desc) (bounded : descTag desc < 2 ^ 32)
    (index : valueTag value = kind.index + 2)
    (entry : bodyEntry desc = kind.entry) :
    Eventually (step e) (EntryPost original base desc value) (s, base + 32) := by
  have nonzero : s.regs.rax.toBitVec ≠ 0#64 := by
    rw [descriptor]
    intro equal
    have same := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat] at same
    omega
  have notOne : s.regs.rax.toBitVec.take 32 ≠ 1#32 := by
    rw [descriptor]
    cases desc <;> simp only [descTag] at nonScalar ⊢
    all_goals first | omega | decide
  have tag : s.regs.rcx = UInt64.ofNat (kind.index + 2) := by
    apply UInt64.toBitVec_inj.1
    simpa only [index, UInt64.toBitVec_ofNat'] using valueKind
  apply select_table e base hc s kind _ nonzero notOne tag table
  apply Eventually.done
  refine ⟨?_, anchors.routed base kind, descriptor, ?_⟩
  · rw [entry]
  · intro small
    omega

end SszX86.Emit
