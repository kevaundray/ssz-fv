import SszArm.MeasureEntryOps

namespace SszArm.Measure

open SszNative.Serialize (Desc)

def dispatchOps : Desc → List Dispatch.Op
  | .bool => [.p44, .p48, .p328, .p332, .p336]
  | .uint _ | .byteVector _ => [.p44, .p48, .p328, .p332, .p336, .p340, .p344]
  | .byteList _ => [.p44, .p48, .p328, .p332, .p552, .p556]
  | .bitVector _ | .bitList _ => [.p44, .p48, .p328, .p332, .p552, .p556, .p560, .p564]
  | .progressiveBitList _ => [.p44, .p48, .p52, .p56, .p60, .p444, .p448]

def bodyEntry : Desc → Nat
  | .bool => 760
  | .uint _ => 348
  | .byteVector _ => 1156
  | .byteList _ => 776
  | .bitVector _ => 568
  | .bitList _ => 1248
  | .progressiveBitList _ => 684

@[irreducible] def selected (s : ArmState) (desc : Desc) : ArmState :=
  Dispatch.block (dispatchOps desc) s

theorem dispatch_follows (s : ArmState) (base : BitVec 64) (desc : Desc)
    (pc : read_pc s = base + 44#64)
    (tag : r (.GPR 9#5) s = Emit.descriptorTag desc) :
    Dispatch.Follows base (dispatchOps desc) s := by
  change r .PC s = base + 44#64 at pc
  cases desc <;>
    simp (config := {decide := true, instances := true})
      [dispatchOps, Dispatch.Follows, Dispatch.Op.row, Dispatch.Op.effect,
       Emit.Dispatch.branch, Emit.Dispatch.compare64, Emit.Dispatch.next,
       Emit.Dispatch.greater, Activation.put, Activation.next,
       state_simp_rules, bitvec_rules, minimal_theory,
       pc, tag, Emit.descriptorTag, BitVec.add_assoc]

theorem selected_run (s : ArmState) (base : BitVec 64) (desc : Desc)
    (code : CodeAt s base) (error : read_err s = .None) (pc : read_pc s = base + 44#64)
    (tag : r (.GPR 9#5) s = Emit.descriptorTag desc) :
    run (dispatchOps desc).length s = selected s desc := by
  rw [selected]
  exact Dispatch.runs _ s base code error (dispatch_follows s base desc pc tag)

theorem selected_pc (s : ArmState) (base : BitVec 64) (desc : Desc)
    (pc : read_pc s = base + 44#64)
    (tag : r (.GPR 9#5) s = Emit.descriptorTag desc) :
    read_pc (selected s desc) = base + BitVec.ofNat 64 (bodyEntry desc) := by
  change r .PC s = base + 44#64 at pc
  cases desc <;>
    simp (config := {decide := true, instances := true})
      [selected, Dispatch.block, dispatchOps, bodyEntry, Dispatch.Op.effect,
       Emit.Dispatch.branch, Emit.Dispatch.compare64, Emit.Dispatch.next,
       Emit.Dispatch.greater, Activation.put, Activation.next,
       state_simp_rules, bitvec_rules, minimal_theory,
       pc, tag, Emit.descriptorTag, BitVec.add_assoc]

/-- The primitive decision tree executes no composite call frontier. Its path
is independent of the value kind and of both retained-plan flag values. -/
theorem dispatch_no_frontier (desc : Desc) (op : Dispatch.Op) (member : op ∈ dispatchOps desc) :
    op.row.1 ∉ frontiers := by
  cases op <;> decide

theorem bodyEntry_no_frontier (desc : Desc) : bodyEntry desc ∉ frontiers := by
  cases desc <;> simp only [bodyEntry, frontiers] <;> decide

@[simp] theorem selected_program (s : ArmState) (desc : Desc) :
    (selected s desc).program = s.program := by rw [selected, Dispatch.block_program]

@[simp] theorem selected_error (s : ArmState) (desc : Desc) :
    read_err (selected s desc) = read_err s := by rw [selected, Dispatch.block_error]

@[simp] theorem selected_memory (s : ArmState) (desc : Desc) :
    (selected s desc).mem = s.mem := by rw [selected, Dispatch.block_memory]

@[simp] theorem selected_register (s : ArmState) (desc : Desc) (reg : BitVec 5)
    (untouched : reg ≠ 22#5) :
    r (.GPR reg) (selected s desc) = r (.GPR reg) s := by
  rw [selected, Dispatch.block_register _ _ _ untouched]

@[simp] theorem selected_vector (s : ArmState) (desc : Desc) (reg : BitVec 5) :
    r (.SFP reg) (selected s desc) = r (.SFP reg) s := by rw [selected, Dispatch.block_vector]

theorem selected_aligned (s : ArmState) (desc : Desc) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (selected s desc) := by
  simpa only [CheckSPAlignment, state_simp_rules,
    selected_register s desc 31#5 (by decide)] using aligned

theorem selected_bodyRegisters {s : ArmState} {args : Args} (desc : Desc)
    (registers : BodyRegisters s args) : BodyRegisters (selected s desc) args := by
  rcases registers with ⟨result, arena, value, stack⟩
  exact ⟨(selected_register _ _ _ (by decide)).trans result,
    (selected_register _ _ _ (by decide)).trans arena,
    (selected_register _ _ _ (by decide)).trans value,
    (selected_register _ _ _ (by decide)).trans stack⟩

end SszArm.Measure
