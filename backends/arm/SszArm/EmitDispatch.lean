import SszArm.EmitDispatchOps

namespace SszArm.Emit

open SszNative.Serialize (Desc Value)

/-- Compatibility is derived from logical measurement, not an entry premise. -/
def Compatible : Desc → Value → Prop
  | .bool, .bool _ | .uint _, .uint _
  | .byteVector _, .bytes _ | .byteList _, .bytes _
  | .bitVector _, .bits _ | .bitList _, .bits _ | .progressiveBitList _, .bits _ => True
  | _, _ => False

theorem compatible_of_expected {desc : Desc} {value : Value} {size : Nat}
    (expected : SszNative.Serialize.expectedSize desc value = .ok size) :
    Compatible desc value := by
  cases desc <;> cases value <;>
    simp_all only [Compatible, SszNative.Serialize.expectedSize]
  all_goals cases expected

def dispatchOps : Desc → List Dispatch.Op
  | .bool => [.p48]
  | .uint _ => [.p48, .p52, .p56]
  | .byteVector _ | .byteList _ => [.p48, .p52, .p56, .p544, .p548, .p552, .p556]
  | .bitVector _ | .bitList _ | .progressiveBitList _ =>
    [.p48, .p52, .p56, .p544, .p548, .p552, .p556, .p560, .p564]

def bodyEntry : Desc → Nat
  | .bool => 344 | .uint _ => 60
  | .byteVector _ | .byteList _ => 820
  | .bitVector _ | .bitList _ | .progressiveBitList _ => 568

@[irreducible] def selected (s : ArmState) (desc : Desc) : ArmState :=
  Dispatch.block (dispatchOps desc) s

theorem dispatch_follows (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (compatible : Compatible desc value)
    (pc : read_pc s = base + 48#64)
    (tag : r (.GPR 8#5) s = descriptorTag desc)
    (valueTag : r (.GPR 9#5) s = (Emit.valueTag value).setWidth 64) :
    Dispatch.Follows base (dispatchOps desc) s := by
  change r .PC s = base + 48#64 at pc
  cases desc <;> cases value <;> simp only [Compatible] at compatible
  all_goals try contradiction
  all_goals
    simp (config := {decide := true, instances := true})
      [dispatchOps, Dispatch.Follows, Dispatch.Op.row, Dispatch.Op.effect,
       Dispatch.branch, Dispatch.compare64, Dispatch.compare32, Dispatch.next,
       Dispatch.greater, state_simp_rules, bitvec_rules, minimal_theory,
       pc, tag, valueTag, descriptorTag, Emit.valueTag, BitVec.add_assoc]

theorem selected_run (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (compatible : Compatible desc value) (code : CodeAt s base)
    (error : read_err s = .None) (pc : read_pc s = base + 48#64)
    (tag : r (.GPR 8#5) s = descriptorTag desc)
    (valueTag : r (.GPR 9#5) s = (Emit.valueTag value).setWidth 64) :
    run (dispatchOps desc).length s = selected s desc := by
  rw [selected]
  exact Dispatch.runs _ s base code error (dispatch_follows s base desc value compatible pc tag valueTag)

theorem selected_pc (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (compatible : Compatible desc value) (pc : read_pc s = base + 48#64)
    (tag : r (.GPR 8#5) s = descriptorTag desc)
    (valueTag : r (.GPR 9#5) s = (Emit.valueTag value).setWidth 64) :
    read_pc (selected s desc) = base + BitVec.ofNat 64 (bodyEntry desc) := by
  change r .PC s = base + 48#64 at pc
  cases desc <;> cases value <;> simp only [Compatible] at compatible
  all_goals try contradiction
  all_goals
    simp (config := {decide := true, instances := true})
      [selected, Dispatch.block, dispatchOps, bodyEntry, Dispatch.Op.effect,
       Dispatch.branch, Dispatch.compare64, Dispatch.compare32, Dispatch.next,
       Dispatch.greater, state_simp_rules, bitvec_rules, minimal_theory,
       pc, tag, valueTag, descriptorTag, Emit.valueTag, BitVec.add_assoc]

@[simp] theorem selected_program (s : ArmState) (desc : Desc) :
    (selected s desc).program = s.program := by rw [selected, Dispatch.block_program]

@[simp] theorem selected_error (s : ArmState) (desc : Desc) :
    read_err (selected s desc) = read_err s := by rw [selected, Dispatch.block_error]

@[simp] theorem selected_memory (s : ArmState) (desc : Desc) :
    (selected s desc).mem = s.mem := by rw [selected, Dispatch.block_memory]

@[simp] theorem selected_register (s : ArmState) (desc : Desc) (reg : BitVec 5) :
    r (.GPR reg) (selected s desc) = r (.GPR reg) s := by rw [selected, Dispatch.block_register]

@[simp] theorem selected_vector (s : ArmState) (desc : Desc) (reg : BitVec 5) :
    r (.SFP reg) (selected s desc) = r (.SFP reg) s := by rw [selected, Dispatch.block_vector]

theorem selected_aligned (s : ArmState) (desc : Desc) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (selected s desc) := by
  simpa only [CheckSPAlignment, state_simp_rules, selected_register] using aligned

theorem selected_bodyRegisters {s : ArmState} {args : Args} (desc : Desc)
    (registers : BodyRegisters s args) : BodyRegisters (selected s desc) args := by
  rcases registers with ⟨result, output, capacity, value, stack⟩
  exact ⟨(selected_register _ _ _).trans result, (selected_register _ _ _).trans output,
    (selected_register _ _ _).trans capacity, (selected_register _ _ _).trans value,
    (selected_register _ _ _).trans stack⟩

end SszArm.Emit
