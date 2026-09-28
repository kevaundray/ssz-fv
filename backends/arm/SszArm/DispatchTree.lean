import SszArm.DispatchBlocks

namespace SszArm.Dispatch

open Block

/-- Includes the descriptor LDR and arena MOV, rather than assuming an internal
register tag or selecting a post-branch PC as an entry premise. -/
def Kind.ops : Kind → List Op
  | .bool => [.p28, .p32, .p36, .p40, .p128, .p132, .p136]
  | .uint | .byteVector => [.p28, .p32, .p36, .p40, .p128, .p132, .p136, .p140, .p144]
  | .byteList => [.p28, .p32, .p36, .p40, .p128, .p132, .p412, .p416]
  | .bitVector | .bitList => [.p28, .p32, .p36, .p40, .p128, .p132, .p412, .p416, .p420, .p424]
  | .progressiveBitList => [.p28, .p32, .p36, .p40, .p44, .p48, .p228, .p232]

def selected (s : ArmState) (kind : Kind) : ArmState := Block.effect kind.ops s

@[simp] theorem selected_program (s : ArmState) (kind : Kind) :
    (selected s kind).program = s.program := by
  cases kind <;> simp [selected, Kind.ops, Block.effect]

@[simp] theorem selected_error (s : ArmState) (kind : Kind) :
    read_err (selected s kind) = read_err s := by
  cases kind <;> simp [selected, Kind.ops, Block.effect]

@[simp] theorem selected_memory (s : ArmState) (kind : Kind) :
    (selected s kind).mem = s.mem := by
  cases kind <;> simp [selected, Kind.ops, Block.effect, Op.effect, branch, put, next,
    Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem selected_reg (s : ArmState) (kind : Kind) (reg : BitVec 5)
    (notTag : reg ≠ 8#5) (notArena : reg ≠ 19#5) :
    r (.GPR reg) (selected s kind) = r (.GPR reg) s := by
  cases kind <;> simp [selected, Kind.ops, Block.effect, Op.effect, branch, put, next,
    Udivti3.compare, Udivti3.next, notTag, notArena, state_simp_rules]

@[simp] theorem selected_arena (s : ArmState) (kind : Kind) :
    r (.GPR 19#5) (selected s kind) = r (.GPR 4#5) s := by
  cases kind <;> simp [selected, Kind.ops, Block.effect, Op.effect, branch, put, next,
    Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem selected_vector (s : ArmState) (kind : Kind) (reg : BitVec 5) :
    r (.SFP reg) (selected s kind) = r (.SFP reg) s := by
  cases kind <;> simp [selected, Kind.ops, Block.effect, Op.effect, branch, put, next,
    Udivti3.compare, Udivti3.next, state_simp_rules]

theorem selected_aligned (s : ArmState) (kind : Kind) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (selected s kind) :=
  CheckSPAlignment_of_r_sp_eq (selected_reg s kind 31#5 (by decide) (by decide)) aligned

theorem selected_pc (s : ArmState) (base : BitVec 64) (kind : Kind)
    (pc : read_pc s = base + 28#64)
    (tag : read_mem_bytes 8 (r (.GPR 1#5) s) s = kind.tag) :
    read_pc (selected s kind) = base + BitVec.ofNat 64 kind.entry := by
  change r .PC s = base + 28#64 at pc
  cases kind <;>
    simp (config := {decide := true}) [selected, Kind.ops, Kind.tag, Kind.entry,
      Block.effect, Op.effect, branch, greater, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, tag, pc, BitVec.add_assoc]

/-- Literal conditional branches establish the exact accepted primitive entry. -/
theorem selected_run (s : ArmState) (base : BitVec 64) (kind : Kind)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 28#64)
    (tag : read_mem_bytes 8 (r (.GPR 1#5) s) s = kind.tag) :
    run kind.ops.length s = selected s kind := by
  apply Block.runs kind.ops s base code error
  change r .PC s = base + 28#64 at pc
  cases kind <;>
    simp (config := {decide := true}) [Kind.ops, Kind.tag, Follows, Op.row,
      Op.effect, branch, greater, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, aligned, tag, pc, BitVec.add_assoc]

end SszArm.Dispatch
