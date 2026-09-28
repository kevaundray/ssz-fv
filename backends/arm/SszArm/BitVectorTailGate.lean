import SszArm.BitVectorBlocks

namespace SszArm.BitVector.TailGate

open Block

def sizeBranch : Op := ⟨6000, 0xb4001214#32,
  .BR (.Compare_branch { sf := 1, op := 0, imm19 := 144, Rt := 20 }), by rfl, by decide⟩
def remainderBranch : Op := ⟨6004, 0xb40011f9#32,
  .BR (.Compare_branch { sf := 1, op := 0, imm19 := 143, Rt := 25 }), by rfl, by decide⟩

def ops (s : ArmState) : List Op :=
  if r (.GPR 20#5) s = 0#64 then [sizeBranch] else [sizeBranch, remainderBranch]

@[irreducible] def result (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (if r (.GPR 20#5) s = 0#64 then base + 6576#64
    else if r (.GPR 25#5) s = 0#64 then base + 6576#64 else base + 6008#64) s

private theorem follows (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (pc : read_pc s = base + 6000#64) :
    Follows base (ops s) s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  by_cases empty : r (.GPR 20#5) s = 0#64
  all_goals
    simp (config := {decide := true, instances := true})
      [ops, empty, Follows, sizeBranch, remainderBranch, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, error, pc, BitVec.add_assoc]

private theorem summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 6000#64) : effect (ops s) s = result s base := by
  change r .PC s = _ at pc
  by_cases empty : r (.GPR 20#5) s = 0#64
  all_goals
    simp (config := {decide := true, instances := true})
      [ops, empty, effect, result, sizeBranch, remainderBranch, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, pc, BitVec.add_assoc]

/-- Empty input never loads a tail byte. A zero division remainder also bypasses
that load, exactly as the native control-flow graph requires. -/
theorem executes (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (error : read_err s = .None) (pc : read_pc s = base + 6000#64) :
    run (ops s).length s = result s base := by
  rw [runs (ops s) s base code (follows s base error pc), summary s base pc]

end SszArm.BitVector.TailGate
