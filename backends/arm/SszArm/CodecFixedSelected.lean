import SszArm.CodecFixedBlocks

namespace SszArm.Codec.Fixed.IsFixed

open Dispatch.Block (next put save branch greater)
open SszNative.Codec (DescTag)

def selectedOps (tag : DescTag) : List Op := (dispatchOps tag).drop 3

def selectedEntry : DescTag → BitVec 64
  | .vector => 24
  | _ => 40

theorem selected_pcs (s : ArmState) (base : BitVec 64) (tag : DescTag)
    (pc : read_pc s = base + selectedEntry tag)
    (loaded : r (.GPR 8#5) s = tagWord tag) : PCs base (selectedOps tag) s := by
  change r .PC s = _ at pc
  cases tag <;>
    simp (config := {decide := true}) [selectedOps, selectedEntry, dispatchOps,
      PCs, Op.row, Op.effect, next, put, branch, greater, Udivti3.compare,
      Udivti3.next, state_simp_rules, loaded, tagWord, pc, BitVec.add_assoc,
      AddWithCarry, bitvec_rules, minimal_theory]

theorem selected_pc (s : ArmState) (base : BitVec 64) (tag : DescTag)
    (pc : read_pc s = base + selectedEntry tag)
    (loaded : r (.GPR 8#5) s = tagWord tag) :
    read_pc (block (selectedOps tag) s) = base + dispatchTarget tag := by
  change r .PC s = _ at pc
  cases tag <;>
    simp (config := {decide := true}) [selectedOps, selectedEntry, dispatchOps,
      dispatchTarget, block, Op.effect, next, put, branch, greater, Udivti3.compare,
      Udivti3.next, state_simp_rules, loaded, tagWord, pc, BitVec.add_assoc,
      AddWithCarry, bitvec_rules, minimal_theory]

theorem selected_memory (s : ArmState) (tag : DescTag) :
    (block (selectedOps tag) s).mem = s.mem := by
  cases tag <;> simp [selectedOps, dispatchOps, block, Op.effect, next, put, branch,
    Udivti3.compare, Udivti3.next, state_simp_rules]

theorem selected_register (s : ArmState) (tag : DescTag) (reg : BitVec 5) :
    r (.GPR reg) (block (selectedOps tag) s) = r (.GPR reg) s := by
  cases tag <;> simp [selectedOps, dispatchOps, block, Op.effect, next, put, branch,
    Udivti3.compare, Udivti3.next, state_simp_rules]

theorem selected_run (s : ArmState) (base : BitVec 64) (tag : DescTag)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + selectedEntry tag)
    (loaded : r (.GPR 8#5) s = tagWord tag) :
    run (selectedOps tag).length s = block (selectedOps tag) s :=
  run_block _ _ _ code error aligned (selected_pcs s base tag pc loaded)

/-- The optimized vector loop loads one child pointer and its tag. It never
allocates a second activation, regardless of the logical vector length. -/
def vectorOps : List Op := [.p24, .p28, .p32, .p36]

theorem vector_pcs (s : ArmState) (base child : BitVec 64) (tag : DescTag)
    (pc : read_pc s = base + 24#64)
    (pointer : read_mem_bytes 8 (r (.GPR 0#5) s + 24#64) s = child)
    (stored : read_mem_bytes 8 child s = tagWord tag) : PCs base vectorOps s := by
  change r .PC s = _ at pc
  cases tag <;> simp (config := {decide := true}) [vectorOps, PCs, Op.row, Op.effect,
    next, put, branch, Udivti3.compare, Udivti3.next, state_simp_rules, pointer,
    stored, tagWord, pc, BitVec.add_assoc, AddWithCarry, bitvec_rules, minimal_theory]

theorem vector_pc (s : ArmState) (base child : BitVec 64) (tag : DescTag)
    (pc : read_pc s = base + 24#64)
    (pointer : read_mem_bytes 8 (r (.GPR 0#5) s + 24#64) s = child)
    (stored : read_mem_bytes 8 child s = tagWord tag) :
    read_pc (block vectorOps s) = base + selectedEntry tag := by
  change r .PC s = _ at pc
  cases tag <;> simp (config := {decide := true}) [vectorOps, selectedEntry, block, Op.effect,
    next, put, branch, Udivti3.compare, Udivti3.next, state_simp_rules, pointer,
    stored, tagWord, pc, BitVec.add_assoc, AddWithCarry, bitvec_rules, minimal_theory]

theorem vector_arguments (s : ArmState) (child : BitVec 64) (tag : DescTag)
    (pointer : read_mem_bytes 8 (r (.GPR 0#5) s + 24#64) s = child)
    (stored : read_mem_bytes 8 child s = tagWord tag) :
    r (.GPR 0#5) (block vectorOps s) = child ∧
    r (.GPR 8#5) (block vectorOps s) = tagWord tag := by
  simp [vectorOps, block, Op.effect, next, put, branch, Udivti3.compare,
    Udivti3.next, state_simp_rules, pointer, stored]

theorem vector_memory (s : ArmState) : (block vectorOps s).mem = s.mem := by
  simp [vectorOps, block, Op.effect, next, put, branch, Udivti3.compare,
    Udivti3.next, state_simp_rules]

theorem vector_register (s : ArmState) (reg : BitVec 5) (h0 : reg ≠ 0#5) (h8 : reg ≠ 8#5) :
    r (.GPR reg) (block vectorOps s) = r (.GPR reg) s := by
  simp [vectorOps, block, Op.effect, next, put, branch, Udivti3.compare,
    Udivti3.next, state_simp_rules, h0, h8]

theorem vector_run (s : ArmState) (base child : BitVec 64) (tag : DescTag)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 24#64)
    (pointer : read_mem_bytes 8 (r (.GPR 0#5) s + 24#64) s = child)
    (stored : read_mem_bytes 8 child s = tagWord tag) : run 4 s = block vectorOps s :=
  run_block vectorOps s base code error aligned (vector_pcs s base child tag pc pointer stored)

end SszArm.Codec.Fixed.IsFixed
