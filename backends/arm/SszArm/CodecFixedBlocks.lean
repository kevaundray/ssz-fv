import SszArm.CodecFixedFrame
import SszCodecTypes

namespace SszArm.Codec.Fixed.IsFixed

open Dispatch.Block (next put save branch greater)
open SszNative.Codec (DescTag)

def PCs (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      PCs base ops (op.effect s)

theorem PCs.follows {base : BitVec 64} {ops : List Op} {s : ArmState}
    (pcs : PCs base ops s) (aligned : CheckSPAlignment s) : Follows base ops s := by
  induction ops generalizing s with
  | nil => trivial
  | cons op ops ih => exact ⟨aligned, pcs.1, ih pcs.2 (op.aligned s aligned)⟩

theorem run_block (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pcs : PCs base ops s) : run ops.length s = block ops s :=
  block_run ops s base code error (pcs.follows aligned)

def tagWord : DescTag → BitVec 64
  | .bool => 0 | .uint => 1 | .byteVector => 2 | .byteList => 3
  | .bitVector => 4 | .bitList => 5 | .progressiveBitList => 6
  | .vector => 7 | .list => 8 | .progressiveList => 9
  | .container => 10 | .progressiveContainer => 11 | .compatibleUnion => 12

/-- All thirteen tag destinations; neither malformed metadata nor validation
is consulted by the native structural dispatch. -/
def dispatchOps : DescTag → List Op
  | .vector => [.p12, .p16, .p20]
  | .bool | .uint | .byteVector => [.p12, .p16, .p20, .p40, .p44, .p48]
  | .byteList => [.p12, .p16, .p20, .p40, .p44, .p48, .p52]
  | .bitVector => [.p12, .p16, .p20, .p40, .p44, .p56, .p60]
  | .container => [.p12, .p16, .p20, .p40, .p44, .p56, .p60, .p64, .p68]
  | _ => [.p12, .p16, .p20, .p40, .p44, .p56, .p60, .p64, .p68, .p72, .p76]

def dispatchTarget : DescTag → BitVec 64
  | .vector => 24
  | .bool | .uint | .byteVector | .bitVector => 188
  | .container => 88
  | .progressiveContainer => 80
  | _ => 172

theorem dispatch_pcs (s : ArmState) (base : BitVec 64) (tag : DescTag)
    (pc : read_pc s = base + 12#64)
    (stored : read_mem_bytes 8 (r (.GPR 0#5) s) s = tagWord tag) :
    PCs base (dispatchOps tag) s := by
  change r .PC s = _ at pc
  cases tag <;>
    simp (config := {decide := true}) [dispatchOps, PCs, Op.row, Op.effect,
      next, put, branch, greater, Udivti3.compare, Udivti3.next,
      state_simp_rules, stored, tagWord, pc, BitVec.add_assoc, AddWithCarry,
      bitvec_rules, minimal_theory]

theorem dispatch_pc (s : ArmState) (base : BitVec 64) (tag : DescTag)
    (pc : read_pc s = base + 12#64)
    (stored : read_mem_bytes 8 (r (.GPR 0#5) s) s = tagWord tag) :
    read_pc (block (dispatchOps tag) s) = base + dispatchTarget tag := by
  change r .PC s = _ at pc
  cases tag <;>
    simp (config := {decide := true}) [dispatchOps, dispatchTarget, block, Op.effect,
      next, put, branch, greater, Udivti3.compare, Udivti3.next,
      state_simp_rules, stored, tagWord, pc, BitVec.add_assoc, AddWithCarry,
      bitvec_rules, minimal_theory]

theorem dispatch_memory (s : ArmState) (tag : DescTag) :
    (block (dispatchOps tag) s).mem = s.mem := by
  cases tag <;> simp [dispatchOps, block, Op.effect, next, put, branch,
    Udivti3.compare, Udivti3.next, state_simp_rules]

theorem dispatch_register (s : ArmState) (tag : DescTag) (reg : BitVec 5)
    (notTag : reg ≠ 8#5) : r (.GPR reg) (block (dispatchOps tag) s) = r (.GPR reg) s := by
  cases tag <;> simp [dispatchOps, block, Op.effect, next, put, branch,
    Udivti3.compare, Udivti3.next, state_simp_rules, notTag]

/-- Dispatch executes from the post-prologue PC, not from an assumed selected
branch. The descriptor tag is loaded by p12 before any comparison. -/
theorem dispatch_run (s : ArmState) (base : BitVec 64) (tag : DescTag)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 12#64)
    (stored : read_mem_bytes 8 (r (.GPR 0#5) s) s = tagWord tag) :
    run (dispatchOps tag).length s = block (dispatchOps tag) s :=
  run_block _ _ _ code error aligned (dispatch_pcs s base tag pc stored)

end SszArm.Codec.Fixed.IsFixed
