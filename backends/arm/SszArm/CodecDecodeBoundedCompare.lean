import SszArm.CodecDecodeBoundedEntry
import SszNatABI

namespace SszArm.Codec.Decode.Bounded

open SszNative.NatABI

def branchOps : List Op := [.p56, .p60, .p64]

/-- Native Rust Ordering is a signed byte; the comparison consumes only that
byte, leaving arbitrary high return-register bits irrelevant. -/
theorem ordering_flags (order : Ordering) :
    (AddWithCarry ((orderingByte order).signExtend 32) (~~~1#32) 1#1).2.n =
      (AddWithCarry ((orderingByte order).signExtend 32) (~~~1#32) 1#1).2.v ↔ order = .gt := by
  cases order <;> decide

theorem ordering_branch (s : ArmState) (base : BitVec 64) (order : Ordering)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 56#64)
    (byte : (r (.GPR 0#5) s).setWidth 8 = orderingByte order) :
    let t := block base branchOps s
    run 3 s = t ∧
      read_pc t = base + BitVec.ofNat 64 (if order = .gt then 68 else 196) ∧
      t.mem = s.mem ∧ t.program = s.program ∧ read_err t = read_err s ∧
      (∀ reg : BitVec 5, reg ≠ 8#5 → r (.GPR reg) t = r (.GPR reg) s) ∧
      (∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s) := by
  have follows : Follows base branchOps s := by
    change r .PC s = _ at pc
    simp [branchOps, Follows, Op.row, Op.effect, put, next, compare32,
      state_simp_rules, pc, BitVec.add_assoc]
  refine ⟨block_run base branchOps s code error aligned follows, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [branchOps, block, Op.effect, put, next, compare32, state_simp_rules,
      byte, BitVec.setWidth_setWidth_of_le, ordering_flags, apply_ite]
  · simp [branchOps, block, Op.effect, put, next, compare32, state_simp_rules]
  · simp [branchOps, block]
  · simp [branchOps, block]
  · intro reg outside
    simp [branchOps, block, Op.effect, put, next, compare32, state_simp_rules, outside]
  · intro reg
    simp [branchOps, block, Op.effect, put, next, compare32, state_simp_rules]

end SszArm.Codec.Decode.Bounded
