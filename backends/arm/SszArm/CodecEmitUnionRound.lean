import SszArm.CodecEmitCompareCall
import SszArm.CodecEmitUnionScanOps

namespace SszArm.Codec.Emit.Union.Scan

open UintCodec (widthLoad)
open SszArm.Emit.Activation (next put)
open SszArm.Emit.Dispatch (branch)

@[simp] theorem prepared_program (s : ArmState) : (prepared s).program = s.program := by
  simp [prepared, prepareOps, block, Op.effect, next, put, branch, state_simp_rules]

@[simp] theorem prepared_error (s : ArmState) : read_err (prepared s) = read_err s := by
  simp [prepared, prepareOps, block, Op.effect, next, put, branch, state_simp_rules]

@[simp] theorem prepared_stack (s : ArmState) : r (.GPR 31#5) (prepared s) = r (.GPR 31#5) s := by
  simp [prepared, prepareOps, block, Op.effect, next, put, branch, state_simp_rules]

@[simp] theorem checked_program (s : ArmState) : (checked s).program = s.program := by
  simp [checked, checkOps, block, Op.effect, next, put, branch, state_simp_rules]

@[simp] theorem checked_error (s : ArmState) : read_err (checked s) = read_err s := by
  simp [checked, checkOps, block, Op.effect, next, put, branch, state_simp_rules]

@[simp] theorem checked_stack (s : ArmState) : r (.GPR 31#5) (checked s) = r (.GPR 31#5) s := by
  simp [checked, checkOps, block, Op.effect, next, put, branch, state_simp_rules]

structure Round (s t : ArmState) (bias : BitVec 64) (left right : Nat) : Prop where
  pc : read_pc t = bias + (if left = right then 2296452#64 else 2296416#64)
  error : read_err t = .None
  program : t.program = s.program
  stack : r (.GPR 31#5) t = r (.GPR 31#5) s
  cursor : r (.GPR 26#5) t = r (.GPR 26#5) s + 24#64
  remaining : r (.GPR 27#5) t = r (.GPR 27#5) s - 24#64
  preserved : ∀ reg : BitVec 5, reg ∈ [18#5, 19#5, 20#5, 21#5, 22#5, 23#5, 24#5, 25#5, 28#5, 29#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  frame : Delimited.MemoryFrame (Stack.envelope (r (.GPR 31#5) s).toNat 16) s t

theorem round_correct (s : ArmState) (bias : BitVec 64) (left right : Nat)
    (code : Linked.CodeAt s bias) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = bias + 2296416#64)
    (nonempty : r (.GPR 27#5) s ≠ 0#64)
    (lhs : SszNative.NatMemory.Pair (widthLoad s)
      (read_mem_bytes 8 (r (.GPR 26#5) s + 32#64) s)
      (read_mem_bytes 8 (r (.GPR 26#5) s + 40#64) s) left)
    (rhs : SszNative.NatMemory.Pair (widthLoad s) (r (.GPR 23#5) s) (r (.GPR 24#5) s) right)
    (leftOwned : NatCompare.Owned s
      (read_mem_bytes 8 (r (.GPR 26#5) s + 32#64) s)
      (read_mem_bytes 8 (r (.GPR 26#5) s + 40#64) s))
    (rightOwned : NatCompare.Owned s (r (.GPR 23#5) s) (r (.GPR 24#5) s)) :
    ∃ fuel t, run fuel s = t ∧ Round s t bias left right := by
  have start : read_pc s = (bias + 2294780#64) + 1636#64 := by
    simpa only [BitVec.add_assoc, BitVec.ofNat_add_ofNat] using pc
  have first := prepared_run s _ code.emit error start nonempty
  have args := prepared_arguments s
  have preparedCode := code.congr (prepared_program s)
  have preparedAligned : CheckSPAlignment (prepared s) := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, prepared_stack] using aligned
  have preparePC : read_pc (prepared s) = bias + 2296432#64 := by
    simpa only [BitVec.add_assoc, BitVec.ofNat_add_ofNat] using prepared_pc s _ start nonempty
  have prepareLhs : SszNative.NatMemory.Pair (widthLoad (prepared s))
      (r (.GPR 0#5) (prepared s)) (r (.GPR 1#5) (prepared s)) left := by
    rw [args.1, args.2.1]
    rw [SszArm.Emit.load_eq_of_mem_eq (prepared_memory s)]
    exact lhs
  have prepareRhs : SszNative.NatMemory.Pair (widthLoad (prepared s))
      (r (.GPR 2#5) (prepared s)) (r (.GPR 3#5) (prepared s)) right := by
    rw [args.2.2.1, args.2.2.2]
    rw [SszArm.Emit.load_eq_of_mem_eq (prepared_memory s)]
    exact rhs
  have prepareLeftOwned : NatCompare.Owned (prepared s)
      (r (.GPR 0#5) (prepared s)) (r (.GPR 1#5) (prepared s)) := by
    simpa only [NatCompare.Owned, args.1, args.2.1, prepared_stack] using leftOwned
  have prepareRightOwned : NatCompare.Owned (prepared s)
      (r (.GPR 2#5) (prepared s)) (r (.GPR 3#5) (prepared s)) := by
    simpa only [NatCompare.Owned, args.2.2.1, args.2.2.2, prepared_stack] using rightOwned
  obtain ⟨fuel, middle, helper, post⟩ := compare_call (prepared s) bias left right
    preparedCode ((prepared_error s).trans error) preparedAligned preparePC
    prepareLhs prepareRhs prepareLeftOwned prepareRightOwned
  have finalPC : read_pc middle = (bias + 2294780#64) + 1656#64 := by
    simpa only [BitVec.add_assoc, BitVec.ofNat_add_ofNat] using post.pc
  have last := checked_run middle _ (preparedCode.congr post.program).emit post.error finalPC
  refine ⟨4 + (fuel + 4), checked middle, ?_, ?_⟩
  · rw [run_plus, first, run_plus, helper, last]
  · refine ⟨?_, by simpa using post.error, by simp [post.program],
      by simpa using post.stack, ?_, ?_, ?_, ?_, ?_⟩
    · rw [checked_pc middle _ finalPC, post.ordering]
      cases order : compare left right with
      | eq =>
        have same := Nat.compare_eq_eq.mp order
        simp [order, same, SszNative.NatABI.orderingByte, BitVec.add_assoc]
      | lt =>
        have different : left ≠ right := by have := Nat.compare_eq_lt.mp order; omega
        simp [order, different, SszNative.NatABI.orderingByte, BitVec.add_assoc]
      | gt =>
        have different : left ≠ right := by have := Nat.compare_eq_gt.mp order; omega
        simp [order, different, SszNative.NatABI.orderingByte, BitVec.add_assoc]
    · rw [(checked_cursor middle).1, post.registers 26#5 (by decide)]
      simp [prepared, prepareOps, block, Op.effect, next, put, branch, state_simp_rules]
    · rw [(checked_cursor middle).2, post.registers 27#5 (by decide)]
      simp [prepared, prepareOps, block, Op.effect, next, put, branch, state_simp_rules]
    · intro reg member
      simp only [List.mem_cons, List.mem_singleton] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp [checked, checkOps, block, Op.effect, next, put, branch, state_simp_rules,
          post.registers _ (by decide), prepared, prepareOps]
    · intro reg
      simp [checked, checkOps, block, Op.effect, next, put, branch, state_simp_rules,
        post.vectors, prepared, prepareOps]
    · intro address outside
      rw [checked_memory, post.frame address]
      · exact congrFun (prepared_memory s) address
      · simpa only [prepared_stack] using outside

end SszArm.Codec.Emit.Union.Scan
