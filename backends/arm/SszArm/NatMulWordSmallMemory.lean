import SszArm.NatMulWordSmallModel

namespace SszArm.NatMulWord

open UintCodec (widthLoad)
open Delimited (MemoryFrame Protected Returned)

 theorem small_value_protected {s t : ArmState} (abi : SmallABI s t)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand)
    (value : SszNative.NatOperand) (success : result.result = .ok value)
    (address bytes : Nat) (protection : Protected (localWrites s result) address bytes) :
    Protected (valueWrites t) address bytes := by
  rcases protection with empty | apart
  · exact Or.inl empty
  · right
    have work := apart ((r (.GPR 31#5) s).toNat - 48, 48) (small_stack_local s result)
    have output := apart ((r (.GPR 0#5) s).toNat, 16) (by simp [localWrites, success])
    have status := apart ((r (.GPR 0#5) s).toNat + 64, 4) (by simp [localWrites, success])
    intro span member
    simp only [valueWrites, NatAdd.valueWrites, abi.out, abi.sp,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp only [Prod.fst, Prod.snd] at * <;> omega

 theorem small_value_frame {s t u : ArmState} (abi : SmallABI s t)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand)
    (value : SszNative.NatOperand) (success : result.result = .ok value)
    (frame : MemoryFrame (valueWrites t) t u) : MemoryFrame (writesFor s result) t u := by
  intro a outside
  have localOutside := fun span member => outside span (small_local_writes s result span member)
  have work := localOutside ((r (.GPR 31#5) s).toNat - 48, 48) (small_stack_local s result)
  have output := localOutside ((r (.GPR 0#5) s).toNat, 16) (by simp [localWrites, success])
  have status := localOutside ((r (.GPR 0#5) s).toNat + 64, 4) (by simp [localWrites, success])
  apply frame a
  intro span member
  simp only [valueWrites, NatAdd.valueWrites, abi.out, abi.sp,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp only [Prod.fst, Prod.snd] at * <;> omega

 theorem small_error_frame {s t u : ArmState} (abi : SmallABI s t)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand)
    (failure : SszNative.NatArithmetic.Failure) (failed : result.result = .error failure)
    (frame : MemoryFrame (errorWrites t) t u) : MemoryFrame (writesFor s result) t u := by
  intro a outside
  have localOutside := fun span member => outside span (small_local_writes s result span member)
  have work := localOutside ((r (.GPR 31#5) s).toNat - 48, 48) (small_stack_local s result)
  have output := localOutside ((r (.GPR 0#5) s).toNat, 68) (by simp [localWrites, failed])
  apply frame a
  intro span member
  simp only [errorWrites, NatAdd.localWrites, abi.out, abi.sp,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp only [Prod.fst, Prod.snd] at * <;> omega

 theorem small_error_finish (s u : ArmState) (base factor : BitVec 64)
    (operand : SszNative.NatOperand) (owned : Owned s operand factor)
    (priorFrame : SmallFrame s u) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc u = base + 1264#64)
    (model : outcome s operand factor =
      SszNative.NatArithmetic.unchanged (arenaOf s).used (.error .scratchExhausted)) :
    run 50 u = errorResult .scratch base u ∧ Post s (errorResult .scratch base u) operand factor := by
  have returned := error_run_contract .scratch u base (priorFrame.code code)
    (priorFrame.error.trans error) (priorFrame.aligned aligned) pc
    (priorFrame.return_owned owned.return_owned)
  refine ⟨returned.1, small_unchanged_post s _ operand factor owned _ model
    (priorFrame.returned returned.2.1) ?_ ?_⟩
  · simpa only [priorFrame.out] using returned.2.2.1
  · exact (priorFrame.full _).trans (small_error_frame priorFrame.toSmallABI owned.stackBound _ _
      (by rw [model]; rfl) returned.2.2.2)

 theorem small_narrow_finish (s u : ArmState) (base factor word : BitVec 64)
    (operand : SszNative.NatOperand) (owned : Owned s operand factor)
    (priorFrame : SmallFrame s u) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc u = base + 1048#64)
    (low : r (.GPR 8#5) u = word)
    (model : outcome s operand factor =
      SszNative.NatArithmetic.unchanged (arenaOf s).used (.ok (.small word))) :
    run 21 u = valueResult .small base u ∧ Post s (valueResult .small base u) operand factor := by
  have returned := value_run_contract .small u base (priorFrame.code code)
    (priorFrame.error.trans error) (priorFrame.aligned aligned) pc
    (priorFrame.return_owned owned.return_owned) (.small word) rfl low trivial trivial
  refine ⟨returned.1, small_unchanged_post s _ operand factor owned _ model
    (priorFrame.returned returned.2.1) ?_ ?_⟩
  · simpa only [priorFrame.out] using returned.2.2.1
  · exact (priorFrame.full _).trans (small_value_frame priorFrame.toSmallABI owned.stackBound _ _
      (by rw [model]; rfl) returned.2.2.2)

end SszArm.NatMulWord
