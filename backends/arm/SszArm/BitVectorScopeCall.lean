import SszArm.BitVectorLeafFrame
import SszArm.BitVectorPair

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

def scopeEntry (c : ArmState) (base : BitVec 64) : ArmState :=
  called .scope (Stages.CallPreparation.scope.result c base) base

theorem scope_arguments {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (base : BitVec 64) (owned : Owned s length data) (current : Working s c length) :
    r (.GPR 0#5) (scopeEntry c base) = r (.GPR 31#5) s + 144#64 ∧
      r (.GPR 1#5) (scopeEntry c base) = r (.GPR 31#5) s + 48#64 ∧
      r (.GPR 2#5) (scopeEntry c base) = BitVec.ofNat 64 data.size := by
  have size : r (.GPR 3#5) s = BitVec.ofNat 64 data.size := by
    rw [← owned.length]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  constructor
  · simp (config := {decide := true}) [scopeEntry, called, Stages.CallPreparation.result,
      state_simp_rules, current.sp]
  constructor
  · simp (config := {decide := true}) [scopeEntry, called, Stages.CallPreparation.result,
      state_simp_rules, current.sp]
  · simp (config := {decide := true}) [scopeEntry, called, Stages.CallPreparation.result,
      state_simp_rules, current.size, size]

/-- Scope runs before every padding read and before the representability helper.
Its exact success or complete failure object comes from the leaf's actual RET. -/
theorem scope_executes {s c : ArmState} {length expected : SszNative.NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (base : BitVec 64)
    (owned : Owned s length data) (current : Counted s c length remainder)
    (pair : SszNative.NatArithmetic.operandAt (widthLoad c)
      (r (.GPR 31#5) s + 48#64).toNat expected)
    (limbs : NatDivision.OperandOwned (localWrites s) expected)
    (code : JointCodeAt c base) (aligned : CheckSPAlignment s)
    (pc : read_pc c = base + 5948#64) :
    ∃ fuel t, run fuel c = t ∧ NatExact.Post (scopeEntry c base) t expected ∧
      Counted s t length remainder ∧ JointCodeAt t base ∧ read_pc t = base + 5964#64 ∧
      MemoryFrame (localWrites s) c t := by
  have args := scope_arguments base owned current.toWorking
  have prepared := Stages.prepare .scope c base code.body current.error
    (current.toWorking.aligned aligned) pc
  have preparedCurrent := current.after_preparation .scope base (Or.inr (Or.inl rfl))
  have entryCurrent : Counted s (scopeEntry c base) length remainder :=
    preparedCurrent.after_call .scope base
  have entryPair : SszNative.NatArithmetic.operandAt (widthLoad (scopeEntry c base))
      (r (.GPR 1#5) (scopeEntry c base)).toNat expected := by
    rw [args.2.1]
    simpa only [scopeEntry, call_observe, preparation_observe] using pair
  have helperOwned := exact_owned owned args.1 entryCurrent.sp args.2.1 entryPair limbs
  have preparedCode : JointCodeAt (Stages.CallPreparation.scope.result c base) base := by
    rw [← prepared]
    exact code.run _
  have preparedPC : read_pc (Stages.CallPreparation.scope.result c base) = base + 5960#64 := by
    simp only [Stages.CallPreparation.result, Stages.CallPreparation.stop, state_simp_rules]
  obtain ⟨fuel, t, execution, post⟩ := scope_call (Stages.CallPreparation.scope.result c base) base
    expected preparedCode preparedCurrent.error (preparedCurrent.toWorking.aligned aligned)
    preparedPC helperOwned
  have whole : run (Stages.CallPreparation.scope.ops.length + fuel) c = t := by
    rw [run_plus, prepared, execution]
  have initial : MemoryFrame (localWrites s) c (scopeEntry c base) := by
    apply frame_of_memory
    simp only [scopeEntry, called, Stages.CallPreparation.result, state_simp_rules]
  have cover := (leaf_locals_covered owned 68 (by decide) args.1 entryCurrent.sp).trans
    (exact_writes_local (scopeEntry c base) expected)
  refine ⟨_, t, whole, post, entryCurrent.after_return post.returned, ?_, ?_,
    initial.trans (cover.frame post.frame)⟩
  · rw [← whole]
    exact code.run _
  · have returned := post.returned.pc
    simpa (config := {decide := true}) only
      [scopeEntry, called, CallSite.offset, state_simp_rules, BitVec.ofNat_eq_ofNat] using returned

end SszArm.BitVector
