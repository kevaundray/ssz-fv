import SszArm.BitVectorLeafFrame

namespace SszArm.BitVector

open Delimited (MemoryFrame)

def narrowEntry (c : ArmState) (base : BitVec 64) : ArmState :=
  called .narrow (Stages.CallPreparation.narrow.result c base) base

theorem narrow_arguments {s c : ArmState} {length : SszNative.NatOperand}
    (base : BitVec 64) (current : Working s c length) :
    r (.GPR 0#5) (narrowEntry c base) = r (.GPR 31#5) s + 144#64 ∧
      r (.GPR 1#5) (narrowEntry c base) = length.pointer ∧
      r (.GPR 2#5) (narrowEntry c base) = length.payload := by
  constructor
  · simp (config := {decide := true}) [narrowEntry, called, Stages.CallPreparation.result,
      state_simp_rules, current.sp]
  constructor
  · simp (config := {decide := true}) [narrowEntry, called, Stages.CallPreparation.result,
      state_simp_rules, current.pointer]
  · simp (config := {decide := true}) [narrowEntry, called, Stages.CallPreparation.result,
      state_simp_rules, current.payload]

/-- Narrow the original length descriptor only after scope and padding. The
proof executes the complete helper scan; no representability premise is used. -/
theorem narrowing_executes {s c : ArmState} {length : SszNative.NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (base : BitVec 64)
    (owned : Owned s length data) (current : Counted s c length remainder)
    (before : MemoryFrame (writesFor s (outcome s length data)) s c)
    (code : JointCodeAt c base) (aligned : CheckSPAlignment s)
    (pc : read_pc c = base + 6576#64) :
    ∃ fuel t, run fuel c = t ∧ NatToU128.Post (narrowEntry c base) t length ∧
      Counted s t length remainder ∧ JointCodeAt t base ∧ read_pc t = base + 6592#64 ∧
      MemoryFrame (localWrites s) c t := by
  have args := narrow_arguments base current.toWorking
  have prepared := Stages.prepare .narrow c base code.body current.error
    (current.toWorking.aligned aligned) pc
  have preparedCurrent := current.after_preparation .narrow base (Or.inr (Or.inr rfl))
  have entryCurrent : Counted s (narrowEntry c base) length remainder :=
    preparedCurrent.after_call .narrow base
  have initial : MemoryFrame (localWrites s) c (narrowEntry c base) := by
    apply frame_of_memory
    simp only [narrowEntry, called, Stages.CallPreparation.result, state_simp_rules]
  have allBefore := before.trans ((local_covered s (outcome s length data)).frame initial)
  have helperOwned := narrow_owned owned allBefore args.1 entryCurrent.sp args.2.1 args.2.2
  have preparedCode : JointCodeAt (Stages.CallPreparation.narrow.result c base) base := by
    rw [← prepared]
    exact code.run _
  have preparedPC : read_pc (Stages.CallPreparation.narrow.result c base) = base + 6588#64 := by
    simp only [Stages.CallPreparation.result, Stages.CallPreparation.stop, state_simp_rules]
  obtain ⟨fuel, t, execution, post⟩ := narrow_call (Stages.CallPreparation.narrow.result c base) base
    length preparedCode preparedCurrent.error (preparedCurrent.toWorking.aligned aligned)
    preparedPC helperOwned
  have whole : run (Stages.CallPreparation.narrow.ops.length + fuel) c = t := by
    rw [run_plus, prepared, execution]
  have cover := (leaf_locals_covered owned 32 (by decide) args.1 entryCurrent.sp).trans
    (narrow_writes_local (narrowEntry c base) length)
  refine ⟨_, t, whole, post, entryCurrent.after_return post.returned, ?_, ?_,
    initial.trans (cover.frame post.frame)⟩
  · rw [← whole]
    exact code.run _
  · have returned := post.returned.pc
    simpa (config := {decide := true}) only
      [narrowEntry, called, CallSite.offset, state_simp_rules, BitVec.ofNat_eq_ofNat] using returned

end SszArm.BitVector
