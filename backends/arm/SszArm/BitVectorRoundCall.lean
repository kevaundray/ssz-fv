import SszArm.BitVectorArena
import SszArm.BitVectorExpectedPair
import SszArm.BitVectorRoundOwned

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

def roundEntry (c : ArmState) (base : BitVec 64) : ArmState :=
  called .round (Stages.CallPreparation.round.result c base) base

theorem round_arguments {s c : ArmState} {length quotient : SszNative.NatOperand}
    {data : Ssz.Bytes} (base : BitVec 64) (owned : Owned s length data)
    (current : Working s c length)
    (pair : SszNative.NatArithmetic.operandAt (widthLoad c)
      (r (.GPR 31#5) s + 48#64).toNat quotient)
    (arena : ArenaAt s c (outcome s length data).divided.used)
    (arenaRegister : r (.GPR 19#5) c = r (.GPR 19#5) s) :
    RoundArguments s (roundEntry c base) length quotient := by
  have pointer : read_mem_bytes 8 (r (.GPR 31#5) s + 48#64) c = quotient.pointer := by
    simpa only [BitVec.add_zero] using read_of_observe_offset c
      (r (.GPR 31#5) s + 48#64) 0 8 quotient.pointer
      (by simpa only [Nat.add_zero] using pair.1)
  have payload : read_mem_bytes 8 (r (.GPR 31#5) s + 56#64) c = quotient.payload := by
    simpa only [BitVec.add_assoc, show 48#64 + 8#64 = 56#64 by decide] using
      read_of_observe_offset c (r (.GPR 31#5) s + 48#64) 8 8 quotient.payload pair.2.1
  have observe : widthLoad (roundEntry c base) = widthLoad c := by
    funext address bytes
    simp only [widthLoad, roundEntry, called, Stages.CallPreparation.result, state_simp_rules]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) [roundEntry, called, Stages.CallPreparation.result,
      state_simp_rules, current.sp]
  · simp (config := {decide := true}) [roundEntry, called, Stages.CallPreparation.result,
      state_simp_rules, current.sp, pointer]
  · simp (config := {decide := true}) [roundEntry, called, Stages.CallPreparation.result,
      state_simp_rules, current.sp, payload]
  · simp (config := {decide := true}) [roundEntry, called, Stages.CallPreparation.result,
      state_simp_rules, SszNative.NatOperand.pointer]
  · simp (config := {decide := true}) [roundEntry, called, Stages.CallPreparation.result,
      state_simp_rules, SszNative.NatOperand.payload]
  · simp (config := {decide := true}) [roundEntry, called, Stages.CallPreparation.result,
      state_simp_rules, arenaRegister]
  · simp (config := {decide := true}) [roundEntry, called, Stages.CallPreparation.result,
      state_simp_rules, current.sp]
  · rw [observe]
    exact pair.2.2
  · simp (config := {decide := true}) [NatAdd.arenaOf, roundEntry, called,
      Stages.CallPreparation.result, state_simp_rules, arenaRegister,
      arena.base, arena.capacity, arena.cursor, arenaOf, outcome, divided_eq]

/-- The optional add is entered from the actual pair-copy frontier. Neither its
allocation success nor its return object is an execution precondition. -/
theorem rounding_executes {s c : ArmState} {length quotient : SszNative.NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (base : BitVec 64)
    (owned : Owned s length data) (current : Counted s c length remainder)
    (pair : SszNative.NatArithmetic.operandAt (widthLoad c)
      (r (.GPR 31#5) s + 48#64).toNat quotient)
    (arena : ArenaAt s c (outcome s length data).divided.used)
    (arenaRegister : r (.GPR 19#5) c = r (.GPR 19#5) s)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0) (code : JointCodeAt c base)
    (aligned : CheckSPAlignment s) (pc : read_pc c = base + 3392#64) :
    ∃ fuel t, run fuel c = t ∧ NatAdd.Post (roundEntry c base) t quotient (.small 1) ∧
      Counted s t length remainder ∧ JointCodeAt t base ∧ read_pc t = base + 3416#64 ∧
      MemoryFrame (writesFor s (outcome s length data)) c t := by
  have args := round_arguments base owned current.toWorking pair arena arenaRegister
  have prepared := Stages.prepare .round c base code.body current.error
    (current.toWorking.aligned aligned) pc
  have preparedCurrent := current.after_preparation .round base (Or.inl rfl)
  have preparedCode : JointCodeAt (Stages.CallPreparation.round.result c base) base := by
    rw [← prepared]
    exact code.run _
  have preparedPC : read_pc (Stages.CallPreparation.round.result c base) = base + 3412#64 := by
    simp only [Stages.CallPreparation.result, Stages.CallPreparation.stop, state_simp_rules]
  obtain ⟨fuel, t, execution, post⟩ := round_call (Stages.CallPreparation.round.result c base) base
    quotient preparedCode preparedCurrent.error (preparedCurrent.toWorking.aligned aligned)
    preparedPC (round_owned owned args division nonzero)
  have whole : run (Stages.CallPreparation.round.ops.length + fuel) c = t := by
    rw [run_plus, prepared, execution]
  have entryCurrent : Counted s (roundEntry c base) length remainder :=
    preparedCurrent.after_call .round base
  have initial : MemoryFrame (writesFor s (outcome s length data)) c (roundEntry c base) := by
    apply frame_of_memory
    simp only [roundEntry, called, Stages.CallPreparation.result, state_simp_rules]
  refine ⟨_, t, whole, post, entryCurrent.after_return post.returned, ?_, ?_,
    initial.trans ((round_writes owned args division nonzero).frame post.frame)⟩
  · rw [← whole]
    exact code.run _
  · have returned := post.returned.pc
    simpa (config := {decide := true}) only
      [roundEntry, called, CallSite.offset, state_simp_rules, BitVec.ofNat_eq_ofNat] using returned

end SszArm.BitVector
