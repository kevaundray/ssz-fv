import SszArm.BitVectorStageState
import SszArm.BitVectorPair
import SszArm.BitVectorCopySpace
import SszArm.BitVectorLeafOwned

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- The first semantic frontier includes the real entry, arbitrary division
scan, nested __udivti3, RET, status load, and exact quotient-pair save. -/
theorem entry_checks_division (s : ArmState) (base : BitVec 64)
    (length : SszNative.NatOperand) (data : Ssz.Bytes)
    (owned : Owned s length data) (code : JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 428#64) :
    ∃ fuel d, run fuel s = Block.divisionStatusResult d base ∧
      NatDivision.Post (divisionEntry s base) d length ∧ Working s d length ∧
      Working s (Block.divisionStatusResult d base) length ∧
      JointCodeAt (Block.divisionStatusResult d base) base ∧
      MemoryFrame (writesFor s (outcome s length data)) s (Block.divisionStatusResult d base) := by
  obtain ⟨fuel, d, execution, post, nextCode, nextPC⟩ :=
    entry_divides s base length data owned code error aligned pc
  have current := (working_division_entry s base length data owned error).after_return post.returned
  have status := Block.division_status_run d base nextCode.body current.error
    (current.aligned aligned) nextPC
  have whole : run (fuel + 5) s = Block.divisionStatusResult d base := by
    rw [run_plus, execution, status]
  have initial : MemoryFrame (writesFor s (outcome s length data)) s (divisionEntry s base) :=
    frame_of_memory (division_arguments s base length data owned).memory
  have divided := (division_writes s base length data owned).frame post.frame
  have saved := (local_covered s (outcome s length data)).frame (division_status_frame owned current base)
  refine ⟨fuel + 5, d, whole, post, current, current.after_status base, ?_,
    (initial.trans divided).trans saved⟩
  rw [← whole]
  exact code.run _

/-- Success is read from the actual helper object, not hypothesized as an
architectural branch. The copied pair retains its arbitrary Large limbs. -/
theorem division_status_success {s d : ArmState} {base : BitVec 64}
    {length quotient : SszNative.NatOperand} {data : Ssz.Bytes} {remainder : BitVec 64}
    (owned : Owned s length data) (current : Working s d length)
    (post : NatDivision.Post (divisionEntry s base) d length)
    (success : (outcome s length data).divided.result = .ok (quotient, remainder)) :
    Counted s (Block.divisionStatusResult d base) length remainder ∧
      read_pc (Block.divisionStatusResult d base) = base + 3380#64 ∧
      SszNative.NatArithmetic.operandAt (widthLoad (Block.divisionStatusResult d base))
        (r (.GPR 31#5) s + 64#64).toNat quotient := by
  have args := division_arguments s base length data owned
  have stored := post.result
  rw [division_outcome s base length data owned, success, args.out] at stored
  change SszNative.NatArithmetic.operandAt (widthLoad d)
      (r (.GPR 31#5) s + 144#64).toNat quotient ∧
    widthLoad d ((r (.GPR 31#5) s + 144#64).toNat + 16) 8 = some remainder.toNat ∧
    widthLoad d ((r (.GPR 31#5) s + 144#64).toNat + 64) 4 = some 0 at stored
  have pointer : read_mem_bytes 8 (r (.GPR 31#5) s + 144#64) d = quotient.pointer := by
    simpa only [Nat.add_zero, BitVec.add_zero] using
      read_of_observe_offset d (r (.GPR 31#5) s + 144#64) 0 8 quotient.pointer
        (by simpa only [Nat.add_zero] using stored.1.1)
  have payload : read_mem_bytes 8 (r (.GPR 31#5) s + 152#64) d = quotient.payload := by
    simpa only [BitVec.add_assoc, show 144#64 + 8#64 = 152#64 by decide] using
      read_of_observe_offset d (r (.GPR 31#5) s + 144#64) 8 8 quotient.payload stored.1.2.1
  have remainderLoaded : read_mem_bytes 8 (r (.GPR 31#5) s + 160#64) d = remainder := by
    simpa only [BitVec.add_assoc, show 144#64 + 16#64 = 160#64 by decide] using
      read_of_observe_offset d (r (.GPR 31#5) s + 144#64) 16 8 remainder stored.2.1
  have status : read_mem_bytes 4 (r (.GPR 31#5) s + 208#64) d = 0#32 := by
    simpa only [BitVec.add_assoc, show 144#64 + 64#64 = 208#64 by decide] using
      read_of_observe_offset d (r (.GPR 31#5) s + 144#64) 64 4 0#32 stored.2.2
  refine ⟨current.status_counted base remainder (by rw [current.sp]; exact remainderLoaded), ?_, ?_⟩
  · simp only [Block.divisionStatusResult, state_simp_rules, current.sp, status, ite_true]
  · have observe : widthLoad (Block.divisionStatusResult d base) =
        widthLoad (write_mem_bytes 16 (r (.GPR 31#5) s + 64#64)
          (quotient.payload ++ quotient.pointer) d) := by
      funext address bytes
      simp only [widthLoad, Block.divisionStatusResult, state_simp_rules, current.sp, pointer, payload]
      simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes,
        Memory.write_mem_bytes_eq_mem_write_bytes, state_simp_rules]
    rw [observe]
    have bound := owned.stackHigh
    have physical : (r (.GPR 31#5) s + 64#64).toNat + 16 ≤ 2^64 := by bv_omega
    have originalSuccess : (SszNative.NatDivision.run length 8 (arenaOf s).base
        (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder) := by
      simpa only [outcome, divided_eq] using success
    exact operand_at_written_pair d (r (.GPR 31#5) s + 64#64) quotient physical stored.1.2.2
      ((stack_copy_covered owned 64 16 (by decide)).operand quotient
        (quotient_local_owned owned originalSuccess))

end SszArm.BitVector
