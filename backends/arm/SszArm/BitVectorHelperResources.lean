import SszArm.BitVectorFrontier
import SszArm.BitVectorRoundCall

namespace SszArm.BitVector

open UintCodec (widthLoad)

theorem division_buffers {s d : ArmState} {base : BitVec 64}
    {length : SszNative.NatOperand} {data : Ssz.Bytes} (owned : Owned s length data)
    (post : NatDivision.Post (divisionEntry s base) d length) :
    SszNative.BitVector.allocationAt (widthLoad d) (outcome s length data).divided := by
  have stored := post.written
  rw [division_outcome s base length data owned] at stored
  exact stored

theorem division_resources {s d : ArmState} {base : BitVec 64}
    {length : SszNative.NatOperand} {data : Ssz.Bytes} (owned : Owned s length data)
    (post : NatDivision.Post (divisionEntry s base) d length)
    (unrounded : (outcome s length data).rounded = none) : Resources s d length data := by
  refine ⟨?_, division_buffers owned post, ?_⟩
  · simpa only [SszNative.BitVector.Outcome.used, unrounded] using division_arena owned post
  · intro rounded present
    rw [unrounded] at present
    cases present

/-- This resource transfer observes every first-helper word through the second
helper, including words trimmed out of the quotient representation. -/
theorem rounded_resources {s e d : ArmState} {length quotient : SszNative.NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (owned : Owned s length data)
    (args : RoundArguments s e length quotient)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0)
    (arenaBefore : ArenaAt s e (outcome s length data).divided.used)
    (dividedBefore : SszNative.BitVector.allocationAt (widthLoad e) (outcome s length data).divided)
    (post : NatAdd.Post e d quotient (.small 1)) : Resources s d length data := by
  have rounded := rounded_eq s length quotient remainder data division nonzero
  have arenaAfter : ArenaAt s d (rounding s length quotient).used := by
    refine ⟨?_, ?_, ?_⟩
    · have preserved := post.arena.base
      rw [args.arena] at preserved
      exact preserved.trans arenaBefore.base
    · have preserved := post.arena.capacity
      rw [args.arena] at preserved
      exact preserved.trans arenaBefore.capacity
    · have used := post.cursor
      rw [args.arena, args.model] at used
      exact used
  refine ⟨?_, ?_, ?_⟩
  · simpa only [SszNative.BitVector.Outcome.used, rounded] using arenaAfter
  · intro reservation allocated
    exact written_preserved reservation.pointer (outcome s length data).divided.written
      (division_buffer_physical owned reservation allocated)
      (division_buffer_owned_round owned args division reservation allocated) post.frame
      (dividedBefore reservation allocated)
  · intro result present
    rw [rounded] at present
    have same := Option.some.inj present
    subst result
    have stored := post.written
    rw [args.model] at stored
    exact stored

end SszArm.BitVector
