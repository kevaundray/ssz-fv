import SszArm.BitVectorPaddingGate
import SszArm.BitVectorNarrowCall
import SszArm.BitVectorSuccess

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- After exact scope succeeds, execute either the native padding error or the
complete original-length narrowing and inlined Bits construction. -/
theorem finish_executes {s c : ArmState} {length expected : SszNative.NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (base : BitVec 64)
    (owned : Owned s length data) (current : Counted s c length remainder)
    (arithmetic : SszNative.BitVector.Expected length expected remainder)
    (scope : SszNative.NatNarrow.runExact expected (BitVec.ofNat 64 data.size) = true)
    (before : MemoryFrame (writesFor s (outcome s length data)) s c)
    (code : JointCodeAt c base) (aligned : CheckSPAlignment s)
    (pc : read_pc c = base + 6000#64) :
    ∃ fuel t, run fuel c = t ∧
      Terminal s t base data (SszNative.BitVector.finish length expected remainder data) ∧
      MemoryFrame (localWrites s) c t := by
  obtain ⟨paddingFuel, paddingState, paddingRun, paddingPost, semantic⟩ :=
    PaddingGate.decision base owned current arithmetic scope code.body pc
      (current.toWorking.aligned aligned) (original_bytes owned before)
  by_cases bad : PaddingGate.Bad remainder data
  · have branch : read_pc paddingState = base + 4732#64 ∧
        SszNative.BitVector.ResultAt (widthLoad paddingState) (r (.GPR 0#5) s).toNat
          (r (.GPR 2#5) s).toNat data (.error .paddingBits) := by
      simpa only [if_pos bad] using paddingPost.branch
    refine ⟨paddingFuel, paddingState, paddingRun, ?_, paddingPost.frame⟩
    rw [semantic, if_pos bad]
    exact ⟨branch.1, paddingPost.counted.error, paddingPost.counted.sp,
      paddingPost.counted.vectors, branch.2⟩
  · have paddingPC : read_pc paddingState = base + 6576#64 := by
      simpa only [if_neg bad] using paddingPost.branch
    have paddingCode := code.of_program paddingPost.program
    have afterPadding := before.trans ((local_covered s (outcome s length data)).frame paddingPost.frame)
    obtain ⟨narrowFuel, narrowed, narrowRun, narrowPost, narrowCurrent, narrowCode, narrowPC, narrowFrame⟩ :=
      narrowing_executes base owned paddingPost.counted afterPadding paddingCode aligned paddingPC
    have args := narrow_arguments base paddingPost.counted.toWorking
    have observed : SszNative.NatNarrow.U128ResultAt (widthLoad narrowed)
        (r (.GPR 31#5) s + 144#64).toNat (SszNative.NatNarrow.toU128 length) := by
      simpa only [args.1] using narrowPost.result
    have afterNarrow := afterPadding.trans ((local_covered s (outcome s length data)).frame narrowFrame)
    obtain ⟨valueFuel, final, valueRun, terminal, valueFrame⟩ :=
      value_terminal base owned narrowCurrent arithmetic scope afterNarrow observed narrowCode aligned narrowPC
    have whole : run (paddingFuel + narrowFuel + valueFuel) c = final := by
      rw [run_plus, run_plus, paddingRun, narrowRun, valueRun]
    refine ⟨paddingFuel + narrowFuel + valueFuel, final, whole, ?_,
      (paddingPost.frame.trans narrowFrame).trans valueFrame⟩
    simpa only [semantic, if_neg bad] using terminal

end SszArm.BitVector
