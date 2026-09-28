import SszArm.BitVectorOriginal
import SszArm.BitVectorTerminal
import SszArm.BitVectorValueFrame

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- Interpret the actual narrowing object and execute every inlined success
guard/store. Original ownership discharges all terminal storage obligations. -/
theorem value_terminal {s c : ArmState} {length expected : SszNative.NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (base : BitVec 64)
    (owned : Owned s length data) (current : Counted s c length remainder)
    (arithmetic : SszNative.BitVector.Expected length expected remainder)
    (scope : SszNative.NatNarrow.runExact expected (BitVec.ofNat 64 data.size) = true)
    (before : MemoryFrame (writesFor s (outcome s length data)) s c)
    (observed : SszNative.NatNarrow.U128ResultAt (widthLoad c)
      (r (.GPR 31#5) s + 144#64).toNat (SszNative.NatNarrow.toU128 length))
    (code : JointCodeAt c base) (aligned : CheckSPAlignment s)
    (pc : read_pc c = base + 6592#64) :
    ∃ fuel t, run fuel c = t ∧
      Terminal s t base data (SszNative.BitVector.construct length data) ∧
      MemoryFrame (localWrites s) c t := by
  have space := ValueTail.space_of_owned s c length data owned current.sp current.output
  have cover := ValueTail.writes_covered s c owned.stackLow current.sp current.output
  have scopeActual : SszNative.NatNarrow.runExact expected (r (.GPR 20#5) c) = true := by
    rw [current.toWorking.byte_count owned]
    exact scope
  have bound := owned.stackHigh
  have pointer : (r (.GPR 31#5) s + 144#64).toNat = (r (.GPR 31#5) s).toNat + 144 := by
    bv_omega
  have privateObject : SszNative.NatNarrow.U128ResultAt (widthLoad c)
      ((r (.GPR 31#5) c).toNat + 144) (SszNative.NatNarrow.toU128 length) := by
    simpa only [current.sp, pointer] using observed
  have size : (r (.GPR 20#5) c).toNat = data.size := by
    rw [current.size]
    exact owned.length
  have bytes : SszNative.ByteView.BytesAt (widthLoad c) (r (.GPR 24#5) c).toNat data := by
    rw [current.input]
    exact original_bytes owned before
  have inputBound : (r (.GPR 24#5) c).toNat + data.size ≤ 2^64 := by
    rw [current.input]
    exact owned.inputBound
  have inputOwned : Delimited.Protected (ValueTail.writes c) (r (.GPR 24#5) c).toNat data.size := by
    rw [current.input]
    exact ((local_covered s (outcome s length data)).trans cover).protected owned.inputOwned
  have post := ValueTail.correct_of_scope c base length expected remainder data space code.body
    current.error (current.toWorking.aligned aligned) pc arithmetic scopeActual privateObject
    size bytes inputBound inputOwned
  refine ⟨ValueTail.fuel c base, run (ValueTail.fuel c base) c, rfl, ?_, cover.frame post.frame⟩
  rw [construct_of_scope owned arithmetic scope]
  refine ⟨post.pc, post.error, post.sp.trans current.sp, ?_, ?_⟩
  · intro reg low high
    exact (congrArg (fun value : BitVec 128 => value.setWidth 64) (post.vectors reg)).trans
      (current.vectors reg low high)
  · simpa only [current.output, current.input] using post.resultAt

end SszArm.BitVector
