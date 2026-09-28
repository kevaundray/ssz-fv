import SszArm.MeasureBitsReturnedSuccess
import SszArm.MeasureBitsReturnedError
import SszArm.MeasureHelpersAllocation
import SszArm.MeasureHelpersFrame
import SszArm.MeasureHelpersNativeView

namespace SszArm.Measure.Bits.Constructor

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

def result (s : ArmState) : Except SszNative.Serialize.Error SszNative.NatOperand :=
  (NatFromU128.outcome s).result.mapError SszNative.Serialize.Error.arithmetic

def tailWrites (s : ArmState) : List Span :=
  match (NatFromU128.outcome s).result with
  | .ok _ => Result.successWrites s
  | .error _ => [((r (.GPR 19#5) s).toNat, 72)]

def writesFor (s : ArmState) : List Span := NatFromU128.writesFor s ++ tailWrites s

/-- Original current-state geometry at the real BL1912. Every conditional here
is a pure accepted fromWide outcome, not a premise about future execution. -/
structure Space (s : ArmState) : Prop where
  native : NatFromU128.Owned s
  scratch : r (.GPR 0#5) s = r (.GPR 31#5) s + 120#64
  savedScratch : r (.GPR 23#5) s = r (.GPR 31#5) s + 120#64
  scratchBound : (r (.GPR 31#5) s).toNat + 192 ≤ 2^64
  success : Result.SuccessSpace s
  failure : match (NatFromU128.outcome s).result with
    | .ok _ => True
    | .error _ => Propagation.CopySpace s
  headerTail : Protected (tailWrites s) (r (.GPR 4#5) s).toNat 24
  freeTail : Protected (tailWrites s)
    ((NatDivision.arenaOf s).base + (NatDivision.arenaOf s).used)
    ((NatDivision.arenaOf s).capacity - (NatDivision.arenaOf s).used)

structure Post (s t : ArmState) (base : BitVec 64)
    extends ReturnedPost s t base (result s) (writesFor s) where
  cursor : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat = (NatFromU128.outcome s).used
  header : read_mem_bytes 8 (r (.GPR 4#5) s) t = NatFromU128.addressWord s ∧
    read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) t = NatFromU128.capacityWord s
  written : NatDivision.WrittenAt (widthLoad t) (NatFromU128.outcome s)

end SszArm.Measure.Bits.Constructor
