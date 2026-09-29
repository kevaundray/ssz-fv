import SszArm.CodecFixedStack
import SszArm.CodecStorageTypes
import SszArm.CodecStack
import SszFixedSizeClassification

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (Desc)
open Delimited (MemoryFrame Returned)

/-- Only this finite recursive stack region is mutable. Descriptor storage may
share any read-only backing; it need not form a disjoint ownership tree. -/
def writes (s : ArmState) (desc : Desc) : List Delimited.Span :=
  Stack.envelope (r (.GPR 31#5) s).toNat (isFixedStack desc)

structure Owned (s : ArmState) (desc : Desc) : Prop where
  stack : isFixedStack desc ≤ (r (.GPR 31#5) s).toNat
  descriptor : Storage.DescOwned (writes s desc) s (r (.GPR 0#5) s).toNat desc

structure Post (s t : ArmState) (desc : Desc) : Prop where
  returned : Returned s t
  platform : r (.GPR 18#5) t = r (.GPR 18#5) s
  program : t.program = s.program
  result : r (.GPR 0#5) t = if SszNative.FixedSize.isFixed desc then 1#64 else 0#64
  frame : MemoryFrame (writes s desc) s t

theorem Post.descriptor {s t : ArmState} {desc : Desc}
    (owned : Owned s desc) (post : Post s t desc) :
    Storage.DescOwned (writes s desc) t (r (.GPR 0#5) s).toNat desc :=
  Storage.desc_preserved owned.descriptor post.frame

/-- Refinement does not require prior schema validation or successful width
measurement. Structural classification alone selects the native return bit. -/
theorem Post.refines {s t : ArmState} {desc : Desc} (post : Post s t desc) :
    r (.GPR 0#5) t = if desc.erase.fixedSize.isSome then 1#64 else 0#64 := by
  rw [post.result, SszNative.FixedSize.isFixed_eq]

end SszArm.Codec.Fixed.IsFixed
