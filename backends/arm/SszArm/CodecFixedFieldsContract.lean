import SszArm.CodecFixedFieldsCall
import SszArm.CodecFixedFieldsTail
import SszArm.CodecFixedEntry

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (Desc)

def fieldWrites (source : ArmState) (budget : Nat) : List Delimited.Span :=
  Stack.envelope (r (.GPR 31#5) source).toNat (32 + budget)

/-- The remaining native slice, not a disjoint logical ownership tree. The
physical byte count bounds the real loop counter; logical metadata is absent. -/
structure FieldsOwned (source current : ArmState) (fields : List (String × Desc))
    (pointer budget : Nat) : Prop where
  stack : 32 + budget ≤ (r (.GPR 31#5) source).toNat
  lowering : 16 ≤ budget
  children : isFixedFieldsStack fields ≤ budget
  context : BodyContext source current
  pointer : r (.GPR 8#5) current = BitVec.ofNat 64 pointer
  count : r (.GPR 19#5) current = BitVec.ofNat 64 (24 * fields.length)
  range : pointer + 24 * fields.length ≤ 2^64
  countBound : 24 * fields.length < 2^64
  fields : (Storage.fieldEntries pointer fields).Owned (fieldWrites source budget) current

structure FieldsPost (source current final : ArmState) (fields : List (String × Desc))
    (base : BitVec 64) (budget : Nat) : Prop where
  context : BodyContext source final
  program : final.program = current.program
  error : read_err final = .None
  pc : read_pc final = base + if SszNative.FixedSize.fieldsFixed fields then 188#64 else 172#64
  frame : Delimited.MemoryFrame (fieldWrites source budget) current final

end SszArm.Codec.Fixed.IsFixed
