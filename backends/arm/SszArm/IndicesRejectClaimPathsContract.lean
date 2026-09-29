import SszArm.IndicesStorageResults
import SszArm.IndicesLinkedRejectClaimPaths
import SszArm.IndicesPrefixEqualContract
import SszIndicesFrontier

namespace SszArm.Indices.RejectClaimPaths

open SszNative (NatOperand)

/-- The 160-byte activation, including the real comparator's 32-byte frame.
The result extent ends at the four-byte reason at offset 64. -/
def writes (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 0#5) s).toNat, 68), ((r (.GPR 31#5) s).toNat - 192, 192)]

/-- Original ABI observations, without a validity or canonical-Nat hypothesis.
Readonly claims and indices may alias, including being the same slice. -/
structure Owned (s : ArmState) (indices claims : List NatOperand) : Prop where
  stackLow : 192 ≤ (r (.GPR 31#5) s).toNat
  stack : Codec.Storage.Physical ((r (.GPR 31#5) s).toNat - 192) 192 16
  output : Codec.Storage.Physical (r (.GPR 0#5) s).toNat 68 8
  outputStack : (r (.GPR 0#5) s).toNat + 68 ≤ (r (.GPR 31#5) s).toNat - 192 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat
  indicesAt : (Storage.operands (r (.GPR 1#5) s).toNat indices).Owned (writes s) s
  claimsAt : (Storage.operands (r (.GPR 3#5) s).toNat claims).Owned (writes s) s
  indicesLength : (r (.GPR 2#5) s).toNat = indices.length
  claimsLength : (r (.GPR 4#5) s).toNat = claims.length

structure Post (s t : ArmState) (indices claims : List NatOperand) : Prop where
  returned : Delimited.Returned s t
  value : (Storage.unitResult (r (.GPR 0#5) s).toNat
    (SszNative.Indices.rejectClaimPaths indices claims)).At t
  memory : Delimited.MemoryFrame (writes s) s t
  program : t.program = s.program

/-- The requested slice observations survive the whole validation activation. -/
theorem Post.indices_preserved {s t : ArmState} {indices claims : List NatOperand}
    (owned : Owned s indices claims) (post : Post s t indices claims) :
    (Storage.operands (r (.GPR 1#5) s).toNat indices).Owned (writes s) t :=
  Storage.operands_preserved owned.indicesAt post.memory

theorem Post.claims_preserved {s t : ArmState} {indices claims : List NatOperand}
    (owned : Owned s indices claims) (post : Post s t indices claims) :
    (Storage.operands (r (.GPR 3#5) s).toNat claims).Owned (writes s) t :=
  Storage.operands_preserved owned.claimsAt post.memory

end SszArm.Indices.RejectClaimPaths
