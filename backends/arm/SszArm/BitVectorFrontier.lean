import SszArm.BitVectorResourceFrame
import SszArm.BitVectorTerminal

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- Logical resource state, independent of the native result tag. -/
structure Resources (s t : ArmState) (length : SszNative.NatOperand) (data : Ssz.Bytes) : Prop where
  arena : ArenaAt s t (outcome s length data).used
  written : (outcome s length data).writtenAt (widthLoad t)

theorem Resources.after_local {s a b : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (current : Resources s a length data) (owned : Owned s length data)
    (frame : MemoryFrame (localWrites s) a b) : Resources s b length data :=
  ⟨current.arena.after_local owned frame, written_after_local owned frame current.written⟩

/-- The arithmetic phase's normal exit, reached before the exact scope helper.
The expected representation is the exact physical copied pair, not a synthetic
canonical numeral. -/
structure ExpectedAt (s t : ArmState) (base : BitVec 64) (length expected : SszNative.NatOperand)
    (remainder : BitVec 64) (data : Ssz.Bytes) : Prop where
  current : Counted s t length remainder
  pc : read_pc t = base + 5948#64
  code : JointCodeAt t base
  pair : SszNative.NatArithmetic.operandAt (widthLoad t)
    (r (.GPR 31#5) s + 48#64).toNat expected
  limbs : NatDivision.OperandOwned (localWrites s) expected
  arithmetic : SszNative.BitVector.Expected length expected remainder
  model : (outcome s length data).result = SszNative.BitVector.finish length expected remainder data
  resources : Resources s t length data
  frame : MemoryFrame (writesFor s (outcome s length data)) s t

structure Completed (s t : ArmState) (base : BitVec 64) (length : SszNative.NatOperand)
    (data : Ssz.Bytes) : Prop where
  terminal : Terminal s t base data (outcome s length data).result
  resources : Resources s t length data
  frame : MemoryFrame (writesFor s (outcome s length data)) s t
  code : JointCodeAt t base

theorem Completed.post {s t : ArmState} {base : BitVec 64} {length : SszNative.NatOperand}
    {data : Ssz.Bytes} (completed : Completed s t base length data)
    (owned : Owned s length data) (aligned : CheckSPAlignment s) :
    Post s (run 8 t) length data :=
  completed.terminal.finish owned completed.code.body aligned completed.resources.written
    completed.resources.arena.cursor completed.resources.arena.base
    completed.resources.arena.capacity completed.frame

end SszArm.BitVector
