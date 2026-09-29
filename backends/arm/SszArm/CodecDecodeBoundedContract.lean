import SszArm.CodecDecodeBoundedOps
import SszArm.CodecMeasureError
import SszArm.NatCompareProofs
import SszCodecDecodeCore

namespace SszArm.Codec.Decode.Bounded

open SszNative
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

def stackWrites (s : ArmState) : List Span :=
  [((r (.GPR 31#5) s).toNat - 64, 16),
   ((r (.GPR 31#5) s).toNat - 48, 8),
   ((r (.GPR 31#5) s).toNat - 32, 32)]

def localWrites (s : ArmState) : List Span :=
  ((r (.GPR 0#5) s).toNat, 68) :: stackWrites s

def limitBytes : Option NatOperand → Nat
  | none => 4
  | some _ => 24

/-- Rust Option<Nat> has a four-byte discriminant and a payload at +8. An
absent bound does not assert or read an initialized payload. -/
def LimitAt (s : ArmState) (address : BitVec 64) : Option NatOperand → Prop
  | none => read_mem_bytes 4 address s = 0#32
  | some cap => read_mem_bytes 4 address s = 1#32 ∧
      read_mem_bytes 8 (address + 8#64) s = cap.pointer ∧
      read_mem_bytes 8 (address + 16#64) s = cap.payload ∧ cap.At (widthLoad s)

def ActualAt (s : ArmState) (address : BitVec 64) (actual : NatOperand) : Prop :=
  read_mem_bytes 8 address s = actual.pointer ∧
  read_mem_bytes 8 (address + 8#64) s = actual.payload ∧ actual.At (widthLoad s)

structure Owned (s : ArmState) (limit : Option NatOperand) (actual : NatOperand) : Prop where
  limitAt : LimitAt s (r (.GPR 1#5) s) limit
  actualAt : ActualAt s (r (.GPR 2#5) s) actual
  limitBound : (r (.GPR 1#5) s).toNat + limitBytes limit ≤ 2 ^ 64
  actualBound : (r (.GPR 2#5) s).toNat + 16 ≤ 2 ^ 64
  resultBound : (r (.GPR 0#5) s).toNat + 68 ≤ 2 ^ 64
  stackBound : 64 ≤ (r (.GPR 31#5) s).toNat
  outputStack : Protected (stackWrites s) (r (.GPR 0#5) s).toNat 68
  limitOwned : Protected (localWrites s) (r (.GPR 1#5) s).toNat (limitBytes limit)
  actualOwned : Protected (localWrites s) (r (.GPR 2#5) s).toNat 16
  limitWords : ∀ cap, limit = some cap → NatDivision.OperandOwned (localWrites s) cap
  actualWords : NatDivision.OperandOwned (localWrites s) actual

structure JointCodeAt (s : ArmState) (base : BitVec 64) : Prop where
  body : CodeAt s base
  compare : NatCompare.CodeAt s (base - 78128#64)

def ResultAt (s : ArmState) (address : Nat) : Except Codec.Error Unit → Prop
  | .ok () => widthLoad s (address + 64) 4 = some 0
  | .error reason => SszArm.Codec.Measure.ErrorAt (widthLoad s) address reason

def writesFor (s : ArmState) (result : Except Codec.Error Unit) : List Span :=
  (match result with
  | .ok () => ((r (.GPR 0#5) s).toNat + 64, 4)
  | .error _ => ((r (.GPR 0#5) s).toNat, 68)) :: stackWrites s

structure Post (s t : ArmState) (limit : Option NatOperand) (actual : NatOperand) : Prop where
  result : ∀ used, ResultAt t (r (.GPR 0#5) s).toNat (CodecDecode.bounded limit actual used).result
  pc : read_pc t = r (.GPR 30#5) s
  error : read_err t = .None
  program : t.program = s.program
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, 18 ≤ reg.toNat → reg.toNat ≤ 30 → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  frame : ∀ used, MemoryFrame (writesFor s (CodecDecode.bounded limit actual used).result) s t
  limitAt : LimitAt t (r (.GPR 1#5) s) limit
  actualAt : ActualAt t (r (.GPR 2#5) s) actual

end SszArm.Codec.Decode.Bounded
