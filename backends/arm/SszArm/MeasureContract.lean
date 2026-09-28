import SszArm.MeasureImpl
import SszArm.EmitContract

namespace SszArm.Measure

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Outcome Error)
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

structure Args where
  result : BitVec 64
  descriptor : BitVec 64
  value : BitVec 64
  arena : BitVec 64
  retain : BitVec 8
  stack : BitVec 64

def Args.ofEntry (s : ArmState) : Args :=
  ⟨r (.GPR 0#5) s, r (.GPR 1#5) s, r (.GPR 2#5) s,
   r (.GPR 3#5) s, (r (.GPR 4#5) s).setWidth 8, r (.GPR 31#5) s⟩

def Args.bodySP (args : Args) : BitVec 64 := args.stack - 272#64

def arenaOf (s : ArmState) (args : Args) : SszNative.Delimited.ArenaState :=
  ⟨(read_mem_bytes 8 args.arena s).toNat,
   (read_mem_bytes 8 (args.arena + 8#64) s).toNat,
   (read_mem_bytes 8 (args.arena + 16#64) s).toNat⟩

def outcome (s : ArmState) (args : Args) (desc : Desc) (value : Value) : Outcome NatOperand :=
  SszNative.Serialize.measure desc value (arenaOf s args)

/-- Active descriptor fields, not inactive Rust enum padding. -/
def descriptorSpans (args : Args) : Desc → List Span
  | .bool => [(args.descriptor.toNat, 8)]
  | .progressiveBitList none => [(args.descriptor.toNat, 16)]
  | .progressiveBitList (some _) => [(args.descriptor.toNat, 32)]
  | _ => [(args.descriptor.toNat, 24)]

/-- The tag and live payload are owned independently of enum padding. -/
def valueSpans (args : Args) : Value → List Span
  | .bool _ => [(args.value.toNat, 2)]
  | .uint _ | .bytes _ => [(args.value.toNat, 1), (args.value.toNat + 8, 16)]
  | .bits _ => [(args.value.toNat, 1), (args.value.toNat + 16, 32)]
  | .seq _ | .union _ _ => [(args.value.toNat, 1)]

def backingSpans (s : ArmState) (args : Args) : Value → List Span
  | .bytes bytes => [((read_mem_bytes 8 (args.value + 8#64) s).toNat, bytes.size)]
  | .bits bits => [((read_mem_bytes 8 (args.value + 16#64) s).toNat, bits.bytes.size)]
  | _ => []

/-- Only a failed second constructor is copied through the 72-byte propagation
path. Inline first-constructor errors initialize exactly 68 result bytes. -/
def propagated (measured : Outcome NatOperand) : Bool :=
  match measured.result with
  | .error (.arithmetic _) => measured.calls.length == 2
  | _ => false

def resultExtent (measured : Outcome NatOperand) : Nat :=
  if propagated measured then 72 else 68

def resultWrites (args : Args) (measured : Outcome NatOperand) : List Span :=
  match measured.result with
  | .ok _ => [(args.result.toNat, 40), (args.result.toNat + 64, 4)]
  | .error _ => [(args.result.toNat, resultExtent measured)]

/-- The constructor's result occupies SP+120..188 only when the real helper is
called. Its four-byte tail at SP+188 is read, never initialized by measurement. -/
def bodyStackWrites (args : Args) (measured : Outcome NatOperand) : List Span :=
  [(args.stack.toNat - 288, 16)] ++
    (if measured.calls.length = 2 then [(args.stack.toNat - 152, 68)] else [])

def saveWrites (args : Args) : List Span := [(args.stack.toNat - 80, 80)]

def stackWrites (args : Args) (measured : Outcome NatOperand) : List Span :=
  saveWrites args ++ bodyStackWrites args measured

def allocationWrites (args : Args) (measured : Outcome NatOperand) : List Span :=
  measured.calls.flatMap fun call => match call.allocation with
    | none => []
    | some reservation =>
      [(args.arena.toNat + 16, 8), (reservation.pointer, 8 * call.written.length)]

def localWrites (args : Args) (measured : Outcome NatOperand) : List Span :=
  stackWrites args measured ++ resultWrites args measured

def bodyWrites (args : Args) (measured : Outcome NatOperand) : List Span :=
  bodyStackWrites args measured ++ resultWrites args measured ++ allocationWrites args measured

def writesFor (args : Args) (measured : Outcome NatOperand) : List Span :=
  localWrites args measured ++ allocationWrites args measured

def errorCode : Error → Nat
  | .wrongType => 1
  | .limit _ _ => 2
  | .scope _ _ => 3
  | .arithmetic .scratchExhausted => 32768
  | .arithmetic .badRepresentation => 32770
  | .outputTooSmall => 32769

def errorOperands : Error → NatOperand × NatOperand
  | .scope expected actual | .limit expected actual => (expected, actual)
  | _ => (.small 0#64, .small 0#64)

/-- The private NativeError representation agrees with the checked arithmetic
layout. Scope and Limit preserve both original Nat representations. -/
def ErrorAt (observe : Nat → Nat → Option Nat) (address : Nat) (reason : Error) : Prop :=
  observe address 8 = some 1 ∧ observe (address + 8) 8 = some 0 ∧
  SszNative.NatArithmetic.operandAt observe (address + 16) (errorOperands reason).1 ∧
  SszNative.NatArithmetic.operandAt observe (address + 32) (errorOperands reason).2 ∧
  observe (address + 48) 8 = some 0 ∧ observe (address + 56) 8 = some 0 ∧
  observe (address + 64) 4 = some (errorCode reason)

/-- Only initialized Plan fields occur here; bytes 40..64 and 68..72 are not
promised on success. Empty children use the aligned dangling pointer eight. -/
def ResultAt (observe : Nat → Nat → Option Nat) (address : Nat) :
    Except Error NatOperand → Prop
  | .ok operand => observe address 8 = some 8 ∧ observe (address + 8) 8 = some 0 ∧
      SszNative.NatArithmetic.operandAt observe (address + 16) operand ∧
      observe (address + 32) 8 = some 0 ∧ observe (address + 64) 4 = some 0
  | .error reason => ErrorAt observe address reason

/-- All premises concern original storage. There is no successful expectedSize,
future helper exit, initialized result object, or valid-cursor premise. -/
structure Owned (s : ArmState) (args : Args) (desc : Desc) (value : Value) : Prop where
  retain : args.retain = 0#8 ∨ args.retain = 1#8
  physical : value.Physical
  descriptor : Emit.DescriptorAt s args.descriptor desc
  value_at : Emit.ValueAt s args.value value
  descriptorBound : ∀ span ∈ descriptorSpans args desc, span.1 + span.2 ≤ 2^64
  valueBound : ∀ span ∈ valueSpans args value, span.1 + span.2 ≤ 2^64
  resultBound : args.result.toNat + resultExtent (outcome s args desc value) ≤ 2^64
  arenaBound : args.arena.toNat + 24 ≤ 2^64
  storageBound : (arenaOf s args).base + (arenaOf s args).capacity ≤ 2^64
  nonnull : 0 < (arenaOf s args).capacity → 0 < (arenaOf s args).base
  stackLow : 288 ≤ args.stack.toNat
  resultStack : ∀ span ∈ resultWrites args (outcome s args desc value),
    Protected (stackWrites args (outcome s args desc value)) span.1 span.2
  headerLocal : Protected (localWrites args (outcome s args desc value)) args.arena.toNat 24
  freeLocal : Protected (localWrites args (outcome s args desc value) ++ [(args.arena.toNat, 24)])
    ((arenaOf s args).base + (arenaOf s args).used)
    ((arenaOf s args).capacity - (arenaOf s args).used)
  descriptorOwned : ∀ span ∈ descriptorSpans args desc,
    Protected (writesFor args (outcome s args desc value)) span.1 span.2
  valueOwned : ∀ span ∈ valueSpans args value,
    Protected (writesFor args (outcome s args desc value)) span.1 span.2
  operandOwned : ∀ operand ∈ Emit.descriptorOperands desc ++ Emit.valueOperands value,
    NatDivision.OperandOwned (writesFor args (outcome s args desc value)) operand
  backingOwned : ∀ span ∈ backingSpans s args value,
    Protected (writesFor args (outcome s args desc value)) span.1 span.2

structure BodyRegisters (s : ArmState) (args : Args) : Prop where
  result : r (.GPR 19#5) s = args.result
  arena : r (.GPR 20#5) s = args.arena
  value : r (.GPR 21#5) s = args.value
  stack : r (.GPR 31#5) s = args.bodySP

/-- A leaf summary ends at the real common epilogue, after its actual status store. -/
structure Produced (s t : ArmState) (args : Args) (desc : Desc) (value : Value)
    (base : BitVec 64) : Prop where
  pc : read_pc t = base + 4116#64
  program : t.program = s.program
  error : read_err t = .None
  stack : r (.GPR 31#5) t = args.bodySP
  result : ResultAt (widthLoad t) args.result.toNat (outcome s args desc value).result
  cursor : (read_mem_bytes 8 (args.arena + 16#64) t).toNat = (outcome s args desc value).used
  header : read_mem_bytes 8 args.arena t = read_mem_bytes 8 args.arena s ∧
    read_mem_bytes 8 (args.arena + 8#64) t = read_mem_bytes 8 (args.arena + 8#64) s
  written : ∀ call ∈ (outcome s args desc value).calls,
    NatDivision.WrittenAt (widthLoad t) call
  frame : MemoryFrame (bodyWrites args (outcome s args desc value)) s t
  registers : ∀ reg : BitVec 5, reg ∈ [18#5, 27#5, 28#5, 29#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

structure Returned (s t : ArmState) : Prop where
  pc : read_pc t = r (.GPR 30#5) s
  error : read_err t = .None
  program : t.program = s.program
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, 18 ≤ reg.toNat → reg.toNat ≤ 30 →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

structure Post (s t : ArmState) (desc : Desc) (value : Value) : Prop where
  returned : Returned s t
  result : ResultAt (widthLoad t) (Args.ofEntry s).result.toNat
    (outcome s (Args.ofEntry s) desc value).result
  cursor : (read_mem_bytes 8 ((Args.ofEntry s).arena + 16#64) t).toNat =
    (outcome s (Args.ofEntry s) desc value).used
  header : read_mem_bytes 8 (Args.ofEntry s).arena t = read_mem_bytes 8 (Args.ofEntry s).arena s ∧
    read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) t =
      read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) s
  written : ∀ call ∈ (outcome s (Args.ofEntry s) desc value).calls,
    NatDivision.WrittenAt (widthLoad t) call
  frame : MemoryFrame (writesFor (Args.ofEntry s) (outcome s (Args.ofEntry s) desc value)) s t
  descriptor : Emit.DescriptorAt t (Args.ofEntry s).descriptor desc
  value_at : Emit.ValueAt t (Args.ofEntry s).value value
  operands : ∀ operand ∈ Emit.descriptorOperands desc ++ Emit.valueOperands value,
    NatDivision.OperandPreserved s t operand
  backing : ∀ span ∈ backingSpans s (Args.ofEntry s) value, ∀ address : BitVec 64,
    span.1 ≤ address.toNat → address.toNat < span.1 + span.2 → t.mem address = s.mem address

end SszArm.Measure
