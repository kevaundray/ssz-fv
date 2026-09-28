import SszArm.SerializeImpl
import SszArm.MeasurePost
import SszArm.MeasureAllocationFrame
import SszArm.EmitPost
import SszSerializeResources

namespace SszArm.Serialize

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Outcome Error Written)
open Delimited (Span Protected MemoryFrame)
open UintCodec (widthLoad)

structure Args where
  result : BitVec 64
  descriptor : BitVec 64
  value : BitVec 64
  output : BitVec 64
  capacity : BitVec 64
  arena : BitVec 64
  stack : BitVec 64

def Args.ofEntry (s : ArmState) : Args :=
  ⟨r (.GPR 0#5) s, r (.GPR 1#5) s, r (.GPR 2#5) s,
   r (.GPR 3#5) s, r (.GPR 4#5) s, r (.GPR 5#5) s, r (.GPR 31#5) s⟩

def Args.bodySP (args : Args) : BitVec 64 := args.stack - 144#64

def Args.plan (args : Args) : BitVec 64 := args.bodySP + 24#64

def Args.measure (args : Args) : Measure.Args :=
  ⟨args.plan, args.descriptor, args.value, args.arena, 1#8, args.bodySP⟩

def Args.emit (args : Args) (count : Nat) : Emit.Args :=
  ⟨args.result, args.descriptor, args.value, args.output, BitVec.ofNat 64 count, args.bodySP⟩

def arenaOf (s : ArmState) (args : Args) : SszNative.Delimited.ArenaState :=
  Measure.arenaOf s args.measure

def measured (s : ArmState) (args : Args) (desc : Desc) (value : Value) : Outcome NatOperand :=
  SszNative.Serialize.measure desc value (arenaOf s args)

def outcome (s : ArmState) (args : Args) (desc : Desc) (value : Value) : Written :=
  SszNative.Serialize.serialize desc value args.capacity.toNat (arenaOf s args)

def saveWrites (args : Args) : List Span := [(args.stack.toNat - 48, 48)]

/-- The original writable stack regions, including both callees and lowering
spills. The unaccessed gaps are not included. This is ownership, not a claim
that the wrapper has initialized a Plan or any output byte. -/
def stackSpans (args : Args) : List Span :=
  [(args.stack.toNat - 432, 16), (args.stack.toNat - 320, 16),
   (args.stack.toNat - 296, 68), (args.stack.toNat - 224, 80),
   (args.stack.toNat - 160, 16), (args.stack.toNat - 136, 16),
   (args.stack.toNat - 120, 72), (args.stack.toNat - 48, 48)]

def externalSpans (args : Args) : List Span :=
  [(args.result.toNat, 72), (args.output.toNat, args.capacity.toNat)]

def freeSpan (s : ArmState) (args : Args) : Span :=
  ((arenaOf s args).base + (arenaOf s args).used,
   (arenaOf s args).capacity - (arenaOf s args).used)

/-- A static original-input ownership envelope, not a future callee contract. -/
def writable (s : ArmState) (args : Args) : List Span :=
  stackSpans args ++ externalSpans args ++
    [(args.arena.toNat + 16, 8), freeSpan s args]

structure Owned (s : ArmState) (args : Args) (desc : Desc) (value : Value) : Prop where
  physical : value.Physical
  descriptorBound : args.descriptor.toNat + Emit.descriptorBytes desc ≤ 2^64
  descriptor : Emit.DescriptorAt s args.descriptor desc
  valueBound : args.value.toNat + Emit.valueBytes value ≤ 2^64
  value_at : Emit.ValueAt s args.value value
  resultBound : args.result.toNat + 72 ≤ 2^64
  outputBound : args.output.toNat + args.capacity.toNat ≤ 2^64
  arenaBound : args.arena.toNat + 24 ≤ 2^64
  storageBound : (arenaOf s args).base + (arenaOf s args).capacity ≤ 2^64
  nonnull : 0 < (arenaOf s args).capacity → 0 < (arenaOf s args).base
  stackLow : 432 ≤ args.stack.toNat
  resultStack : Protected (stackSpans args) args.result.toNat 72
  outputStack : Protected (stackSpans args) args.output.toNat args.capacity.toNat
  outputResult : Protected [(args.result.toNat, 72)] args.output.toNat args.capacity.toNat
  arenaOwned : Protected (stackSpans args ++ externalSpans args) args.arena.toNat 24
  freeOwned : Protected (stackSpans args ++ externalSpans args ++ [(args.arena.toNat, 24)])
    (freeSpan s args).1 (freeSpan s args).2
  descriptorOwned : Protected (writable s args) args.descriptor.toNat (Emit.descriptorBytes desc)
  valueOwned : Protected (writable s args) args.value.toNat (Emit.valueBytes value)
  operandOwned : ∀ operand ∈ Emit.descriptorOperands desc ++ Emit.valueOperands value,
    NatDivision.OperandOwned (writable s args) operand
  backingOwned : ∀ span ∈ Measure.backingSpans s args.measure value,
    Protected (writable s args) span.1 span.2

def ResultAt (observe : Nat → Nat → Option Nat) (address : Nat) : Except Error Nat → Prop
  | .ok count => observe address 8 = some count ∧ observe (address + 64) 4 = some 0
  | .error reason => Measure.ErrorAt observe address reason

/-- Wrapper stores after measurement: errors copy all 72 bytes, whereas success
restages only the five initialized Plan words. The status word is not restaged. -/
def afterMeasureWrites (args : Args) (first : Outcome NatOperand) : List Span :=
  [(args.stack.toNat - 136, 16)] ++
    match first.result with
    | .error _ => [(args.result.toNat, 72)]
    | .ok _ => [(args.stack.toNat - 120, 40)]

def sizeWrites (args : Args) (operand : NatOperand) : List Span :=
  match operand with
  | .small _ => []
  | .large _ limbs => if limbs = [] then [] else [(args.stack.toNat - 160, 8)]

def continuationWrites (args : Args) (first : Outcome NatOperand) : List Span :=
  match first.result with
  | .error _ => []
  | .ok operand => sizeWrites args operand ++
      if operand.value < 2^64 ∧ operand.value ≤ args.capacity.toNat then
        Emit.writesFor (args.emit operand.value) operand.value
      else [(args.stack.toNat - 160, 16), (args.result.toNat, 68)]

def writesFor (s : ArmState) (args : Args) (desc : Desc) (value : Value) : List Span :=
  saveWrites args ++ Measure.writesFor args.measure (measured s args desc value) ++
    afterMeasureWrites args (measured s args desc value) ++
    continuationWrites args (measured s args desc value)

structure Post (s t : ArmState) (desc : Desc) (value : Value) : Prop where
  returned : Emit.Returned s t
  result : ResultAt (widthLoad t) (Args.ofEntry s).result.toNat
    (outcome s (Args.ofEntry s) desc value).outcome.result
  cursor : (read_mem_bytes 8 ((Args.ofEntry s).arena + 16#64) t).toNat =
    (outcome s (Args.ofEntry s) desc value).outcome.used
  header : read_mem_bytes 8 (Args.ofEntry s).arena t = read_mem_bytes 8 (Args.ofEntry s).arena s ∧
    read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) t =
      read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) s
  written : ∀ call ∈ (outcome s (Args.ofEntry s) desc value).outcome.calls,
    NatDivision.WrittenAt (widthLoad t) call
  bytes : SszNative.ByteView.BytesAt (widthLoad t) (Args.ofEntry s).output.toNat
    (outcome s (Args.ofEntry s) desc value).writes
  frame : MemoryFrame (writesFor s (Args.ofEntry s) desc value) s t
  descriptor : Emit.DescriptorAt t (Args.ofEntry s).descriptor desc
  value_at : Emit.ValueAt t (Args.ofEntry s).value value
  operands : ∀ operand ∈ Emit.descriptorOperands desc ++ Emit.valueOperands value,
    NatDivision.OperandPreserved s t operand
  backing : ∀ span ∈ Measure.backingSpans s (Args.ofEntry s).measure value,
    ∀ address : BitVec 64, span.1 ≤ address.toNat → address.toNat < span.1 + span.2 →
      t.mem address = s.mem address
  tail : ∀ index, (outcome s (Args.ofEntry s) desc value).writes.size ≤ index →
    index < (Args.ofEntry s).capacity.toNat →
      t.mem ((Args.ofEntry s).output + BitVec.ofNat 64 index) =
        s.mem ((Args.ofEntry s).output + BitVec.ofNat 64 index)

end SszArm.Serialize
