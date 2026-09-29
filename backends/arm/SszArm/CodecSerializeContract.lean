import SszArm.CodecSerializeEntry
import SszArm.CodecMeasureContract
import SszArm.CodecEmitStack
import SszCodecEmitProofs

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value Error)
open SszNative.CodecMeasure (Plan)
open Delimited (Span Protected MemoryFrame)
open UintCodec (widthLoad)

abbrev Args := SszArm.Serialize.Args

namespace Args

abbrev ofEntry (s : ArmState) := SszArm.Serialize.Args.ofEntry s
abbrev bodySP (args : Args) := SszArm.Serialize.Args.bodySP args
abbrev plan (args : Args) := SszArm.Serialize.Args.plan args
abbrev measure (args : Args) := SszArm.Serialize.Args.measure args

end Args

def arenaOf (s : ArmState) (args : Args) : SszNative.Delimited.ArenaState :=
  Measure.arenaOf s args.measure

def measured (s : ArmState) (args : Args) (desc : Desc) (value : Value) :
    SszNative.CodecMeasure.Outcome Plan :=
  SszNative.CodecMeasure.measure desc value (arenaOf s args) true

def outcome (s : ArmState) (args : Args) (desc : Desc) (value : Value) :
    SszNative.CodecEmit.Written :=
  SszNative.CodecEmit.serialize desc value args.capacity.toNat (arenaOf s args)

def requiredStack (desc : Desc) : Nat :=
  stackBytes (Measure.stackBytes desc) (Emit.stackBytes desc)

def stackSpans (args : Args) (desc : Desc) : List Span :=
  Stack.envelope args.stack.toNat (requiredStack desc)

def externalSpans (args : Args) : List Span :=
  [(args.result.toNat, 72)] ++
    (if args.capacity.toNat = 0 then [] else [(args.output.toNat, args.capacity.toNat)])

def freeSpan (s : ArmState) (args : Args) : Span :=
  ((arenaOf s args).base + (arenaOf s args).used,
    (arenaOf s args).capacity - (arenaOf s args).used)

/-- Caller ownership covers the full free suffix, but no uninitialized byte is
read by the logical storage predicates. Failure need not have a valid cursor. -/
def envelope (s : ArmState) (args : Args) (desc : Desc) : List Span :=
  stackSpans args desc ++ externalSpans args ++
    ((args.arena.toNat + 16, 8) :: (if (freeSpan s args).2 = 0 then [] else [freeSpan s args]))

structure Owned (s : ArmState) (args : Args) (desc : Desc) (value : Value) : Prop where
  result : Storage.Physical args.result.toNat 72 8
  output : Storage.Physical args.output.toNat args.capacity.toNat 1
  arena : Storage.Physical args.arena.toNat 24 8
  storageBound : (arenaOf s args).base + (arenaOf s args).capacity ≤ 2^64
  nonnull : 0 < (arenaOf s args).capacity → 0 < (arenaOf s args).base
  stackLow : requiredStack desc ≤ args.stack.toNat
  resultStack : Protected (stackSpans args desc) args.result.toNat 72
  outputStack : Protected (stackSpans args desc) args.output.toNat args.capacity.toNat
  outputResult : Protected [(args.result.toNat, 72)] args.output.toNat args.capacity.toNat
  arenaOwned : Protected (stackSpans args desc ++ externalSpans args) args.arena.toNat 24
  freeOwned : Protected (stackSpans args desc ++ externalSpans args ++ [(args.arena.toNat, 24)])
    (freeSpan s args).1 (freeSpan s args).2
  descriptor : Storage.DescOwned (envelope s args desc) s args.descriptor.toNat desc
  value_at : Storage.ValueOwned (envelope s args desc) s args.value.toNat value

/-- Public calls cannot return private emitter bounds/index faults. This is an
observation in the conclusion, never a validation or measurement precondition. -/
def ResultAt (s : ArmState) (address : Nat) : Except SszNative.CodecEmit.Fault Nat → Prop
  | .ok count => widthLoad s address 8 = some count ∧ widthLoad s (address + 64) 4 = some 0
  | .error (.returned reason) => Measure.ErrorAt (widthLoad s) address reason
  | .error (.bounds _ _ _) | .error .fieldIndex => False

def resultWrites (args : Args) (first : SszNative.CodecMeasure.Outcome Plan)
    (final : SszNative.CodecEmit.Written) : List Span :=
  match first.result with
  | .error _ => [(args.result.toNat, 72)]
  | .ok _ => match final.result with
    | .ok _ => [(args.result.toNat, 8), (args.result.toNat + 64, 4)]
    | .error _ => [(args.result.toNat, 68)]

/-- Model write addresses are relative to the original caller output in
`serialize`; allocation effects remain at their absolute arena addresses. -/
def outputWrites (args : Args) (final : SszNative.CodecEmit.Written) : List Span :=
  final.writes.map fun write => (args.output.toNat + write.address, write.bytes.size)

def writesFor (s : ArmState) (args : Args) (desc : Desc) (value : Value) : List Span :=
  stackSpans args desc ++ resultWrites args (measured s args desc value) (outcome s args desc value) ++
    (outcome s args desc value).effects.flatMap (Measure.effectWrites args.arena.toNat) ++
    outputWrites args (outcome s args desc value)

def outputCount (result : Except SszNative.CodecEmit.Fault Nat) : Nat :=
  match result with | .ok count => count | .error _ => 0

structure Post (s t : ArmState) (desc : Desc) (value : Value) : Prop where
  returned : Delimited.Returned s t
  program : t.program = s.program
  result : ResultAt t (Args.ofEntry s).result.toNat (outcome s (Args.ofEntry s) desc value).result
  cursor : (read_mem_bytes 8 ((Args.ofEntry s).arena + 16#64) t).toNat =
    (outcome s (Args.ofEntry s) desc value).used
  header : read_mem_bytes 8 (Args.ofEntry s).arena t = read_mem_bytes 8 (Args.ofEntry s).arena s ∧
    read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) t =
      read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) s
  effects : ∀ effect ∈ (outcome s (Args.ofEntry s) desc value).effects, Measure.EffectAt t effect
  frame : MemoryFrame (writesFor s (Args.ofEntry s) desc value) s t
  bytes : ∀ count, (outcome s (Args.ofEntry s) desc value).result = .ok count →
    ∃ bytes, Ssz.serialize desc.erase value.erase = .ok bytes ∧ bytes.size = count ∧
      SszNative.ByteView.BytesAt (widthLoad t) (Args.ofEntry s).output.toNat bytes
  suffix : ∀ index, outputCount (outcome s (Args.ofEntry s) desc value).result ≤ index →
    index < (Args.ofEntry s).capacity.toNat →
    t.mem ((Args.ofEntry s).output + BitVec.ofNat 64 index) =
      s.mem ((Args.ofEntry s).output + BitVec.ofNat 64 index)
  descriptor : Storage.DescAt t (Args.ofEntry s).descriptor.toNat desc
  value_at : Storage.ValueAt t (Args.ofEntry s).value.toNat value

end SszArm.Codec.Serialize
