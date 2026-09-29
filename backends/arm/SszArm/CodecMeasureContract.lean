import SszArm.CodecMeasureStack
import SszArm.CodecMeasureError
import SszArm.CodecStorageModels
import SszArm.CodecStack

set_option autoImplicit false

namespace SszArm.Codec.Measure

open SszNative (NatOperand)
open SszNative.Codec (Desc Value Error)
open SszNative.CodecMeasure (Plan Effect)
open Delimited (Span Protected MemoryFrame)

abbrev Args := SszArm.Measure.Args

namespace Args

abbrev ofEntry := SszArm.Measure.Args.ofEntry
abbrev bodySP := SszArm.Measure.Args.bodySP

end Args

def arenaOf (s : ArmState) (args : Args) : SszNative.Delimited.ArenaState :=
  SszArm.Measure.arenaOf s args

def outcome (s : ArmState) (args : Args) (desc : Desc) (value : Value) :
    SszNative.CodecMeasure.Outcome Plan :=
  SszNative.CodecMeasure.measure desc value (arenaOf s args) (args.retain == 1#8)

def ResultAt (s : ArmState) (address : Nat) : Except Error Plan → Prop
  | .ok plan => Storage.PlanAt s address plan ∧
      UintCodec.widthLoad s (address + 64) 4 = some 0
  | .error reason => ErrorAt (UintCodec.widthLoad s) address reason

def stackWrites (args : Args) (desc : Desc) : List Span :=
  Stack.envelope args.stack.toNat (stackBytes desc)

def localEnvelope (args : Args) (desc : Desc) : List Span :=
  stackWrites args desc ++ [(args.result.toNat, 72)]

/-- Original-state writable ownership. It grants no initialization, allocation
success, valid cursor, or future helper outcome. -/
def envelope (s : ArmState) (args : Args) (desc : Desc) : List Span :=
  localEnvelope args desc ++ ((args.arena.toNat + 16, 8) ::
    (if (arenaOf s args).capacity - (arenaOf s args).used = 0 then [] else
      [((arenaOf s args).base + (arenaOf s args).used,
        (arenaOf s args).capacity - (arenaOf s args).used)]))

def arithmeticWrites (arena : Nat) {α : Type}
    (call : SszNative.NatArithmetic.Outcome α) : List Span :=
  match call.allocation with
  | none => []
  | some allocation => [(arena + 16, 8), (allocation.pointer, 8 * call.written.length)]

/-- Only committed cursor words, initialized limbs and initialized Plan slots
are included. Failed attempts, allocation gaps and untouched suffixes are not. -/
def effectWrites (arena : Nat) : Effect → List Span
  | .primitive _ _ _ measured => measured.calls.flatMap (arithmeticWrites arena)
  | .arithmetic _ _ _ call => arithmeticWrites arena call
  | .reservePlans count _ reservation =>
      if count = 0 then [] else
        match reservation with | none => [] | some _ => [(arena + 16, 8)]
  | .writePlan address _ _ => [(address, 40)]

def resultWrites (args : Args) (result : Except Error Plan) : List Span :=
  match result with
  | .ok _ => [(args.result.toNat, 40), (args.result.toNat + 64, 4)]
  | .error _ => [(args.result.toNat, 72)]

def writesFor (args : Args) (desc : Desc)
    (measured : SszNative.CodecMeasure.Outcome Plan) : List Span :=
  stackWrites args desc ++ resultWrites args measured.result ++
    measured.effects.flatMap (effectWrites args.arena.toNat)

/-- Persistent meaningful observations of each committed effect. Plan slots
include the recursive child storage needed by the real emitter. -/
def EffectAt (s : ArmState) : Effect → Prop
  | .primitive _ _ _ measured =>
      ∀ call ∈ measured.calls, NatDivision.WrittenAt (UintCodec.widthLoad s) call
  | .arithmetic _ _ _ call => NatDivision.WrittenAt (UintCodec.widthLoad s) call
  | .reservePlans _ _ _ => True
  | .writePlan address _ plan => Storage.PlanAt s address plan

structure Owned (s : ArmState) (args : Args) (desc : Desc) (value : Value) : Prop where
  retain : args.retain = 0#8 ∨ args.retain = 1#8
  result : Storage.Physical args.result.toNat 72 8
  arena : Storage.Physical args.arena.toNat 24 8
  storageBound : (arenaOf s args).base + (arenaOf s args).capacity ≤ 2^64
  nonnull : 0 < (arenaOf s args).capacity → 0 < (arenaOf s args).base
  stackLow : stackBytes desc ≤ args.stack.toNat
  resultStack : Protected (stackWrites args desc) args.result.toNat 72
  headerLocal : Protected (localEnvelope args desc) args.arena.toNat 24
  freeLocal : Protected (localEnvelope args desc ++ [(args.arena.toNat, 24)])
    ((arenaOf s args).base + (arenaOf s args).used)
    ((arenaOf s args).capacity - (arenaOf s args).used)
  descriptor : Storage.DescOwned (envelope s args desc) s args.descriptor.toNat desc
  value_at : Storage.ValueOwned (envelope s args desc) s args.value.toNat value

structure Post (s t : ArmState) (desc : Desc) (value : Value) : Prop where
  returned : Delimited.Returned s t
  program : t.program = s.program
  result : ResultAt t (Args.ofEntry s).result.toNat
    (outcome s (Args.ofEntry s) desc value).result
  cursor : (read_mem_bytes 8 ((Args.ofEntry s).arena + 16#64) t).toNat =
    (outcome s (Args.ofEntry s) desc value).used
  header : read_mem_bytes 8 (Args.ofEntry s).arena t =
      read_mem_bytes 8 (Args.ofEntry s).arena s ∧
    read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) t =
      read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) s
  effects : ∀ effect ∈ (outcome s (Args.ofEntry s) desc value).effects, EffectAt t effect
  frame : MemoryFrame
    (writesFor (Args.ofEntry s) desc (outcome s (Args.ofEntry s) desc value)) s t
  descriptor : Storage.DescAt t (Args.ofEntry s).descriptor.toNat desc
  value_at : Storage.ValueAt t (Args.ofEntry s).value.toNat value

end SszArm.Codec.Measure
