import SszArm.CodecMeasureContract
import SszArm.CodecMeasureSingletonActivation

set_option autoImplicit false

namespace SszArm.Codec.Measure.Singleton

open SszNative.CodecMeasure (Plan)
open Delimited (Span Protected MemoryFrame)

structure Args where
  result : BitVec 64
  arena : BitVec 64
  source : BitVec 64
  stack : BitVec 64

def Args.ofEntry (s : ArmState) : Args :=
  ⟨r (.GPR 0) s, r (.GPR 1) s, r (.GPR 2) s, r (.GPR 31) s⟩

def arenaOf (s : ArmState) (args : Args) : SszNative.Delimited.ArenaState :=
  ⟨(read_mem_bytes 8 args.arena s).toNat,
    (read_mem_bytes 8 (args.arena + 8#64) s).toNat,
    (read_mem_bytes 8 (args.arena + 16#64) s).toNat⟩

def reservation (s : ArmState) (args : Args) : Option SszNative.Arena.Reservation :=
  SszNative.Arena.reserve (arenaOf s args).base (arenaOf s args).capacity (arenaOf s args).used 5

def stackWrites (args : Args) : List Span := [(args.stack.toNat - 48, 48)]

def localEnvelope (args : Args) : List Span := stackWrites args ++ [(args.result.toNat, 72)]

def envelope (s : ArmState) (args : Args) : List Span :=
  localEnvelope args ++ ((args.arena.toNat + 16, 8) ::
    (if (arenaOf s args).capacity - (arenaOf s args).used = 0 then [] else
      [((arenaOf s args).base + (arenaOf s args).used,
        (arenaOf s args).capacity - (arenaOf s args).used)]))

def resultWrites (args : Args) : Option SszNative.Arena.Reservation → List Span
  | none => [(args.result.toNat, 68)]
  | some _ => [(args.result.toNat, 16), (args.result.toNat + 64, 4)]

def allocationWrites (args : Args) : Option SszNative.Arena.Reservation → List Span
  | none => []
  | some allocation => [(args.arena.toNat + 16, 8), (allocation.pointer, 40)]

def writesFor (s : ArmState) (args : Args) : List Span :=
  stackWrites args ++ resultWrites args (reservation s args) ++ allocationWrites args (reservation s args)

def ResultAt (s : ArmState) (address : Nat) (plan : Plan) :
    Option SszNative.Arena.Reservation → Prop
  | none => ErrorAt (UintCodec.widthLoad s) address (.primitive (.arithmetic .scratchExhausted))
  | some allocation =>
      UintCodec.widthLoad s address 8 = some allocation.pointer ∧
      UintCodec.widthLoad s (address + 8) 8 = some 1 ∧
      UintCodec.widthLoad s (address + 64) 4 = some 0 ∧ Storage.PlanAt s allocation.pointer plan

structure Owned (s : ArmState) (args : Args) (plan : Plan) : Prop where
  resultPhysical : Storage.Physical args.result.toNat 72 8
  arenaPhysical : Storage.Physical args.arena.toNat 24 8
  storageBound : (arenaOf s args).base + (arenaOf s args).capacity ≤ 2^64
  nonnull : 0 < (arenaOf s args).capacity → 0 < (arenaOf s args).base
  stackLow : 48 ≤ args.stack.toNat
  resultStack : Protected (stackWrites args) args.result.toNat 72
  headerLocal : Protected (localEnvelope args) args.arena.toNat 24
  freeLocal : Protected (localEnvelope args ++ [(args.arena.toNat, 24)])
    ((arenaOf s args).base + (arenaOf s args).used)
    ((arenaOf s args).capacity - (arenaOf s args).used)
  source : Storage.PlanOwned (envelope s args) s args.source.toNat plan

structure Post (s t : ArmState) (plan : Plan) : Prop where
  returned : Delimited.Returned s t
  program : t.program = s.program
  result : ResultAt t (Args.ofEntry s).result.toNat plan (reservation s (Args.ofEntry s))
  cursor : (read_mem_bytes 8 ((Args.ofEntry s).arena + 16#64) t).toNat =
    match reservation s (Args.ofEntry s) with
    | none => (arenaOf s (Args.ofEntry s)).used
    | some allocation => allocation.used
  header : read_mem_bytes 8 (Args.ofEntry s).arena t = read_mem_bytes 8 (Args.ofEntry s).arena s ∧
    read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) t = read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) s
  frame : MemoryFrame (writesFor s (Args.ofEntry s)) s t
  source : Storage.PlanAt t (Args.ofEntry s).source.toNat plan

end SszArm.Codec.Measure.Singleton
