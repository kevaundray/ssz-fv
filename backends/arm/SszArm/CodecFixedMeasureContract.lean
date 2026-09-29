import SszArm.CodecFixedStack
import SszArm.CodecStorageTypes
import SszArm.CodecStack
import SszArm.MeasureContract
import SszFixedSizeProofs
import SszFixedSizeResources

namespace SszArm.Codec.Fixed.MeasureFixed

open SszNative (NatOperand)
open SszNative.Codec (Desc)
open SszNative.Serialize (Outcome Error)
open Delimited (Span Protected MemoryFrame Returned)
open UintCodec (widthLoad)

structure Args where
  result : BitVec 64
  descriptor : BitVec 64
  arena : BitVec 64
  stack : BitVec 64

def Args.ofEntry (s : ArmState) : Args :=
  ⟨r (.GPR 0#5) s, r (.GPR 1#5) s, r (.GPR 2#5) s, r (.GPR 31#5) s⟩

def Args.bodySP (args : Args) : BitVec 64 := args.stack - 160#64

def arenaOf (s : ArmState) (args : Args) : SszNative.Delimited.ArenaState :=
  ⟨(read_mem_bytes 8 args.arena s).toNat,
    (read_mem_bytes 8 (args.arena + 8#64) s).toNat,
    (read_mem_bytes 8 (args.arena + 16#64) s).toNat⟩

def outcome (s : ArmState) (args : Args) (desc : Desc) : Outcome (Option NatOperand) :=
  SszNative.FixedSize.measureFixed desc (arenaOf s args)

/-- Rust Result<Option<Nat>> uses the option word at +0, the exact Nat header
at +8/+16, and the NativeError status at +64. No inactive padding is observed. -/
def ResultAt (observe : Nat → Nat → Option Nat) (address : Nat) :
    Except Error (Option NatOperand) → Prop
  | .ok none => observe address 8 = some 0 ∧ observe (address + 64) 4 = some 0
  | .ok (some width) => observe address 8 = some 1 ∧
      SszNative.NatArithmetic.operandAt observe (address + 8) width ∧
      observe (address + 64) 4 = some 0
  | .error reason => Measure.ErrorAt observe address reason

def stackWrites (args : Args) (desc : Desc) : List Span :=
  Stack.envelope args.stack.toNat (measureFixedStack desc)

def resultWrites (args : Args) (measured : Outcome (Option NatOperand)) : List Span :=
  match measured.result with
  | .ok none => [(args.result.toNat, 8), (args.result.toNat + 64, 4)]
  | .ok (some _) => [(args.result.toNat, 24), (args.result.toNat + 64, 4)]
  | .error _ => [(args.result.toNat, 72)]

def allocationWrites (args : Args) (measured : Outcome (Option NatOperand)) : List Span :=
  measured.calls.flatMap fun call => match call.allocation with
    | none => []
    | some reservation =>
      [(args.arena.toNat + 16, 8), (reservation.pointer, 8 * call.written.length)]

def writesFor (args : Args) (desc : Desc) (measured : Outcome (Option NatOperand)) : List Span :=
  stackWrites args desc ++ resultWrites args measured ++ allocationWrites args measured

/-- The original storage envelope is independent of successful arithmetic.
Arena prefix, alignment gaps, and free suffix are tracked separately by Post. -/
def localEnvelope (args : Args) (desc : Desc) : List Span :=
  stackWrites args desc ++ [(args.result.toNat, 72)]

def freeEnvelope (s : ArmState) (args : Args) : List Span :=
  if (arenaOf s args).used < (arenaOf s args).capacity then
    [((arenaOf s args).base + (arenaOf s args).used,
      (arenaOf s args).capacity - (arenaOf s args).used)]
  else []

def mutableEnvelope (s : ArmState) (args : Args) (desc : Desc) : List Span :=
  localEnvelope args desc ++ [(args.arena.toNat + 16, 8)] ++ freeEnvelope s args

structure Owned (s : ArmState) (desc : Desc) : Prop where
  stack : measureFixedStack desc ≤ (Args.ofEntry s).stack.toNat
  resultBound : (Args.ofEntry s).result.toNat + 72 ≤ 2^64
  resultStack : Protected (stackWrites (Args.ofEntry s) desc) (Args.ofEntry s).result.toNat 72
  arenaBound : (Args.ofEntry s).arena.toNat + 24 ≤ 2^64
  storageBound : (arenaOf s (Args.ofEntry s)).base + (arenaOf s (Args.ofEntry s)).capacity ≤ 2^64
  nonnull : 0 < (arenaOf s (Args.ofEntry s)).capacity → 0 < (arenaOf s (Args.ofEntry s)).base
  headerLocal : Protected (localEnvelope (Args.ofEntry s) desc) (Args.ofEntry s).arena.toNat 24
  freeLocal : Protected (localEnvelope (Args.ofEntry s) desc ++ [((Args.ofEntry s).arena.toNat, 24)])
    ((arenaOf s (Args.ofEntry s)).base + (arenaOf s (Args.ofEntry s)).used)
    ((arenaOf s (Args.ofEntry s)).capacity - (arenaOf s (Args.ofEntry s)).used)
  descriptor : Storage.DescOwned (mutableEnvelope s (Args.ofEntry s) desc) s
    (Args.ofEntry s).descriptor.toNat desc

structure Post (s t : ArmState) (desc : Desc) : Prop where
  returned : Returned s t
  program : t.program = s.program
  result : ResultAt (widthLoad t) (Args.ofEntry s).result.toNat
    (outcome s (Args.ofEntry s) desc).result
  cursor : (read_mem_bytes 8 ((Args.ofEntry s).arena + 16#64) t).toNat =
    (outcome s (Args.ofEntry s) desc).used
  written : ∀ call ∈ (outcome s (Args.ofEntry s) desc).calls, NatDivision.WrittenAt (widthLoad t) call
  frame : MemoryFrame (writesFor (Args.ofEntry s) desc (outcome s (Args.ofEntry s) desc)) s t
  arenaBase : read_mem_bytes 8 (Args.ofEntry s).arena t = read_mem_bytes 8 (Args.ofEntry s).arena s
  arenaCapacity : read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) t =
    read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) s

theorem Post.used_mono {s t : ArmState} {desc : Desc} (post : Post s t desc) :
    (arenaOf s (Args.ofEntry s)).used ≤
      (read_mem_bytes 8 ((Args.ofEntry s).arena + 16#64) t).toNat := by
  rw [post.cursor]
  exact SszNative.FixedSize.measureFixed_used_mono desc _

theorem Post.refines {s t : ArmState} {desc : Desc} (post : Post s t desc) :
    (outcome s (Args.ofEntry s) desc).result.map (Option.map NatOperand.value) =
        .ok desc.erase.fixedSize ∨
      (outcome s (Args.ofEntry s) desc).result = .error (.arithmetic .scratchExhausted) := by
  cases measured : (outcome s (Args.ofEntry s) desc).result with
  | ok width =>
    left
    simp only [Except.map]
    exact congrArg Except.ok (SszNative.FixedSize.measureFixed_success desc _ width measured)
  | error reason =>
    right
    rw [SszNative.FixedSize.measureFixed_error desc _ reason measured]

end SszArm.Codec.Fixed.MeasureFixed
