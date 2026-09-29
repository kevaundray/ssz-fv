import SszArm.CodecEmitStack
import SszArm.CodecStorageLegacy
import SszArm.EmitProgram
import SszCodecEmitProofs

namespace SszArm.Codec.Emit

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure (Plan)
open Delimited (Span Protected MemoryFrame)

structure Args where
  result : BitVec 64
  descriptor : BitVec 64
  value : BitVec 64
  plan : BitVec 64
  output : BitVec 64
  capacity : BitVec 64
  stack : BitVec 64

def Args.ofEntry (s : ArmState) : Args :=
  ⟨r (.GPR 0#5) s, r (.GPR 1#5) s, r (.GPR 2#5) s, r (.GPR 3#5) s,
   r (.GPR 4#5) s, r (.GPR 5#5) s, r (.GPR 31#5) s⟩

def Args.primitive (args : Args) : SszArm.Emit.Args :=
  ⟨args.result, args.descriptor, args.value, args.output, args.capacity, args.stack⟩

def Args.out (args : Args) : SszNative.CodecEmit.Slice :=
  ⟨args.output.toNat, args.capacity.toNat⟩

def stackWrites (args : Args) (desc : Desc) : List Span :=
  Stack.envelope args.stack.toNat (stackBytes desc)

def resultWrites (args : Args) : List Span :=
  [(args.result.toNat, 8), (args.result.toNat + 64, 4)]

def writesFor (args : Args) (desc : Desc) (size : Nat) : List Span :=
  stackWrites args desc ++ resultWrites args ++
    (if size = 0 then [] else [(args.output.toNat, size)])

/-- The emitter reads only retained children and a leading width when children
exist. Discarded fixed child plans are logical witnesses, not runtime storage. -/
structure PlanValid (desc : Desc) (value : Value) (retain : Bool)
    (measured : Plan) (supplied : Option Plan) : Prop where
  generated : SszNative.CodecEmit.Generated desc value retain measured
  usable : retain = true ∨ SszNative.FixedSize.isFixed desc = true
  children : SszNative.CodecEmit.children supplied = measured.children
  leading : measured.children ≠ [] → SszNative.CodecEmit.leading supplied = measured.leading

theorem measured_valid (desc : Desc) (value : Value)
    (arena : SszNative.Delimited.ArenaState) (physical : value.Physical) (plan : Plan)
    (measured : (SszNative.CodecMeasure.measure desc value arena true).result = .ok plan) :
    PlanValid desc value true plan (some plan) :=
  ⟨SszNative.CodecEmit.measure_generated desc value arena true physical plan measured,
    Or.inl rfl, rfl, fun _ => rfl⟩

def PlanAt (s : ArmState) (pointer : BitVec 64) : Option Plan → Prop
  | none => pointer = 0#64
  | some plan => pointer ≠ 0#64 ∧ Storage.PlanAt s pointer.toNat plan

def PlanOwned (writes : List Span) (s : ArmState) (pointer : BitVec 64) : Option Plan → Prop
  | none => pointer = 0#64
  | some plan => pointer ≠ 0#64 ∧ Storage.PlanOwned writes s pointer.toNat plan

theorem plan_at {writes s pointer supplied} (owned : PlanOwned writes s pointer supplied) :
    PlanAt s pointer supplied := by
  cases supplied with
  | none => exact owned
  | some plan => exact ⟨owned.1, Storage.plan_at owned.2⟩

theorem plan_preserved {writes s t pointer supplied}
    (owned : PlanOwned writes s pointer supplied) (frame : MemoryFrame writes s t) :
    PlanOwned writes t pointer supplied := by
  cases supplied with
  | none => exact owned
  | some plan => exact ⟨owned.1, Storage.plan_preserved owned.2 frame⟩

/-- Private generated-plan precondition. Public serialization derives validity
from its completed measurement; it is not a public validation assumption. All
remaining hypotheses describe only entry memory and physical separation. -/
structure Owned (s : ArmState) (args : Args) (desc : Desc) (value : Value)
    (retain : Bool) (measured : Plan) (supplied : Option Plan) : Prop where
  valid : PlanValid desc value retain measured supplied
  fitting : measured.size.value ≤ args.capacity.toNat
  physical : value.Physical
  stackLow : stackBytes desc ≤ args.stack.toNat
  resultBound : args.result.toNat + 72 ≤ 2 ^ 64
  outputBound : args.output.toNat + args.capacity.toNat ≤ 2 ^ 64
  resultStack : Protected (stackWrites args desc) args.result.toNat 72
  outputStack : Protected (stackWrites args desc) args.output.toNat args.capacity.toNat
  outputResult : Protected (resultWrites args) args.output.toNat args.capacity.toNat
  descriptor : Storage.DescOwned (writesFor args desc measured.size.value)
    s args.descriptor.toNat desc
  value_at : Storage.ValueOwned (writesFor args desc measured.size.value)
    s args.value.toNat value
  plan : PlanOwned (writesFor args desc measured.size.value) s args.plan supplied

/-- Total ARM memory is observed only at physical addresses in the postcondition.
The function is also a suitable old-memory argument to the checked write model. -/
def byteMemory (s : ArmState) (address : Nat) : Option UInt8 :=
  some (UInt8.ofBitVec (read_mem_bytes 1 (BitVec.ofNat 64 address) s))

/-- Match the checked ordered write list on the complete caller output slice.
No unbounded Nat addresses are quantified: the physical output bound makes
every observed offset injective into the actual 64-bit address space. -/
def OutputMatches (s t : ArmState) (args : Args) (desc : Desc) (value : Value)
    (supplied : Option Plan) : Prop :=
  ∀ index, index < args.capacity.toNat →
    byteMemory t (args.output.toNat + index) =
      SszNative.CodecEmit.applyWrites (byteMemory s)
        (SszNative.CodecEmit.emit desc value supplied args.out).writes
        (args.output.toNat + index)

structure Post (s t : ArmState) (desc : Desc) (value : Value)
    (measured : Plan) (supplied : Option Plan) : Prop where
  returned : SszArm.Emit.Returned s t
  length : read_mem_bytes 8 (Args.ofEntry s).result t = BitVec.ofNat 64 measured.size.value
  status : read_mem_bytes 4 ((Args.ofEntry s).result + 64#64) t = 0#32
  output : OutputMatches s t (Args.ofEntry s) desc value supplied
  frame : MemoryFrame (writesFor (Args.ofEntry s) desc measured.size.value) s t
  descriptor : Storage.DescOwned (writesFor (Args.ofEntry s) desc measured.size.value)
    t (Args.ofEntry s).descriptor.toNat desc
  value_at : Storage.ValueOwned (writesFor (Args.ofEntry s) desc measured.size.value)
    t (Args.ofEntry s).value.toNat value
  plan : PlanOwned (writesFor (Args.ofEntry s) desc measured.size.value)
    t (Args.ofEntry s).plan supplied

theorem valid_success (desc : Desc) (value : Value) (retain : Bool)
    (measured : Plan) (supplied : Option Plan) (args : Args)
    (valid : PlanValid desc value retain measured supplied)
    (fitting : measured.size.value ≤ args.capacity.toNat) :
    (SszNative.CodecEmit.emit desc value supplied args.out).result = .ok measured.size.value :=
  SszNative.CodecEmit.generated_emit_success desc value retain measured supplied args.out
    valid.generated valid.usable valid.children valid.leading fitting args.capacity.isLt

/-- A generated plan's exact byte refinement transfers through the ISA's
pointwise ordered-write postcondition, independently of old output contents. -/
theorem Post.initialized {s t : ArmState} {desc : Desc} {value : Value}
    {retain : Bool} {measured : Plan} {supplied : Option Plan}
    (post : Post s t desc value measured supplied)
    (owned : Owned s (Args.ofEntry s) desc value retain measured supplied)
    (bytes : Ssz.Bytes) (semantic : Ssz.serialize desc.erase value.erase = .ok bytes)
    (index : Nat) (inside : index < bytes.size)
    (size : bytes.size = measured.size.value) :
    byteMemory t ((Args.ofEntry s).output.toNat + index) = some bytes[index] := by
  have encoded := SszNative.CodecEmit.generated_emit_encodes desc value retain measured
    supplied (Args.ofEntry s).out bytes owned.valid.generated owned.valid.usable
    owned.valid.children owned.valid.leading owned.fitting (Args.ofEntry s).capacity.isLt semantic
  rw [post.output index (by omega)]
  exact encoded.initialized (byteMemory s) index inside

theorem Post.suffix {s t : ArmState} {desc : Desc} {value : Value}
    {measured : Plan} {supplied : Option Plan}
    (post : Post s t desc value measured supplied)
    (bytes : Ssz.Bytes) (encoded : SszNative.CodecEmit.Encodes
      (SszNative.CodecEmit.emit desc value supplied (Args.ofEntry s).out).writes
      (Args.ofEntry s).output.toNat bytes)
    (index : Nat) (outside : bytes.size ≤ index)
    (inside : index < (Args.ofEntry s).capacity.toNat) :
    byteMemory t ((Args.ofEntry s).output.toNat + index) =
      byteMemory s ((Args.ofEntry s).output.toNat + index) := by
  rw [post.output index inside]
  exact encoded.frame (byteMemory s) _ (Or.inr (by omega))

end SszArm.Codec.Emit
