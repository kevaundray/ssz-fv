import SszCodecMeasureOrder
import SszSerializeProofs

set_option autoImplicit false

namespace SszNative.CodecEmit

open Codec (Desc Value Error)
open CodecMeasure (Plan Parts)

/-- Private Rust slice/index failures are distinct from returned codec errors.
Public entry points discharge these alternatives from generated plans. The
totalization is not a model of exact pre-panic partial writes for invalid private
calls: contiguous primitive writes are abstracted as a chunk. Actual public
measurement supplies sufficient slices, where the abstraction is exact. -/
inductive Fault where
  | returned (reason : Error)
  | bounds (available start count : Nat)
  | fieldIndex

structure Slice where
  address : Nat
  length : Nat

/-- A copy is addressed, ordered, and independent of the old output contents. -/
structure Write where
  address : Nat
  bytes : Ssz.Bytes

structure Emitted (α : Type) where
  result : Except Fault α
  writes : List Write

def pure {α : Type} (value : α) : Emitted α := ⟨.ok value, []⟩
def fail {α : Type} (reason : Fault) : Emitted α := ⟨.error reason, []⟩

def bind {α β : Type} (first : Emitted α) (next : α → Emitted β) : Emitted β :=
  match first.result with
  | .error reason => ⟨.error reason, first.writes⟩
  | .ok value =>
    let second := next value
    ⟨second.result, first.writes ++ second.writes⟩

def returned {α : Type} (result : Except Error α) : Emitted α :=
  ⟨result.mapError Fault.returned, []⟩

def sub (out : Slice) (start count : Nat) : Emitted Slice :=
  if start + count ≤ out.length then pure ⟨out.address + start, count⟩
  else fail (.bounds out.length start count)

def suffix (out : Slice) (start : Nat) : Emitted Slice :=
  if start ≤ out.length then pure ⟨out.address + start, out.length - start⟩
  else fail (.bounds out.length start 0)

def copy (out : Slice) (bytes : Ssz.Bytes) : Emitted Nat :=
  if bytes.size ≤ out.length then ⟨.ok bytes.size, [⟨out.address, bytes⟩]⟩
  else fail (.bounds out.length 0 bytes.size)

/-- The private emitter converts only uint width. In particular this does not
repeat primitive measurement or reserve arena storage. Primitive contiguous
writes use the existing limb/packed-bit emission abstraction. -/
def primitive (desc : Serialize.Desc) (value : Value) (out : Slice) : Emitted Nat :=
  match desc, value with
  | .bool, .bool _ => copy out (Serialize.emit desc value.toPrimitive)
  | .uint width, .uint _ =>
    bind (returned (CodecMeasure.hostSize width 0).result) fun _ =>
      copy out (Serialize.emit desc value.toPrimitive)
  | .byteVector _, .bytes _ | .byteList _, .bytes _ =>
    copy out (Serialize.emit desc value.toPrimitive)
  | .bitVector _, .bits _ | .bitList _, .bits _ | .progressiveBitList _, .bits _ =>
    copy out (Serialize.emit desc value.toPrimitive)
  | _, _ => fail (.returned (.primitive .wrongType))

def nextPart : Parts → Emitted (Desc × Parts)
  | .repeated element => pure (element, .repeated element)
  | .fields [] => fail .fieldIndex
  | .fields ((_, desc) :: rest) => pure (desc, .fields rest)

def inline : Parts → Desc → Bool
  | .repeated _, _ => false
  | .fields _, desc => FixedSize.isFixed desc

abbrev Visit (values : List Value) :=
  (value : Value) → value ∈ values → Desc → Option Plan → Slice → Emitted Nat

/-- Empty retained children select the sequential loop, not an empty zip.
Every actual value is visited with no child plan and the remaining suffix. -/
def sequential (parts : Parts) (values : List Value) (visit : Visit values)
    (out : Slice) (position : Nat) : Emitted Nat :=
  match values with
  | [] => pure position
  | value :: rest =>
    bind (nextPart parts) fun entry =>
      bind (suffix out position) fun target =>
        bind (visit value (by simp) entry.1 none target) fun size =>
          sequential entry.2 rest
            (fun value member => visit value (List.mem_cons_of_mem _ member))
            out (position + size)
termination_by values.length

/-- The zip stops at either list. Each host-size conversion precedes that
child's slice checks and writes. Offset bytes precede the corresponding body. -/
def table (parts : Parts) (values : List Value) (visit : Visit values)
    (children : List Plan) (out : Slice) (head body : Nat) : Emitted Nat :=
  match values, children with
  | [], _ | _, [] => pure body
  | value :: rest, child :: children =>
    bind (nextPart parts) fun entry =>
      bind (returned (CodecMeasure.hostSize child.size 0).result) fun size =>
        if inline parts entry.1 then
          bind (sub out head size) fun target =>
            bind (visit value (by simp) entry.1 (some child) target) fun _ =>
              table entry.2 rest
                (fun value member => visit value (List.mem_cons_of_mem _ member))
                children out (head + size) body
        else
          bind (sub out head 4) fun target =>
            bind (copy target (Ssz.uintBytes 4 body)) fun _ =>
              bind (sub out body size) fun target =>
                bind (visit value (by simp) entry.1 (some child) target) fun _ =>
                  table entry.2 rest
                    (fun value member => visit value (List.mem_cons_of_mem _ member))
                    children out (head + 4) (body + size)
termination_by values.length

def children (plan : Option Plan) : List Plan :=
  match plan with
  | none => []
  | some plan => plan.children

def leading (plan : Option Plan) : Nat :=
  match plan with
  | none => 0
  | some plan => plan.leading

def emitParts (parts : Parts) (values : List Value) (visit : Visit values)
    (plan : Option Plan) (out : Slice) : Emitted Nat :=
  if (children plan).isEmpty then sequential parts values visit out 0
  else table parts values visit (children plan) out 0 (leading plan)

def emitStep (desc : Desc) (value : Value) (plan : Option Plan) (out : Slice)
    (visit : Visit value.children) : Emitted Nat :=
  match desc, value with
  | .primitive shape, value => primitive shape value out
  | .vector element _, .seq values | .list element _, .seq values
    | .progressiveList element _, .seq values =>
    emitParts (.repeated element) values visit plan out
  | .container fields, .seq values | .progressiveContainer _ fields, .seq values =>
    emitParts (.fields fields) values visit plan out
  | .compatibleUnion variants, .union selector value =>
    bind (copy out #[UInt8.ofNat selector.value]) fun _ =>
      bind (returned (CodecMeasure.option variants selector)) fun chosen =>
        bind (suffix out 1) fun target =>
          bind (visit value (by simp [Value.children]) chosen (children plan).head? target)
            fun size => pure (1 + size)
  | _, _ => fail (.returned (.primitive .wrongType))

def emit (desc : Desc) (value : Value) (plan : Option Plan) (out : Slice) : Emitted Nat :=
  emitStep desc value plan out
    (fun child _ desc plan out => emit desc child plan out)
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

structure Written where
  result : Except Fault Nat
  used : Nat
  effects : List CodecMeasure.Effect
  writes : List Write

/-- Public caller-output entry point. The emitter sees exactly the measured
prefix, never the full caller capacity. All preceding errors have no writes. -/
def serialize (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) : Written :=
  let measured := CodecMeasure.measure desc value arena true
  match measured.result with
  | .error reason => ⟨.error (.returned reason), measured.used, measured.effects, []⟩
  | .ok plan =>
    match (CodecMeasure.hostSize plan.size measured.used).result with
    | .error reason => ⟨.error (.returned reason), measured.used, measured.effects, []⟩
    | .ok size =>
      if size ≤ capacity then
        let emitted := emit desc value (some plan) ⟨0, size⟩
        ⟨emitted.result, measured.used, measured.effects, emitted.writes⟩
      else ⟨.error (.returned (.primitive .outputTooSmall)), measured.used, measured.effects, []⟩

structure Allocated where
  written : Written
  /-- None means the byte allocator was not called; some (_, none) records its failure. -/
  reservation : Option (Nat × Option Arena.Reservation)

/-- Final byte storage is allocated after all retained measurement effects.
The zero-size allocation retains the shared allocator's dangling pointer one. -/
def serializeAlloc (desc : Desc) (value : Value) (arena : Delimited.ArenaState) : Allocated :=
  let measured := CodecMeasure.measure desc value arena true
  match measured.result with
  | .error reason => ⟨⟨.error (.returned reason), measured.used, measured.effects, []⟩, none⟩
  | .ok plan =>
    match (CodecMeasure.hostSize plan.size measured.used).result with
    | .error reason => ⟨⟨.error (.returned reason), measured.used, measured.effects, []⟩, none⟩
    | .ok size =>
      match Arena.reserveBytes arena.base arena.capacity measured.used size with
      | none =>
        ⟨⟨.error (.returned (.primitive (.arithmetic .scratchExhausted))),
          measured.used, measured.effects, []⟩, some (size, none)⟩
      | some reservation =>
        let emitted := emit desc value (some plan) ⟨reservation.pointer, size⟩
        ⟨⟨emitted.result, reservation.used, measured.effects, emitted.writes⟩,
          some (size, some reservation)⟩

/-- Evaluation never consults an old cell covered by a copy. -/
def applyWrite (before : Nat → Option UInt8) (write : Write) : Nat → Option UInt8 :=
  fun address =>
    if write.address ≤ address ∧ address < write.address + write.bytes.size then
      write.bytes[address - write.address]?
    else before address

def applyWrites (before : Nat → Option UInt8) (writes : List Write) : Nat → Option UInt8 :=
  writes.foldl applyWrite before

/-- Exact initialized bytes together with an arbitrary untouched exterior. -/
def Encodes (writes : List Write) (address : Nat) (bytes : Ssz.Bytes) : Prop :=
  ∀ before, applyWrites before writes = applyWrite before ⟨address, bytes⟩

end SszNative.CodecEmit
