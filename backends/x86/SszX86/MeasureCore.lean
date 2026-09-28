import SszX86.MeasureDecode
import SszX86.EmitOwned
import SszX86.NatFromU128Corollaries
import SszSerializeResources

namespace SszX86.Measure
open SszNative SszNative.Serialize UintCodec

abbrev NatAt := Emit.NatAt
abbrev BytesAt := Emit.BytesAt
abbrev MemoryFrame := Emit.MemoryFrame
abbrev InSpan := Emit.InSpan
abbrev DescAt := Emit.DescAt
abbrev ValueAt := Emit.ValueAt
abbrev descTag := Emit.descTag
abbrev valueTag := Emit.valueTag
abbrev descBytes := Emit.descBytes
abbrev valueBytes := Emit.valueBytes
abbrev DescBorrowed := Emit.DescBorrowed
abbrev ValueBorrowed := Emit.ValueBorrowed

/-- Private Result<Plan, Error>: only the five live Plan fields are observed.
The empty children slice is the aligned dangling pointer eight, not an allocation. -/
def PlanAt (observe : Nat → Nat → Option Nat) (out : Nat) (operand : NatOperand) : Prop :=
  observe out 8 = some 8 ∧ observe (out + 8) 8 = some 0 ∧
  NatArithmetic.operandAt observe (out + 16) operand ∧
  observe (out + 32) 8 = some 0 ∧ observe (out + 64) 4 = some 0

/-- The semantic errors use the same checked private NativeError representation
as NatArithmetic.errorAt, retaining both represented Nat arguments exactly. -/
def SemanticErrorAt (observe : Nat → Nat → Option Nat) (out code : Nat)
    (expected actual : NatOperand) : Prop :=
  observe out 8 = some 1 ∧ observe (out + 8) 8 = some 0 ∧
  NatArithmetic.operandAt observe (out + 16) expected ∧
  NatArithmetic.operandAt observe (out + 32) actual ∧
  observe (out + 48) 8 = some 0 ∧ observe (out + 56) 8 = some 0 ∧
  observe (out + 64) 4 = some code

def ErrorAt (observe : Nat → Nat → Option Nat) (out : Nat) : Error → Prop
  | .wrongType => SemanticErrorAt observe out 1 (.small 0) (.small 0)
  | .scope expected actual => SemanticErrorAt observe out 3 expected actual
  | .limit expected actual => SemanticErrorAt observe out 2 expected actual
  | .arithmetic reason => NatArithmetic.errorAt observe out reason
  | .outputTooSmall => SemanticErrorAt observe out 32769 (.small 0) (.small 0)

def ResultAt (observe : Nat → Nat → Option Nat) (out : Nat) : Except Error NatOperand → Prop
  | .ok operand => PlanAt observe out operand
  | .error reason => ErrorAt observe out reason

/-- Allocation payloads remain owned after every later semantic/resource error. -/
def CallsAt (observe : Nat → Nat → Option Nat)
    (calls : List (NatArithmetic.Outcome NatOperand)) : Prop :=
  ∀ call ∈ calls, ∀ reservation, call.allocation = some reservation →
    NatMemory.wordsAt observe reservation.pointer call.written

def AllocationWrites (calls : List (NatArithmetic.Outcome NatOperand))
    (address : BitVec 64) : Prop :=
  ∃ call ∈ calls, ∃ reservation, call.allocation = some reservation ∧
    InSpan address (BitVec.ofNat 64 reservation.pointer) (8 * call.written.length)

def Allocated (calls : List (NatArithmetic.Outcome NatOperand)) : Prop :=
  ∃ call ∈ calls, ∃ reservation, call.allocation = some reservation

/-- Only the second, out-of-line list constructor propagates the extra padding
word at result+68. First-constructor failures are published inline. -/
def ResultWrites (out : BitVec 64) (outcome : Outcome NatOperand)
    (address : BitVec 64) : Prop :=
  match outcome.result with
  | .ok _ => InSpan address out 40 ∨ InSpan address (out + 64) 4
  | .error _ => InSpan address out 68 ∨
      (outcome.calls.length = 2 ∧ InSpan address (out + 68) 4)

def ArenaAt (m : DataMem) (header address capacity used : BitVec 64) : Prop :=
  widthLoad m header.toNat 8 = some address.toNat ∧
  widthLoad m (header.toNat + 8) 8 = some capacity.toNat ∧
  widthLoad m (header.toNat + 16) 8 = some used.toNat

def arenaState (address capacity used : BitVec 64) : Delimited.ArenaState :=
  ⟨address.toNat, capacity.toNat, used.toNat⟩

def bodyEntry : Desc → Nat
  | .bool => 46 | .uint _ => 795 | .byteVector _ => 529 | .byteList _ => 616
  | .bitVector _ => 82 | .bitList _ => 879 | .progressiveBitList _ => 929

/-- Only active descriptor/value fields are readonly observations. Inactive enum
padding is governed by the ordinary write frame, not silently made an input. -/
def DescLive (pointer : BitVec 64) (desc : Desc) (address : BitVec 64) : Prop :=
  InSpan address pointer 8 ∨
    match desc with
    | .bool => False
    | .progressiveBitList none => InSpan address (pointer + 8) 4
    | .progressiveBitList (some _) => InSpan address (pointer + 8) 4 ∨
        InSpan address (pointer + 16) 16
    | _ => InSpan address (pointer + 8) 16

def ValueLive (pointer : BitVec 64) (value : Value) (address : BitVec 64) : Prop :=
  InSpan address pointer 1 ∨
    match value with
    | .bool _ => InSpan address (pointer + 1) 1
    | .uint _ | .bytes _ => InSpan address (pointer + 8) 16
    | .bits _ => InSpan address (pointer + 16) 32
    | .seq _ | .union _ _ => False

/-- Full preservation includes arbitrary high zero padding and packed backing bytes.
Readonly objects may alias each other and already-used scratch. -/
def BodyBorrowed (s : MachineData) (desc : Desc) (value : Value)
    (buffer address : BitVec 64) : Prop :=
  DescLive s.regs.rsi.toBitVec desc address ∨
  ValueLive s.regs.r14.toBitVec value address ∨
  DescBorrowed desc address ∨ ValueBorrowed value buffer address

/-- The 216-byte local frame plus the actual sixteen-byte BSR lowering activation.
Nat::compare and Nat::from_u128 have no additional local-stack reservation. -/
def BodyWritable (s : MachineData) (outcome : Outcome NatOperand)
    (address : BitVec 64) : Prop :=
  ResultWrites s.regs.rbx.toBitVec outcome address ∨
  AllocationWrites outcome.calls address ∨
  (Allocated outcome.calls ∧ InSpan address (s.regs.rcx.toBitVec + 16) 8) ∨
  InSpan address (s.regs.rsp.toBitVec - 16) 232

/-- Branch ownership at the genuine dispatcher destination. This contains no
semantic success, expected-size, future-memory, or helper-exit assumption. -/
structure BodyOwned (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64) : Prop where
  physical : value.Physical
  descriptor : DescAt s.dmem s.regs.rsi.toBitVec desc
  descriptorMapped : Large.Mapped s.dmem s.regs.rsi.toBitVec (descBytes desc)
  valueStored : ValueAt s.dmem s.regs.r14.toBitVec buffer value
  tag : s.regs.rax.toBitVec.setWidth 8 = BitVec.ofNat 8 (valueTag value)
  arena : ArenaAt s.dmem s.regs.rcx.toBitVec address capacity used
  descriptorBound : s.regs.rsi.toNat + descBytes desc ≤ 2 ^ 64
  valueBound : s.regs.r14.toNat + valueBytes value ≤ 2 ^ 64
  resultBound : s.regs.rbx.toNat + 72 ≤ 2 ^ 64
  headerBound : s.regs.rcx.toNat + 24 ≤ 2 ^ 64
  stackLow : 16 ≤ s.regs.rsp.toNat
  stackBound : s.regs.rsp.toNat + 272 ≤ 2 ^ 64
  arenaBound : address.toNat + capacity.toNat ≤ 2 ^ 64
  arenaNonzero : 0 < capacity.toNat → 0 < address.toNat
  resultMapped : Large.Mapped s.dmem s.regs.rbx.toBitVec 72
  localMapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 16) 232
  freeMapped : Large.Mapped s.dmem (address + used) (capacity.toNat - used.toNat)
  resultHeader : Large.Disjoint s.regs.rbx.toBitVec s.regs.rcx.toBitVec 72 24
  resultStack : Large.Disjoint s.regs.rbx.toBitVec (s.regs.rsp.toBitVec - 16) 72 288
  headerStack : Large.Disjoint s.regs.rcx.toBitVec (s.regs.rsp.toBitVec - 16) 24 288
  freeResult : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rbx.toNat 72
  freeHeader : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rcx.toNat 24
  freeStack : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat - 16) 288
  readonly : ∀ a, BodyBorrowed s desc value buffer a →
    ¬ (InSpan a s.regs.rbx.toBitVec 72 ∨ InSpan a (s.regs.rcx.toBitVec + 16) 8 ∨
      InSpan a (address + used) (capacity.toNat - used.toNat) ∨
      InSpan a (s.regs.rsp.toBitVec - 16) 232)

/-- The common body endpoint is immediately before the real epilogue at3335. -/
structure BodyPost (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64) (t : MachineData) : Prop where
  stack : t.regs.rsp = s.regs.rsp
  observed : ResultAt (widthLoad t.dmem) s.regs.rbx.toNat
    (measure desc value (arenaState address capacity used)).result
  cursor : widthLoad t.dmem (s.regs.rcx.toNat + 16) 8 =
    some (measure desc value (arenaState address capacity used)).used
  header : widthLoad t.dmem s.regs.rcx.toNat 8 = some address.toNat ∧
    widthLoad t.dmem (s.regs.rcx.toNat + 8) 8 = some capacity.toNat
  calls : CallsAt (widthLoad t.dmem) (measure desc value (arenaState address capacity used)).calls
  descriptor : DescAt t.dmem s.regs.rsi.toBitVec desc
  valueStored : ValueAt t.dmem s.regs.r14.toBitVec buffer value
  frame : MemoryFrame s.dmem t.dmem
    (BodyWritable s (measure desc value (arenaState address capacity used)))
  vectors : t.zmms = s.zmms

end SszX86.Measure
