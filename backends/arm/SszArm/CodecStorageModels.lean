import SszArm.CodecStorageTypes

namespace SszArm.Codec.Storage

open SszNative (NatOperand)
open SszNative.CodecMeasure (Plan)
open SszNative.CodecDecode (Node Slot)
open Delimited (Span MemoryFrame)

mutual
  def plan (address : Nat) : Plan → Image
    | logical@(.mk size leading children allocation) => record address 40 8 (
        .word address 8 logical.childrenPointer ⋏
        .word (address + 8) 8 children.length ⋏
        .operand (address + 16) size ⋏ .word (address + 32) 8 leading ⋏
        .pure (allocation = none → children = []) ⋏
        slice logical.childrenPointer children.length 40 8 ⋏
        planEntries logical.childrenPointer children)

  def planEntries (address : Nat) : List Plan → Image
    | [] => .pure True
    | child :: rest => plan address child ⋏ planEntries (address + 40) rest
end

/-- A Slot's absent width leaves its inactive Nat payload unconstrained. -/
def slot (address : Nat) (logical : Slot) : Image :=
  record address 40 8 (optionOperand address logical.width ⋏
    .word (address + 24) 8 logical.start ⋏ .word (address + 32) 8 logical.ending)

def nodePointer : Option SszNative.Arena.Reservation → Nat
  | none => 16
  | some allocation => allocation.pointer

mutual
  def node (inputBase address : Nat) : Node → Image
    | .bool flag => value address (.bool flag)
    | .uint number => value address (.uint number)
    | .bytes offset data => record address 48 16 (
        .word address 1 2 ⋏ .word (address + 8) 8 (inputBase + offset) ⋏
        .word (address + 16) 8 data.size ⋏
        slice (inputBase + offset) data.size 1 1 ⋏ .bytes (inputBase + offset) data)
    | .bits offset data => record address 48 16 (
        .word address 1 3 ⋏ .word (address + 16) 8 (inputBase + offset) ⋏
        .word (address + 24) 8 data.bytes.size ⋏
        slice (inputBase + offset) data.bytes.size 1 1 ⋏ .bytes (inputBase + offset) data.bytes ⋏
        .word (address + 32) 8 (data.count.setWidth 64).toNat ⋏
        .word (address + 40) 8 ((data.count >>> 64).setWidth 64).toNat)
    | .seq allocation children => record address 48 16 (
        .word address 1 4 ⋏ .word (address + 8) 8 (nodePointer allocation) ⋏
        .word (address + 16) 8 children.length ⋏
        .pure (allocation = none → children = []) ⋏
        slice (nodePointer allocation) children.length 48 16 ⋏
        nodeEntries inputBase (nodePointer allocation) children)
    | .union selector allocation child => record address 48 16 (
        .word address 1 5 ⋏ .operand (address + 8) selector ⋏
        .word (address + 24) 8 allocation.pointer ⋏ node inputBase allocation.pointer child)

  def nodeEntries (inputBase address : Nat) : List Node → Image
    | [] => .pure True
    | child :: rest => node inputBase address child ⋏ nodeEntries inputBase (address + 48) rest
end

def PlanAt (s : ArmState) (address : Nat) (logical : Plan) : Prop :=
  (plan address logical).At s

def PlanOwned (writes : List Span) (s : ArmState) (address : Nat) (logical : Plan) : Prop :=
  (plan address logical).Owned writes s

def SlotAt (s : ArmState) (address : Nat) (logical : Slot) : Prop :=
  (slot address logical).At s

def SlotOwned (writes : List Span) (s : ArmState) (address : Nat) (logical : Slot) : Prop :=
  (slot address logical).Owned writes s

def NodeAt (s : ArmState) (inputBase address : Nat) (logical : Node) : Prop :=
  (node inputBase address logical).At s

def NodeOwned (writes : List Span) (s : ArmState) (inputBase address : Nat) (logical : Node) : Prop :=
  (node inputBase address logical).Owned writes s

theorem plan_at {writes s address logical} (input : PlanOwned writes s address logical) :
    PlanAt s address logical := input.at

theorem slot_at {writes s address logical} (input : SlotOwned writes s address logical) :
    SlotAt s address logical := input.at

theorem node_at {writes s inputBase address logical}
    (input : NodeOwned writes s inputBase address logical) : NodeAt s inputBase address logical :=
  input.at

theorem plan_preserved {writes s t address logical} (input : PlanOwned writes s address logical)
    (frame : MemoryFrame writes s t) : PlanOwned writes t address logical :=
  Image.preserved _ frame input

theorem slot_preserved {writes s t address logical} (input : SlotOwned writes s address logical)
    (frame : MemoryFrame writes s t) : SlotOwned writes t address logical :=
  Image.preserved _ frame input

theorem node_preserved {writes s t inputBase address logical}
    (input : NodeOwned writes s inputBase address logical) (frame : MemoryFrame writes s t) :
    NodeOwned writes t inputBase address logical := Image.preserved _ frame input

/-- Capacity and committed reservation geometry do not initialize a suffix,
inactive enum fields, or alignment gaps. This predicate applies on error too. -/
def initializedPrefix {α : Type} (entry : Nat → α → Image)
    (address count stride alignment : Nat) (initialized : List α) : Image :=
  slice address count stride alignment ⋏ .pure (initialized.length ≤ count) ⋏
    entries entry stride address initialized

def PlansPrefix (s : ArmState) (address count : Nat) (initialized : List Plan) : Prop :=
  (initializedPrefix plan address count 40 8 initialized).At s

def ValuesPrefix (s : ArmState) (inputBase address count : Nat) (initialized : List Node) : Prop :=
  (initializedPrefix (node inputBase) address count 48 16 initialized).At s

def SlotsPrefix (s : ArmState) (address count : Nat) (initialized : List Slot) : Prop :=
  (initializedPrefix slot address count 40 8 initialized).At s

/-- Cursor commit describes a writable region, not an initialized region. -/
def committedSpan (base before after : Nat) : Span := (base + before, after - before)

end SszArm.Codec.Storage
