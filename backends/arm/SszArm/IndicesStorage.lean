import SszArm.CodecStorageInitialized
import SszIndicesTypes

namespace SszArm.Indices.Storage

open SszNative (NatOperand)
open SszNative.Indices (PathStep ChunkPosition Error)
open SszArm.Codec.Storage (Image record slice entries desc initializedPrefix)
open Delimited (Span MemoryFrame)

/-- Measured PathStep is 24 bytes; inactive position payloads are not observed. -/
def pathStep (address : Nat) : PathStep → Image
  | .position ordinal => record address 24 8
      (.word address 8 0 ⋏ .operand (address + 8) ordinal)
  | .length => record address 24 8 (.word address 8 1)
  | .activeFields => record address 24 8 (.word address 8 2)
  | .selector => record address 24 8 (.word address 8 3)

def path (address : Nat) (steps : List PathStep) : Image :=
  slice address steps.length 24 8 ⋏ entries pathStep 24 address steps

def operands (address : Nat) (values : List NatOperand) : Image :=
  slice address values.length 16 8 ⋏ entries Image.operand 16 address values

/-- A reserved frontier may have only a prefix initialized when a child fails. -/
def frontierPrefix (address count : Nat) (values : List NatOperand) : Image :=
  initializedPrefix Image.operand address count 16 8 values

def reasonCode : Error → Nat
  | .arithmetic .scratchExhausted => 32768
  | .arithmetic .badRepresentation => 32770
  | .notAGindex _ => 39
  | .rootHasNoBranch => 40
  | .emptyRequest => 41
  | .repeatedIndex => 42
  | .nestedIndex _ => 43
  | .noParts => 52
  | .noPartsMixin => 53
  | .noMixin => 54
  | .noChunkCount => 55
  | .notSteppable => 56
  | .noSuchField _ => 57
  | .noSuchOption _ => 58
  | .noSuchPosition _ => 59

def errorOperand : Error → NatOperand
  | .notAGindex index | .nestedIndex index => index
  | .noSuchField ordinal | .noSuchOption ordinal | .noSuchPosition ordinal => ordinal
  | _ => .small 0

/-- The native private Result niche uses reason=0 for success. Error operands
retain their original pointer/payload rather than only their logical value. -/
def error (address : Nat) (failure : Error) : Image :=
  .word address 8 1 ⋏ .word (address + 8) 8 0 ⋏
  .operand (address + 16) (errorOperand failure) ⋏
  .operand (address + 32) (.small 0) ⋏
  .operand (address + 48) (.small 0) ⋏
  .word (address + 64) 4 (reasonCode failure)

def natResult (address : Nat) : Except Error NatOperand → Image
  | .ok number => .operand address number ⋏ .word (address + 64) 4 0
  | .error failure => error address failure

def descResult (address : Nat) : Except Error SszNative.Codec.Desc → Image
  | .ok shape => desc address shape ⋏ .word (address + 64) 4 0
  | .error failure => error address failure

def position (address : Nat) (placed : ChunkPosition) : Image :=
  .operand address placed.chunk ⋏ .operand (address + 16) placed.start ⋏
  .operand (address + 32) placed.stop

def positionResult (address : Nat) : Except Error ChunkPosition → Image
  | .ok placed => position address placed ⋏ .word (address + 64) 4 0
  | .error failure => error address failure

/-- Option<Desc> uses the unused descriptor discriminant 13; None observes no
inactive child fields. -/
def target (address : Nat) : Option SszNative.Codec.Desc → Image
  | none => .word address 8 13
  | some shape => desc address shape

def resolveResult (address : Nat) : Except Error (NatOperand × Option SszNative.Codec.Desc) → Image
  | .ok (index, child) => .operand address index ⋏ target (address + 16) child ⋏
      .word (address + 64) 4 0
  | .error failure => error address failure

/-- Omit empty mutable extents: an empty allocation writes no address and must
not impose separation on any immutable alias. -/
def mutableSpan (address bytes : Nat) : List Span :=
  if bytes = 0 then [] else [(address, bytes)]

@[simp] theorem mutableSpan_empty (address : Nat) : mutableSpan address 0 = [] := by
  simp [mutableSpan]

theorem mutableSpan_member {address bytes : Nat} {span : Span}
    (member : span ∈ mutableSpan address bytes) : span = (address, bytes) ∧ 0 < bytes := by
  by_cases empty : bytes = 0
  · simp [mutableSpan, empty] at member
  · simp only [mutableSpan, empty, ↓reduceIte, List.mem_singleton] at member
    exact ⟨member, Nat.pos_of_ne_zero empty⟩

theorem path_preserved {writes s t address steps}
    (owned : (path address steps).Owned writes s) (frame : MemoryFrame writes s t) :
    (path address steps).Owned writes t := Image.preserved _ frame owned

theorem operands_preserved {writes s t address values}
    (owned : (operands address values).Owned writes s) (frame : MemoryFrame writes s t) :
    (operands address values).Owned writes t := Image.preserved _ frame owned

theorem frontierPrefix_preserved {writes s t address count values}
    (owned : (frontierPrefix address count values).Owned writes s)
    (frame : MemoryFrame writes s t) :
    (frontierPrefix address count values).Owned writes t := Image.preserved _ frame owned

end SszArm.Indices.Storage
