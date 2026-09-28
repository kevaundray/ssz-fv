import SszCodecTypes
import SszNatDivision
import SszNatAdd
import SszNatMul

namespace SszNative.FixedSize

open Serialize (Outcome unchanged bind)

/- Pure recursive model of native/src/schema.rs:116–165, not an ISA claim.
Raw declarations and arbitrary NatOperand representations are admitted. In
particular uint widths are bytes, and no validation or depth bound is imposed. -/
mutual
  def isFixed : Codec.Desc → Bool
    | .primitive (.bool) | .primitive (.uint _) | .primitive (.byteVector _)
      | .primitive (.bitVector _) => true
    | .vector element _ => isFixed element
    | .container fields | .progressiveContainer _ fields => fieldsFixed fields
    | _ => false

  def fieldsFixed : List (String × Codec.Desc) → Bool
    | [] => true
    | (_, field) :: rest => isFixed field && fieldsFixed rest
end

/-- Lift the checked arithmetic outcome without changing its representation,
reservation, writes, or cursor. The failed attempt is also a trace entry. -/
def arithmetic (call : NatArithmetic.Outcome NatOperand) : Outcome NatOperand :=
  ⟨call.result.mapError Serialize.Error.arithmetic, call.used, [call]⟩

def add (left right : NatOperand) (arena : Delimited.ArenaState) : Outcome NatOperand :=
  arithmetic (NatAdd.run left right arena.base arena.capacity arena.used)

def mul (left right : NatOperand) (arena : Delimited.ArenaState) : Outcome NatOperand :=
  arithmetic (NatMul.run left right arena.base arena.capacity arena.used)

/-- Only the trace's result is projected to the quotient. All scratch effects
(allocation, complete written limbs, cursor, quotient representation) are exact;
the local typed result retains the remainder needed by native rounding. -/
def divisionCall (call : NatArithmetic.Outcome (NatOperand × BitVec 64)) :
    NatArithmetic.Outcome NatOperand :=
  ⟨call.result.map Prod.fst, call.used, call.allocation, call.written⟩

def div8 (length : NatOperand) (arena : Delimited.ArenaState) :
    Outcome (NatOperand × BitVec 64) :=
  let call := NatDivision.run length 8 arena.base arena.capacity arena.used
  ⟨call.result.mapError Serialize.Error.arithmetic, call.used, [divisionCall call]⟩

def bitWidth (length : NatOperand) (arena : Delimited.ArenaState) : Outcome NatOperand :=
  bind (div8 length arena) fun divided used =>
    if divided.2 = 0 then unchanged used (.ok divided.1)
    else add divided.1 (.small 1) { arena with used := used }

def measurePrimitive (shape : Serialize.Desc) (arena : Delimited.ArenaState) :
    Outcome (Option NatOperand) :=
  match shape with
  | .bool => unchanged arena.used (.ok (some (.small 1)))
  | .uint width | .byteVector width => unchanged arena.used (.ok (some width))
  | .bitVector length =>
    bind (bitWidth length arena) fun width used => unchanged used (.ok (some width))
  | _ => unchanged arena.used (.ok none)

mutual
  /-- Raw measurement short-circuits in field order, retaining earlier effects
  even if a later child is variable or a later arithmetic call fails. -/
  def measureFixed (desc : Codec.Desc) (arena : Delimited.ArenaState) :
      Outcome (Option NatOperand) :=
    match desc with
    | .primitive shape => measurePrimitive shape arena
    | .vector element length =>
      bind (measureFixed element arena) fun measured used =>
        match measured with
        | none => unchanged used (.ok none)
        | some width =>
          bind (mul width length { arena with used := used }) fun total used =>
            unchanged used (.ok (some total))
    | .container fields | .progressiveContainer _ fields =>
      measureFields fields (.small 0) arena
    | _ => unchanged arena.used (.ok none)

  /-- Each field is measured before adding it to the running total, initially
  Small zero. Even addition to zero is an actual checked helper call. -/
  def measureFields (fields : List (String × Codec.Desc)) (total : NatOperand)
      (arena : Delimited.ArenaState) : Outcome (Option NatOperand) :=
    match fields with
    | [] => unchanged arena.used (.ok (some total))
    | (_, field) :: rest =>
      bind (measureFixed field arena) fun measured used =>
        match measured with
        | none => unchanged used (.ok none)
        | some width =>
          bind (add total width { arena with used := used }) fun next used =>
            measureFields rest next { arena with used := used }
end

/-- The structural preflight precedes every measurement and arithmetic call.
Thus a variable child, even in a zero-length vector, returns None allocation-free. -/
def fixedSize (desc : Codec.Desc) (arena : Delimited.ArenaState) :
    Outcome (Option NatOperand) :=
  if isFixed desc then measureFixed desc arena else unchanged arena.used (.ok none)

end SszNative.FixedSize
