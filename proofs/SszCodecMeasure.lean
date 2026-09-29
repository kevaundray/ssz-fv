import SszCodecError
import SszCodecTypesProofs
import SszFixedSize

set_option autoImplicit false

namespace SszNative.CodecMeasure

open Codec (Desc Value Error)

/-- The native64 Plan payload is 40 bytes, aligned to eight. Its child slice
retains its reservation even when empty; `none` denotes the non-retained branch.
The field offsets agree with the accepted x86 primitive Measure.PlanAt relation;
composition with an actual recursive ISA execution remains a separate theorem. -/
inductive Plan where
  | mk (size : NatOperand) (leading : Nat) (children : List Plan)
      (allocation : Option Arena.Reservation)

def Plan.size : Plan → NatOperand
  | .mk size _ _ _ => size

def Plan.leading : Plan → Nat
  | .mk _ leading _ _ => leading

def Plan.children : Plan → List Plan
  | .mk _ _ children _ => children

def Plan.allocation : Plan → Option Arena.Reservation
  | .mk _ _ _ allocation => allocation

def Plan.leaf (size : NatOperand) : Plan := ⟨size, 0, [], none⟩

def Plan.childrenPointer (plan : Plan) : Nat :=
  match plan.allocation with
  | none => 8
  | some reservation => reservation.pointer

/-- The five live native64 fields, not a byte-for-byte initialization assertion.
The private Result status at out+64 is not part of a stored Plan. Borrowed Nat
limb storage and recursive child storage are related separately by the ISA caller. -/
def PlanFields (observe : Nat → Nat → Option Nat) (address : Nat) (plan : Plan) : Prop :=
  observe address 8 = some plan.childrenPointer ∧
  observe (address + 8) 8 = some plan.children.length ∧
  observe (address + 16) 8 = some plan.size.pointer.toNat ∧
  observe (address + 24) 8 = some plan.size.payload.toNat ∧
  observe (address + 32) 8 = some plan.leading

/-- An initializer may affect its complete 40-byte slot. No value is prescribed
for padding or for unspecified bytes, including on a later initializer failure. -/
def PlanWriteSpan (address byte : Nat) : Prop :=
  address ≤ byte ∧ byte < address + 40

/-- Every attempted helper/reservation remains in order, including failures.
A successful initializer writes only after child measurement and both additions.
The primitive outcome itself includes all ordered from_u128 calls and limb writes.
A writePlan establishes PlanFields and permits PlanWriteSpan only; it never
claims initialized padding byte values. -/
inductive Effect where
  | primitive (shape : Serialize.Desc) (value : Serialize.Value)
      (arena : Delimited.ArenaState) (outcome : Serialize.Outcome NatOperand)
  | arithmetic (left right : NatOperand) (arena : Delimited.ArenaState)
      (outcome : NatArithmetic.Outcome NatOperand)
  | reservePlans (count : Nat) (arena : Delimited.ArenaState)
      (reservation : Option Arena.Reservation)
  | writePlan (address index : Nat) (plan : Plan)

def Effect.planWriteFields (effect : Effect) (observe : Nat → Nat → Option Nat) : Prop :=
  match effect with
  | .writePlan address _ plan => PlanFields observe address plan
  | _ => True

def Effect.planWriteAllows (effect : Effect) (byte : Nat) : Prop :=
  match effect with
  | .writePlan address _ _ => PlanWriteSpan address byte
  | _ => False

structure Outcome (α : Type) where
  result : Except Error α
  used : Nat
  effects : List Effect

def unchanged {α : Type} (used : Nat) (result : Except Error α) : Outcome α :=
  ⟨result, used, []⟩

def bind {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β) : Outcome β :=
  match first.result with
  | .error reason => ⟨.error reason, first.used, first.effects⟩
  | .ok value =>
    let second := next value first.used
    ⟨second.result, second.used, first.effects ++ second.effects⟩

def primitive (shape : Serialize.Desc) (value : Value) (arena : Delimited.ArenaState) :
    Outcome Plan :=
  let measured := Serialize.measure shape value.toPrimitive arena
  ⟨(measured.result.map Plan.leaf).mapError Error.primitive, measured.used,
    [.primitive shape value.toPrimitive arena measured]⟩

def add (left right : NatOperand) (arena : Delimited.ArenaState) : Outcome NatOperand :=
  let call := NatAdd.run left right arena.base arena.capacity arena.used
  ⟨call.result.mapError (fun error => Error.primitive (.arithmetic error)), call.used,
    [.arithmetic left right arena call]⟩

def exactCount (expected : NatOperand) (actual used : Nat) : Outcome Unit :=
  if expected.value = actual then unchanged used (.ok ())
  else unchanged used (.error (.primitive (.scope expected (Serialize.count actual))))

def bounded (limit : Option NatOperand) (actual : NatOperand) (used : Nat) : Outcome Unit :=
  let checked := Serialize.bounded limit actual used
  ⟨checked.result.mapError Error.primitive, checked.used, []⟩

def hostSize (size : NatOperand) (used : Nat) : Outcome Nat :=
  let converted := Serialize.hostSize size used
  ⟨converted.result.mapError Error.primitive, converted.used, []⟩

def compositeSize (size : NatOperand) (used : Nat) : Outcome Unit :=
  if 2 ^ 32 ≤ size.value then unchanged used (.error (.offsetOverflow size))
  else unchanged used (.ok ())

/-- Five u64 words have the same payload and alignment as one native64 Plan.
For zero count Arena.reserve returns dangling pointer eight without a cursor
change. Positive failures consume no new bytes but retain every earlier effect. -/
def reservePlans (count : Nat) (arena : Delimited.ArenaState) : Outcome Arena.Reservation :=
  let reserved := Arena.reserve arena.base arena.capacity arena.used (5 * count)
  match reserved with
  | none => ⟨.error (.primitive (.arithmetic .scratchExhausted)), arena.used,
      [.reservePlans count arena none]⟩
  | some reservation => ⟨.ok reservation, reservation.used,
      [.reservePlans count arena (some reservation)]⟩

def writePlan (allocation : Option Arena.Reservation) (index : Nat) (plan : Plan)
    (used : Nat) : Outcome Unit :=
  match allocation with
  | none => unchanged used (.ok ())
  | some reservation => ⟨.ok (), used,
      [.writePlan (reservation.pointer + 40 * index) index plan]⟩

inductive Parts where
  | repeated (element : Desc)
  | fields (fields : List (String × Desc))

def Parts.allFixed : Parts → Bool
  | .repeated element => FixedSize.isFixed element
  | .fields entries => FixedSize.fieldsFixed entries

def Parts.paired : Parts → List Value → Nat
  | .repeated _, values => values.length
  | .fields entries, values => min entries.length values.length

def Parts.arity : Parts → List Value → Bool
  | .repeated _, _ => true
  | .fields entries, values => entries.length == values.length

/-- Partial sums are unbounded raw native Nats. Retained children are accumulated
in traversal order; the scratch writes, rather than this logical list, model the
native storage. No child encoding is constructed or copied by measurement. -/
structure Partial where
  leading : NatOperand
  bodies : NatOperand
  children : List Plan

def initial : Partial := ⟨.small 0, .small 0, []⟩

def accumulate (inline : Bool) (child : Plan) (totals : Partial)
    (arena : Delimited.ArenaState) : Outcome Partial :=
  bind (add totals.leading (if inline then child.size else .small 4) arena)
    fun leading used =>
      if inline then unchanged used (.ok { totals with leading := leading })
      else bind (add totals.bodies child.size { arena with used := used }) fun bodies used =>
        unchanged used (.ok { totals with leading := leading, bodies := bodies })

/-- A callback is allowed only on an actual value child; this exposes structural
recursion without a fuel bound or a successful-validation premise. -/
abbrev Visit (values : List Value) :=
  (value : Value) → value ∈ values → Desc → Delimited.ArenaState → Bool → Outcome Plan

/-- Paired-prefix loop. Field arity is deliberately not checked here. The plan
write follows all arithmetic for that child, so a failed add leaves its slot
uninitialized while retaining all previous slots and nested allocations. -/
def measureLoop (parts : Parts) (values : List Value) (visit : Visit values)
    (keep : Bool) (allocation : Option Arena.Reservation) (index : Nat)
    (totals : Partial) (arena : Delimited.ArenaState) : Outcome Partial :=
  match values with
  | [] => unchanged arena.used (.ok totals)
  | value :: rest =>
    let step (desc : Desc) (remaining : Parts) : Outcome Partial :=
      bind (visit value (by simp) desc arena keep) fun child used =>
        bind (accumulate (FixedSize.isFixed desc) child totals { arena with used := used })
          fun next used =>
            bind (writePlan allocation index child used) fun _ used =>
              measureLoop remaining rest
                (fun value member => visit value (List.mem_cons_of_mem _ member))
                keep allocation (index + 1)
                { next with children := if keep then next.children ++ [child] else next.children }
                { arena with used := used }
    match parts with
    | .repeated element => step element (.repeated element)
    | .fields [] => unchanged arena.used (.ok totals)
    | .fields ((_, desc) :: fields) => step desc (.fields fields)
termination_by values.length

def finishParts (parts : Parts) (values : List Value) (totals : Partial)
    (allocation : Option Arena.Reservation) (arena : Delimited.ArenaState) : Outcome Plan :=
  if parts.arity values then
    bind (add totals.leading totals.bodies arena) fun size used =>
      bind (compositeSize size used) fun _ used =>
        bind (hostSize totals.leading used) fun leading used =>
          unchanged used (.ok ⟨size, leading, totals.children, allocation⟩)
  else unchanged arena.used (.error (.primitive .wrongType))

/-- Reservation precedes even the first child, but only when retain and not all
fixed. Final arity rejection precedes the final add; overflow follows that add
and all child visits, never an early partial-sum test. -/
def measureParts (parts : Parts) (values : List Value) (visit : Visit values)
    (arena : Delimited.ArenaState) (retain : Bool) : Outcome Plan :=
  let keep := retain && !parts.allFixed
  let run (allocation : Option Arena.Reservation) (used : Nat) :=
    bind (measureLoop parts values visit keep allocation 0 initial { arena with used := used })
      fun totals used => finishParts parts values totals allocation { arena with used := used }
  if keep then
    bind (reservePlans (parts.paired values) arena) fun allocation used => run (some allocation) used
  else run none arena.used

/-- First numerical equality wins, even for duplicate selectors or distinct raw
representations of the same natural number. No declaration validation occurs. -/
def option : List (NatOperand × Desc) → NatOperand → Except Error Desc
  | [], selector => .error (.unknownSelector selector)
  | (chosen, desc) :: rest, selector =>
    if chosen.value = selector.value then .ok desc else option rest selector

def unionPlan (child : Plan) (arena : Delimited.ArenaState) (retain : Bool) : Outcome Plan :=
  bind (add child.size (.small 1) arena) fun size used =>
    if retain && !child.children.isEmpty then
      bind (reservePlans 1 { arena with used := used }) fun allocation used =>
        bind (writePlan (some allocation) 0 child used) fun _ used =>
          unchanged used (.ok ⟨size, 0, [child], some allocation⟩)
    else unchanged used (.ok (Plan.leaf size))

/-- One constructor layer, separated only to expose an induction interface. -/
def measureStep (desc : Desc) (value : Value) (arena : Delimited.ArenaState) (retain : Bool)
    (visit : Visit value.children) : Outcome Plan :=
  match desc, value with
  | .primitive shape, value => primitive shape value arena
  | .vector element length, .seq values =>
    bind (exactCount length values.length arena.used) fun _ used =>
      measureParts (.repeated element) values visit { arena with used := used } retain
  | .list element limit, .seq values =>
    bind (bounded (some limit) (Serialize.count values.length) arena.used) fun _ used =>
      measureParts (.repeated element) values visit { arena with used := used } retain
  | .progressiveList element limit, .seq values =>
    bind (bounded limit (Serialize.count values.length) arena.used) fun _ used =>
      measureParts (.repeated element) values visit { arena with used := used } retain
  | .container fields, .seq values | .progressiveContainer _ fields, .seq values =>
    measureParts (.fields fields) values visit arena retain
  | .compatibleUnion variants, .union selector value =>
    bind (unchanged arena.used (option variants selector)) fun chosen used =>
      bind (visit value (by simp [Value.children]) chosen { arena with used := used } retain)
        fun child used => unionPlan child { arena with used := used } retain
  | _, _ => unchanged arena.used (.error (.primitive .wrongType))

/-- Full recursive codec measurement, for arbitrary finite native values and raw
schemas. Value nesting is solely a termination measure, never an input cap. -/
def measure (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) : Outcome Plan :=
  measureStep desc value arena retain
    (fun child _ desc arena retain => measure desc child arena retain)
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

def encodedSize (desc : Desc) (value : Value) (arena : Delimited.ArenaState) : Outcome Nat :=
  bind (measure desc value arena false) fun plan used => hostSize plan.size used

end SszNative.CodecMeasure
