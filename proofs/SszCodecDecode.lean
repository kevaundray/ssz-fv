import SszCodecDecodeCore

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc Error)

abbrev Visit (children : List Desc) :=
  (child : Desc) → child ∈ children → Input → Delimited.ArenaState → Outcome Node

/-- Offset validation has no child callback and no arena effects. Every descending
pair is checked before the single final past-scope guard. -/
def validateOffsets : List Nat → Nat → Except Error Unit
  | [], _ => .ok ()
  | [last], scope => if scope < last then .error .offsetPastScope else .ok ()
  | first :: next :: rest, scope =>
    if next < first then .error .offsetUnordered
    else validateOffsets (next :: rest) scope

structure Window where
  start : Nat
  ending : Nat

def offsetWindows : List Nat → Nat → List Window
  | [], _ => []
  | [last], scope => [⟨last, scope⟩]
  | first :: next :: rest, scope => ⟨first, next⟩ :: offsetWindows (next :: rest) scope

def fixedWindows (count width : Nat) : List Window :=
  (List.range count).map fun index => ⟨index * width, index * width + width⟩

/-- Reservations precede all children. A child's slot is initialized only after
that child returns successfully; bind preserves every earlier effect on failure. -/
def decodeWindows (visit : Input → Delimited.ArenaState → Outcome Node)
    (windows : List Window) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState) : Outcome (List Node) :=
  match windows with
  | [] => unchanged arena.used (.ok [])
  | window :: rest =>
    bind (visit (input.slice window.start window.ending) arena) fun child used =>
      bind (writeValue allocation index child used) fun _ used =>
        bind (decodeWindows visit rest input allocation (index + 1) { arena with used := used })
          fun children used => unchanged used (.ok (child :: children))

def decodeArray (visit : Input → Delimited.ArenaState → Outcome Node)
    (windows : List Window) (input : Input) (arena : Delimited.ArenaState) : Outcome Node :=
  bind (reserve valueLayout windows.length arena) fun allocation used =>
    bind (decodeWindows visit windows input allocation 0 { arena with used := used })
      fun children used => unchanged used (.ok (.seq (some allocation) children))

/-- Reject the actual typed reservation before constructing any logical windows.
In particular, a huge zero-width count cannot force a host list allocation first. -/
def decodeFixed (visit : Input → Delimited.ArenaState → Outcome Node)
    (count width : Nat) (input : Input) (arena : Delimited.ArenaState) : Outcome Node :=
  bind (reserve valueLayout count arena) fun allocation used =>
    bind (decodeWindows visit (fixedWindows count width) input allocation 0
      { arena with used := used }) fun children used =>
        unchanged used (.ok (.seq (some allocation) children))

/-- Extensional proof adapter only: execution uses the reservation-first definition. -/
theorem decodeFixed_eq_decodeArray (visit : Input → Delimited.ArenaState → Outcome Node)
    (count width : Nat) (input : Input) (arena : Delimited.ArenaState) :
    decodeFixed visit count width input arena =
      decodeArray visit (fixedWindows count width) input arena := by
  simp only [decodeFixed, decodeArray, fixedWindows, List.length_map, List.length_range]

def decodeOffsets (visit : Input → Delimited.ArenaState → Outcome Node)
    (count : Nat) (input : Input) (arena : Delimited.ArenaState) : Outcome Node :=
  let offsets := Ssz.readOffsets input.bytes count
  bind (unchanged arena.used (validateOffsets offsets input.bytes.size)) fun _ used =>
    decodeArray visit (offsetWindows offsets input.bytes.size) input { arena with used := used }

def vector (element : Desc) (length : NatOperand)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (input : Input) (arena : Delimited.ArenaState) : Outcome Node :=
  bind (compositeSize input.bytes.size arena.used) fun _ used =>
    bind (fixedSize element { arena with used := used }) fun width used =>
      match width with
      | some width =>
        bind (mul width length { arena with used := used }) fun expected used =>
          bind (exact expected input.bytes.size used) fun _ used =>
            if length.value = 0 then unchanged used (.ok (.seq none []))
            else bind (narrow length scratch used) fun count used =>
              bind (narrow width scratch used) fun width used =>
                decodeFixed visit count width input { arena with used := used }
      | none =>
        bind (mul length (.small 4) { arena with used := used }) fun leading used =>
          if input.bytes.size < leading.value then
            unchanged used (.error (.scopeTooSmall leading (Serialize.count input.bytes.size)))
          else if length.value = 0 then unchanged used (.ok (.seq none []))
          else bind (narrow length scratch used) fun count used =>
            let first := Ssz.readUint input.bytes 0 4
            if leading.value ≠ first then
              unchanged used (.error (.firstOffset leading (Serialize.count first)))
            else decodeOffsets visit count input { arena with used := used }

def list (element : Desc) (limit : Option NatOperand)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (input : Input) (arena : Delimited.ArenaState) : Outcome Node :=
  bind (compositeSize input.bytes.size arena.used) fun _ used =>
    if input.bytes.size = 0 then unchanged used (.ok (.seq none []))
    else bind (fixedSize element { arena with used := used }) fun width used =>
      match width with
      | some width =>
        if width.value = 0 then unchanged used (.error .scopeWidthless)
        else if input.bytes.size < width.value then
          unchanged used (.error (.scopeUndivided (Serialize.count input.bytes.size) width))
        else bind (narrow width representation used) fun width used =>
          if input.bytes.size % width ≠ 0 then
            unchanged used (.error (.scopeUndivided (Serialize.count input.bytes.size)
              (Serialize.count width)))
          else
            let count := input.bytes.size / width
            bind (bounded limit (Serialize.count count) used) fun _ used =>
              decodeFixed visit count width input { arena with used := used }
      | none =>
        if input.bytes.size < 4 then
          unchanged used (.error (.scopeTooSmall (.small 4) (Serialize.count input.bytes.size)))
        else
          let first := Ssz.readUint input.bytes 0 4
          if first < 4 then unchanged used (.error .offsetBelowTable)
          else if first % 4 ≠ 0 then unchanged used (.error .offsetUnaligned)
          else if input.bytes.size < first then unchanged used (.error .offsetPastScope)
          else
            let count := first / 4
            bind (bounded limit (Serialize.count count) used) fun _ used =>
              decodeOffsets visit count input { arena with used := used }

/-- The membership witness enables structural descriptor recursion without fuel.
It records only an existing child, never the result of a future decode. -/
structure Entry (children : List Desc) where
  desc : Desc
  member : desc ∈ children
  slot : Slot

def initialEntries (children : List Desc) : List (Entry children) :=
  children.attach.map fun child => ⟨child.val, child.property, ⟨none, 0, 0⟩⟩

def initializeSlots (count : Nat) (allocation : Arena.Reservation) (used : Nat) : Outcome Unit :=
  ⟨.ok (), used, (List.range count).map fun index =>
    .writeSlot (allocation.pointer + slotLayout.size * index) index ⟨none, 0, 0⟩⟩

structure Measured (children : List Desc) where
  entries : List (Entry children)
  leading : NatOperand
  allFixed : Bool

def measureSlots {children : List Desc} (entries : List (Entry children))
    (allocation : Arena.Reservation) (index : Nat) (leading : NatOperand) (allFixed : Bool)
    (arena : Delimited.ArenaState) : Outcome (Measured children) :=
  match entries with
  | [] => unchanged arena.used (.ok ⟨[], leading, allFixed⟩)
  | entry :: rest =>
    bind (fixedSize entry.desc arena) fun width used =>
      let slot := { entry.slot with width := width }
      bind (writeSlot allocation index slot used) fun _ used =>
        bind (add leading (width.getD (.small 4)) { arena with used := used }) fun leading used =>
          bind (measureSlots rest allocation (index + 1) leading (allFixed && width.isSome)
            { arena with used := used }) fun measured used =>
              unchanged used (.ok { measured with entries := { entry with slot := slot } :: measured.entries })

def positionSlots {children : List Desc} (entries : List (Entry children))
    (input : Input) (allocation : Arena.Reservation) (index position used : Nat) :
    Outcome (List (Entry children) × Nat) :=
  match entries with
  | [] => unchanged used (.ok ([], position))
  | entry :: rest =>
    let width := match entry.slot.width with
      | none => unchanged used (.ok 4)
      | some width => narrow width .truncated used
    bind width fun width used =>
      let ending := position + width
      if 2 ^ 64 ≤ ending ∨ input.bytes.size < ending then unchanged used (.error .truncated)
      else
        let slot := match entry.slot.width with
          | some _ => { entry.slot with start := position, ending := ending }
          | none => { entry.slot with start := Ssz.readUint input.bytes position 4 }
        bind (writeSlot allocation index slot used) fun _ used =>
          bind (positionSlots rest input allocation (index + 1) ending used) fun result used =>
            unchanged used (.ok ({ entry with slot := slot } :: result.1, result.2))

/-- The pending variable slot is updated as soon as its next boundary is known.
No final scope test can hide a later descending pair. -/
def validateSlots {children : List Desc} (entries : List (Entry children))
    (allocation : Arena.Reservation) (index leading scope : Nat)
    (previous : Option (Nat × Slot)) (used : Nat) : Outcome Unit :=
  match entries with
  | [] =>
    match previous with
    | none => exact (Serialize.count leading) scope used
    | some (index, slot) =>
      if scope < slot.start then unchanged used (.error .offsetPastScope)
      else writeSlot allocation index { slot with ending := scope } used
  | entry :: rest =>
    match entry.slot.width with
    | some _ => validateSlots rest allocation (index + 1) leading scope previous used
    | none =>
      match previous with
      | none =>
        if entry.slot.start ≠ leading then
          unchanged used (.error (.firstOffset (Serialize.count leading)
            (Serialize.count entry.slot.start)))
        else validateSlots rest allocation (index + 1) leading scope (some (index, entry.slot)) used
      | some (previousIndex, previousSlot) =>
        if entry.slot.start < previousSlot.start then unchanged used (.error .offsetUnordered)
        else bind (writeSlot allocation previousIndex
          { previousSlot with ending := entry.slot.start } used) fun _ used =>
            validateSlots rest allocation (index + 1) leading scope (some (index, entry.slot)) used

def nextBody {children : List Desc} : List (Entry children) → Nat → Nat
  | [], scope => scope
  | entry :: rest, scope =>
    if entry.slot.width.isSome then nextBody rest scope else entry.slot.start

/-- Pure readback of the slots written by successful validation. -/
def closeSlots {children : List Desc} : List (Entry children) → Nat → List (Entry children)
  | [], _ => []
  | entry :: rest, scope =>
    let slot := if entry.slot.width.isSome then entry.slot
      else { entry.slot with ending := nextBody rest scope }
    { entry with slot := slot } :: closeSlots rest scope

def decodeEntries {children : List Desc} (entries : List (Entry children))
    (visit : Visit children) (input : Input) (allocation : Arena.Reservation) (index : Nat)
    (arena : Delimited.ArenaState) : Outcome (List Node) :=
  match entries with
  | [] => unchanged arena.used (.ok [])
  | entry :: rest =>
    bind (visit entry.desc entry.member (input.slice entry.slot.start entry.slot.ending) arena)
      fun child used =>
        bind (writeValue allocation index child used) fun _ used =>
          bind (decodeEntries rest visit input allocation (index + 1) { arena with used := used })
            fun decoded used => unchanged used (.ok (child :: decoded))

def structureValue (children : List Desc) (visit : Visit children)
    (input : Input) (arena : Delimited.ArenaState) : Outcome Node :=
  bind (compositeSize input.bytes.size arena.used) fun _ used =>
    bind (reserve slotLayout children.length { arena with used := used }) fun slots used =>
      bind (initializeSlots children.length slots used) fun _ used =>
        bind (measureSlots (initialEntries children) slots 0 (.small 0) true
          { arena with used := used }) fun measured used =>
            let budget := if measured.allFixed then exact measured.leading input.bytes.size used
              else if input.bytes.size < measured.leading.value then
                unchanged used (.error (.scopeTooSmall measured.leading (Serialize.count input.bytes.size)))
              else unchanged used (.ok ())
            bind budget fun _ used =>
              bind (positionSlots measured.entries input slots 0 0 used) fun positioned used =>
                bind (validateSlots positioned.1 slots 0 positioned.2 input.bytes.size none used)
                  fun _ used =>
                    let entries := closeSlots positioned.1 input.bytes.size
                    bind (reserve valueLayout children.length { arena with used := used })
                      fun values used =>
                        bind (decodeEntries entries visit input values 0 { arena with used := used })
                          fun decoded used => unchanged used (.ok (.seq (some values) decoded))

def unionOption (variants : List (NatOperand × Desc))
    (visit : Visit (variants.map Prod.snd)) (selector : NatOperand)
    (input : Input) (arena : Delimited.ArenaState) : Outcome Node :=
  match variants with
  | [] => unchanged arena.used (.error (.unknownSelector selector))
  | (chosen, desc) :: rest =>
    if chosen.value = selector.value then
      bind (visit desc (by simp) input arena) fun child used =>
        bind (reserve valueLayout 1 { arena with used := used }) fun allocation used =>
          bind (writeValue allocation 0 child used) fun _ used =>
            unchanged used (.ok (.union selector allocation child))
    else unionOption rest (fun child member => visit child (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ member))
      selector input arena

/-- All raw constructors, including duplicate union selectors and ignored active
metadata. Recursive callbacks can visit only strict descriptor children. -/
def decodeStep (desc : Desc) (input : Input) (arena : Delimited.ArenaState)
    (visit : Visit desc.children) : Outcome Node :=
  match desc with
  | .primitive shape => primitive shape input arena
  | .vector element length => vector element length (visit element (by simp [Desc.children])) input arena
  | .list element limit => list element (some limit) (visit element (by simp [Desc.children])) input arena
  | .progressiveList element limit => list element limit (visit element (by simp [Desc.children])) input arena
  | .container fields | .progressiveContainer _ fields =>
    structureValue (fields.map Prod.snd) visit input arena
  | .compatibleUnion variants =>
    if input.bytes.size = 0 then unchanged arena.used (.error .noSelector)
    else unionOption variants visit (.small (BitVec.ofNat 64 input.bytes[0]!.toNat))
      (input.slice 1 input.bytes.size) arena

def decode (desc : Desc) (input : Input) (arena : Delimited.ArenaState) : Outcome Node :=
  decodeStep desc input arena (fun child _ input arena => decode child input arena)
termination_by desc.nesting
decreasing_by exact Desc.child_nesting_lt _ _ (by assumption)

def run (desc : Desc) (bytes : Ssz.Bytes) (arena : Delimited.ArenaState) : Outcome Node :=
  decode desc ⟨0, bytes⟩ arena

def Outcome.erase (outcome : Outcome Node) : Except Serialize.Host (Except Ssz.Err Ssz.Value) :=
  Codec.eraseResult (outcome.result.map (fun node => node.value.erase))

end SszNative.CodecDecode
