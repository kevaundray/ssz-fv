import SszHashLayoutTypes

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)

/-- Borrowed nested views. Indexing never constructs the list of slots. -/
inductive Nested where
  | sequence (element : Desc) (values : List Value)
  | fields (fields : List (String × Desc)) (values : List Value)
  | progressive (active : List Bool) (fields : List (String × Desc)) (values : List Value)
  | union (desc : Desc) (value : Value)

def Nested.count : Nested → Nat
  | .sequence _ values | .fields _ values => values.length
  | .progressive active _ _ => active.length
  | .union _ _ => 1

/-- Exact optional reads of native `Layout::nested`, including unchecked views. -/
def Nested.at : Nested → Nat → Option (Desc × Value)
  | .sequence element values, index => values[index]?.map (fun value => (element, value))
  | .fields entries values, index =>
      entries[index]?.bind (fun field => values[index]?.map (fun value => (field.2, value)))
  | .progressive active entries values, index =>
      if active[index]?.getD false then
        let ordinal := (active.take index).countP id
        entries[ordinal]?.bind (fun field => values[ordinal]?.map (fun value => (field.2, value)))
      else none
  | .union desc value, index => if index = 0 then some (desc, value) else none

/-- First numerical match; operands are neither normalized nor range checked. -/
def lookup : List (NatOperand × Desc) → NatOperand → Option Desc
  | [], _ => none
  | (chosen, desc) :: rest, selector =>
      if chosen.value = selector.value then some desc else lookup rest selector

/-- Provenance of a borrowed nested view. This records no future child result,
resource sufficiency, or validity of the child. Packed views need no recursion. -/
inductive Generated : Desc → Value → Nested → Prop where
  | vector (element : Desc) (length : NatOperand) (values : List Value) :
      Generated (.vector element length) (.seq values) (.sequence element values)
  | list (element : Desc) (limit : NatOperand) (values : List Value) :
      Generated (.list element limit) (.seq values) (.sequence element values)
  | progressiveList (element : Desc) (limit : Option NatOperand) (values : List Value) :
      Generated (.progressiveList element limit) (.seq values) (.sequence element values)
  | container (fields : List (String × Desc)) (values : List Value) :
      Generated (.container fields) (.seq values) (.fields fields values)
  | progressiveContainer (active : List Bool) (fields : List (String × Desc))
      (values : List Value) :
      Generated (.progressiveContainer active fields) (.seq values)
        (.progressive active fields values)
  | compatibleUnion (variants : List (NatOperand × Desc)) (selector : NatOperand)
      (desc : Desc) (value : Value) (selected : lookup variants selector = some desc) :
      Generated (.compatibleUnion variants) (.union selector value) (.union desc value)

end SszNative.HashLayout
