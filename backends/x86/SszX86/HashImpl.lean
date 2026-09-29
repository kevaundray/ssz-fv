module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.Hash
open Kraken.X64.Parser

abbrev Row := Nat × Nat × Program
abbrev step (e : Executable) := BoolCodec.step e

/-- A selected instruction keeps its actual encoded width. Labels occupy no bytes. -/
def directives (labels : List (String × Nat)) (row : Row) : List (Directive × Nat) :=
  ((labels.filter (fun item => item.2 == row.1)).map
    (fun item => (Directive.label item.1, 0))) ++
  row.2.2.map (fun instruction => (instruction, row.2.1))

/-- Ordinary code ownership: only fetches and linked branch destinations. -/
structure CodeAt (e : Executable) (base : Int64)
    (program : List Row) (labels : List (String × Nat)) : Prop where
  fetch : ∀ row ∈ program,
    e.directivesAtAddress (base + Int64.ofNat row.1) = directives labels row
  targets : ∀ item ∈ labels, e.labels.label item.1 = base + Int64.ofNat item.2

theorem step_at (e : Executable) (base : Int64)
    (program : List Row) (labels : List (String × Nat))
    (hc : CodeAt e base program labels) (row : Row) (hr : row ∈ program)
    (s : MachineData) (post : MachineState → Prop) :
    step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives labels row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  simp only [step, BoolCodec.step, step1, Executable.step, hc.fetch row hr]

/-- All addresses are relative to the real two-slice entry. -/
def compressOffset : Int := -912
def finalizeOffset : Int := -256
def memcpyOffset : Int := 127872
def memsetOffset : Int := 127936
def initialOffset : Int := -74056
def roundsOffset : Int := -74024

end SszX86.Hash
