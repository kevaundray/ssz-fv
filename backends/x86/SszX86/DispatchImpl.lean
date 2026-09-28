module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.Dispatch
open Kraken.X64.Parser

def program : List (Nat × Nat × Program) := [
  (0, 1, parse("pushq %rbp")),
  (1, 2, parse("pushq %r15")),
  (3, 2, parse("pushq %r14")),
  (5, 2, parse("pushq %r13")),
  (7, 2, parse("pushq %r12")),
  (9, 1, parse("pushq %rbx")),
  (10, 7, parse("subq $0x138,%rsp")),
  (17, 3, parse("movq %r8,%rbx")),
  (20, 3, parse("movq %rcx,%r14")),
  (23, 3, parse("movq %rsi,%rbp")),
  (26, 3, parse("movq (%rsi),%rax")),
  (29, 7, [.instr (.regular .W64 .W64 (.lea .rcx
    { base := some .rip, idx := none, disp := .int64 (-106556) }))]),
  (36, 4, [.instr (.regular .W64 .W64 (.movsx (.reg .rax)
    (.mem (w := .W32) { base := some (.reg .rcx), idx := some ⟨.rax, .W32⟩ })))]),
  (40, 3, parse("addq %rcx,%rax")),
  (43, 2, [.instr (.regular .W64 .W64 (.jmp (.reg .rax)))])]

def labels : List (String × Nat) := []

def directives (row : Nat × Nat × Program) : List (Directive × Nat) :=
  row.2.2.map (fun instruction => (instruction, row.2.1))

structure CodeAt (e : Executable) (base : Int64) : Prop where
  fetch : ∀ row ∈ program,
    e.directivesAtAddress (base + Int64.ofNat row.1) = directives row

theorem step_at (e : Executable) (base : Int64) (hc : CodeAt e base)
    (row : Nat × Nat × Program) (hr : row ∈ program)
    (s : MachineData) (post : MachineState → Prop) :
    BoolCodec.step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  simp only [BoolCodec.step, step1, Executable.step, hc.fetch row hr]

/-- Linked read-only bytes at the actual RIP-relative table address. Entries are
signed little-endian 32-bit displacements, not preselected code pointers. -/
def tableBytes : List UInt8 :=
  [0x45,0xa0,0x01,0x00, 0x83,0xa4,0x01,0x00, 0x06,0xa3,0x01,0x00,
   0x50,0xa3,0x01,0x00, 0x8b,0xa0,0x01,0x00, 0xc0,0xa4,0x01,0x00,
   0xf0,0xa4,0x01,0x00, 0xc1,0xa3,0x01,0x00, 0x0a,0xa6,0x01,0x00,
   0xdc,0xa2,0x01,0x00, 0x13,0xa5,0x01,0x00, 0x6e,0xa0,0x01,0x00,
   0x3e,0xa1,0x01,0x00]

def tableAddress (base : Int64) : BitVec 64 := (base - 106520).toBitVec
def tableOffset : Int := -106520

def TableAt (m : DataMem) (base : Int64) : Prop :=
  ∀ i (hi : i < tableBytes.length),
    m.get? (tableAddress base + BitVec.ofNat 64 i) = some tableBytes[i]

inductive Kind where
  | bool | uint | byteVector | byteList | bitVector | bitList | progressiveBitList
  deriving DecidableEq

def Kind.tag : Kind → Nat
  | .bool => 0 | .uint => 1 | .byteVector => 2 | .byteList => 3
  | .bitVector => 4 | .bitList => 5 | .progressiveBitList => 6

def Kind.entry : Kind → Nat
  | .bool => 45 | .uint => 1131 | .byteVector => 750 | .byteList => 824
  | .bitVector => 115 | .bitList => 1192 | .progressiveBitList => 1240

end SszX86.Dispatch
