import SszX86.NatMulImpl
import SszX86.NatAddCore
import SszNatMul

namespace SszX86.NatMul
open Kraken.X64.Parser
open UintCodec

theorem step_chunk0 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (row : Nat × Nat × Program) (hr : row ∈ programChunk0)
    (s : MachineData) (post : MachineState → Prop) :
    step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  apply step_at e base hc row
  simp only [program, List.mem_append, hr, true_or]

theorem step_chunk1 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (row : Nat × Nat × Program) (hr : row ∈ programChunk1)
    (s : MachineData) (post : MachineState → Prop) :
    step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  apply step_at e base hc row
  simp only [program, List.mem_append, hr, or_true, true_or]

theorem step_chunk2 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (row : Nat × Nat × Program) (hr : row ∈ programChunk2)
    (s : MachineData) (post : MachineState → Prop) :
    step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  apply step_at e base hc row
  simp only [program, List.mem_append, hr, or_true, true_or]

theorem step_chunk3 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (row : Nat × Nat × Program) (hr : row ∈ programChunk3)
    (s : MachineData) (post : MachineState → Prop) :
    step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  apply step_at e base hc row
  simp only [program, List.mem_append, hr, or_true, true_or]

theorem step_chunk4 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (row : Nat × Nat × Program) (hr : row ∈ programChunk4)
    (s : MachineData) (post : MachineState → Prop) :
    step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  apply step_at e base hc row
  simp only [program, List.mem_append, hr, or_true, true_or]

theorem step_chunk5 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (row : Nat × Nat × Program) (hr : row ∈ programChunk5)
    (s : MachineData) (post : MachineState → Prop) :
    step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  apply step_at e base hc row
  simp only [program, List.mem_append, hr, or_true, true_or]

theorem step_chunk6 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (row : Nat × Nat × Program) (hr : row ∈ programChunk6)
    (s : MachineData) (post : MachineState → Prop) :
    step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  apply step_at e base hc row
  simp only [program, List.mem_append, hr, or_true]

macro "natmul_step " chunk:num &"row" k:num " using " hc:term : tactic => do
  let rows := Lean.mkIdent (Lean.Name.str `SszX86.NatMul s!"programChunk{chunk.getNat}")
  let fetch := Lean.mkIdent (Lean.Name.str `SszX86.NatMul s!"step_chunk{chunk.getNat}")
  `(tactic|
    (apply step_cps
     have fetched := $fetch _ _ $hc
       ($rows[$k]'(by decide)) (List.getElem_mem (by decide))
     unfold $rows:ident at fetched
     simp only [List.getElem_cons_zero, List.getElem_cons_succ] at fetched
     apply (fetched _ _).mpr
     simp (config := {instances := true})
       [SszX86.NatMul.directives, SszX86.NatMul.usedLabels,
        Directives.interp, Directive.interp, Instr.interp, Operation.interp,
        Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
        ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
        MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
        Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
        BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
        BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
        Int64.add_assoc, Width.bytes, Width.bits]))

macro "natmul_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), Delimited.word_cast])

end SszX86.NatMul
