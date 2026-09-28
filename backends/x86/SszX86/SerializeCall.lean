import SszX86.SerializeEmitOwned
import SszX86.SerializeEdges

namespace SszX86.Serialize
open SszNative SszNative.Serialize UintCodec
open Kraken.X64.Parser

def emitArguments (s : MachineData) : MachineData :=
  { s with regs := { s.regs with
      rcx := UInt64.ofBitVec (s.regs.rsp.toBitVec + 24),
      rdi := s.regs.rbx, rsi := s.regs.r12, rdx := s.regs.r15, r8 := s.regs.r14 } }

/-- The unsigned output-capacity check is after successful native host narrowing. -/
theorem capacity_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (fits : s.regs.r9.toNat ≤ s.regs.r13.toNat → ∀ flags,
      Eventually (step e) P ({ s with status := flags }, base + 388))
    (short : s.regs.r13.toNat < s.regs.r9.toNat → ∀ flags,
      Eventually (step e) P ({ s with status := flags }, base + 313)) :
    Eventually (step e) P (s, base + 308) := by
  have target := hc.targets ("serialize_u388", 388) (by decide)
  serialize_edge_decoded 73 at 308 encodedWidth 3 opcodeAST parse("cmpq %r9,%r13") using hc
  serialize_edge_decoded 74 at 311 encodedWidth 2 opcodeAST parse("jae serialize_u388") using hc
  by_cases enough : s.regs.r9.toNat ≤ s.regs.r13.toNat
  · have notShort : ¬ s.regs.r13.toNat < s.regs.r9.toNat := by omega
    simpa [StatusFlags.from_result, Udivti3.cf_sub, notShort, target, Effects.All]
      using fits enough _
  · have isShort : s.regs.r13.toNat < s.regs.r9.toNat := by omega
    simpa [StatusFlags.from_result, Udivti3.cf_sub, isShort, Effects.All]
      using short isShort _

/-- These are the five original moves, including the optional Plan pointer;
emit receives measured size in R9, not the caller's larger output capacity. -/
theorem emit_arguments_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (emitArguments s, base + 405)) :
    Eventually (step e) P (s, base + 388) := by
  serialize_edge_decoded 86 at 388 encodedWidth 5 opcodeAST parse("leaq 0x18(%rsp),%rcx") using hc
  serialize_edge_decoded 87 at 393 encodedWidth 3 opcodeAST parse("movq %rbx,%rdi") using hc
  serialize_edge_decoded 88 at 396 encodedWidth 3 opcodeAST parse("movq %r12,%rsi") using hc
  serialize_edge_decoded 89 at 399 encodedWidth 3 opcodeAST parse("movq %r15,%rdx") using hc
  serialize_edge_decoded 90 at 402 encodedWidth 3 opcodeAST parse("movq %r14,%r8") using hc
  simpa [emitArguments, Effects.All] using next

end SszX86.Serialize
