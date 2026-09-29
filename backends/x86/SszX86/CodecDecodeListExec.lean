import SszX86.CodecDecodeListImpl
import SszX86.CodecDeserializeMemory
import SszX86.DispatchMemory

set_option autoImplicit false

namespace SszX86.CodecDecodeList
open Kraken.X64.Parser
open SszNative UintCodec

private theorem chunk0_member (row : Nat × Nat × Program) (h : row ∈ programChunk0) :
    row ∈ program := by
  simp only [program, List.mem_append]
  simp only [h, true_or, or_true]

private theorem chunk1_member (row : Nat × Nat × Program) (h : row ∈ programChunk1) :
    row ∈ program := by
  simp only [program, List.mem_append]
  simp only [h, true_or, or_true]

macro "codec_list_step0 " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.CodecDecodeList.step_at _ _ $hc
     (SszX86.CodecDecodeList.programChunk0[$k]'(by decide))
     (chunk0_member _ (List.getElem_mem (by decide)))
   simp only [SszX86.CodecDecodeList.programChunk0, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.CodecDecodeList.directives, SszX86.CodecDecodeList.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "codec_list_step1 " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.CodecDecodeList.step_at _ _ $hc
     (SszX86.CodecDecodeList.programChunk1[$k]'(by decide))
     (chunk1_member _ (List.getElem_mem (by decide)))
   simp only [SszX86.CodecDecodeList.programChunk1, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.CodecDecodeList.directives, SszX86.CodecDecodeList.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "codec_list_push " row:num ", " off:num " using " hc:term
    ", " hm:term : tactic => `(tactic|
  (codec_list_step0 $row using $hc
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · have mapped := $hm
     apply SszX86.Dispatch.push_load (offset := $off)
     · repeat' first | exact mapped | apply Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

/-- Actual PUSH instructions, reused at this helper's independently linked entry. -/
theorem pushes_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (next : Eventually (step e) P (Dispatch.savedState s, base + 10)) :
    Eventually (step e) P (s, base) := by
  have stackReg : s.regs.rsp - 8 - 8 - 8 - 8 - 8 - 8 = s.regs.rsp - 48 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  suffices run : Eventually (step e) P (s, base + 0) by
    simpa only [Int64.add_zero] using run
  codec_list_push 0, 8 using hc, mapped
  codec_list_push 1, 16 using hc, mapped
  codec_list_push 2, 24 using hc, mapped
  codec_list_push 3, 32 using hc, mapped
  codec_list_push 4, 40 using hc, mapped
  codec_list_push 5, 48 using hc, mapped
  simpa [Dispatch.savedState, Dispatch.savedMem, Width.bytes, BitVec.sub_sub, stackReg]
    using next

def stackState (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 104)},
    status := memcpySubFlags s.regs.rsp.toBitVec 104}

theorem stack_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (stackState s, base + 14)) :
    Eventually (step e) P (s, base + 10) := by
  codec_list_step0 6 using hc
  simpa [stackState, memcpySubFlags, BitVec.take, BitVec.signed] using next

/-- The empty branch reaches its stores without reading the descriptor, the
limit, the arena header, or even the input pointer. In particular fixedSize
cannot fail before this shortcut. -/
theorem empty_branch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (empty : s.regs.r8.toBitVec = 0#64) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 301)) :
    Eventually (step e) P (s, base + 14) := by
  have target := hc.targets ("codec_decode_list_u301", 301) (by decide)
  codec_list_step0 7 using hc
  constructor <;> codec_list_step0 8 using hc
  all_goals simpa [StatusFlags.from_result, empty, target, Effects.All] using next _

macro "codec_list_store " row:num " at " offset:num " width " width:num
    " using " hc:term " mapped " hm:term : tactic => do
  `(tactic|
    (codec_list_step1 $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · have mapped := $hm
       have loaded := BoolCodec.mapped_load _ _
         (by repeat' first | exact mapped | apply BoolCodec.mapped_store)
         $offset $width (by decide)
       simpa only [BitVec.ofNat_zero, BitVec.add_zero] using loaded
     simp only [Effects.All]))

/-- The empty sequence initializes exactly its discriminant and slice fields,
followed by the outer Result success discriminant. -/
theorem empty_stores (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mapped : BoolCodec.Mapped s.dmem s.regs.rdi.toBitVec)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := CodecDeserialize.sequenceMem s.dmem s.regs.rdi.toBitVec 16 0}, base + 328)) :
    Eventually (step e) P (s, base + 301) := by
  codec_list_store 2 at 16 width 1 using hc mapped mapped
  codec_list_store 3 at 24 width 8 using hc mapped mapped
  codec_list_store 4 at 32 width 8 using hc mapped mapped
  codec_list_store 5 at 0 width 8 using hc mapped mapped
  simpa [CodecDeserialize.sequenceMem] using next

end SszX86.CodecDecodeList
