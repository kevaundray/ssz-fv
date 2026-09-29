import SszX86.CodecBoundedImpl
import SszX86.DelimitedCompare
import SszX86.MeasureFrame

namespace SszX86.CodecBounded
open Kraken.X64.Parser
open SszX86.UintCodec
open SszNative

macro "codec_bound_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.CodecBounded.step_at _ _ $hc
     (SszX86.CodecBounded.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.CodecBounded.program, SszX86.CodecBounded.programChunk0,
     List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.CodecBounded.directives, SszX86.CodecBounded.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bytesv, Width.bits]))

macro "codec_bound_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), Delimited.word_cast])

def savedMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 s.regs.rbp.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 16) 8 s.regs.r15.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 24) 8 s.regs.r14.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 32) 8 s.regs.r12.toBitVec.toInt
  Mem.storeInt m (s.regs.rsp.toBitVec - 40) 8 s.regs.rbx.toBitVec.toInt

def entered (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 40)
      rbx := s.regs.rdi
      rbp := 0}
    status := flags
    dmem := savedMem s}

private theorem push_load (m : DataMem) (sp : BitVec 64) (off : Nat)
    (hm : Large.Mapped m (sp - 48) 48) (lo : 8 ≤ off) (hi : off ≤ 40) :
    ∃ old, Mem.loadInt m (sp - BitVec.ofNat 64 off) 8 = some old := by
  have address : sp - BitVec.ofNat 64 off = (sp - 48) + BitVec.ofNat 64 (48-off) := by bv_omega
  rw [address]
  exact Large.mapped_load m (sp - 48) 48 (48-off) 8 hm (by omega)

macro "codec_bound_push " row:num " offset " off:num " using " hc:term
    " mapped " hm:term : tactic => `(tactic|
  (codec_bound_step $row using $hc
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · apply SszX86.CodecBounded.push_load (off := $off)
     · repeat' first | exact $hm | apply Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

theorem entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (stack : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (entered s flags, base + 13)) :
    Eventually (step e) P (s, base) := by
  rw [← Int64.add_zero base]
  codec_bound_push 0 offset 8 using hc mapped stack
  codec_bound_push 1 offset 16 using hc mapped stack
  codec_bound_push 2 offset 24 using hc mapped stack
  codec_bound_push 3 offset 32 using hc mapped stack
  codec_bound_push 4 offset 40 using hc mapped stack
  codec_bound_step 5 using hc
  codec_bound_step 6 using hc
  have rsp : s.regs.rsp - 8 - 8 - 8 - 8 - 8 =
      UInt64.ofBitVec (s.regs.rsp.toBitVec - 40) := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  constructor <;> simpa [entered, savedMem, BitVec.sub_sub, rsp] using next _

theorem option_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (tag : BitVec 32)
    (hl : Mem.loadInt s.dmem s.regs.rsi.toBitVec 4 = some (tag.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if tag = 1 then base + 18 else base + 110)) :
    Eventually (step e) P (s, base + 13) := by
  have target := hc.targets ("codec_bounded_u110", 110) (by decide)
  have cast : BitVec.ofInt 32 (tag.toNat : Int) = tag := by bv_omega
  codec_bound_step 7 using hc
  simp [MachineData.load, hl, cast, Effects.All]
  codec_bound_step 8 using hc
  by_cases present : tag = 1#32
  · simpa [present, StatusFlags.from_result, Effects.All] using next _
  · have difference : tag - 1#32 ≠ 0#32 := by
      intro zero
      apply present
      have eq := congrArg (fun x : BitVec 32 => x + 1#32) zero
      simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using eq
    simpa [present, difference, target, StatusFlags.from_result, Effects.All] using next _

def prepared (s : MachineData) (cap actual : NatOperand) : MachineData :=
  {s with
    regs := {s.regs with
      r14 := s.regs.rdx
      r15 := UInt64.ofBitVec cap.pointer
      r12 := UInt64.ofBitVec cap.payload
      rdi := UInt64.ofBitVec actual.pointer
      rsi := UInt64.ofBitVec actual.payload
      rdx := UInt64.ofBitVec cap.pointer
      rcx := UInt64.ofBitVec cap.payload}}

theorem prepare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (cap actual : NatOperand)
    (cp : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (cap.pointer.toNat : Int))
    (cv : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some (cap.payload.toNat : Int))
    (ap : Mem.loadInt s.dmem s.regs.rdx.toBitVec 8 = some (actual.pointer.toNat : Int))
    (av : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + 8#64) 8 = some (actual.payload.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (prepared s cap actual, base + 42)) :
    Eventually (step e) P (s, base + 18) := by
  codec_bound_step 9 using hc
  codec_bound_step 10 using hc
  codec_bound_load cp
  codec_bound_step 11 using hc
  codec_bound_load cv
  codec_bound_step 12 using hc
  codec_bound_load ap
  codec_bound_step 13 using hc
  codec_bound_load av
  codec_bound_step 14 using hc
  codec_bound_step 15 using hc
  simpa only [prepared] using next

def callState (s : MachineData) (base : Int64) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8)}
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 (base + 47).toBitVec.toInt}

/-- Calls the immutable checked Nat.compare body at the actual linked offset. -/
theorem compare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hcompare : NatCompare.CodeAt e (base + Int64.ofInt natCompareOffset))
    (s : MachineData) (lhs rhs : Nat) (P : MachineState → Prop)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (left : NatMemory.Pair (widthLoad (callState s base).dmem)
      s.regs.rdi.toBitVec s.regs.rsi.toBitVec lhs)
    (right : NatMemory.Pair (widthLoad (callState s base).dmem)
      s.regs.rdx.toBitVec s.regs.rcx.toBitVec rhs)
    (next : ∀ t, NatCompare.Returned (callState s base) (base + 47).toBitVec
      (compare lhs rhs) t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 42) := by
  have body : Eventually (step e) P (callState s base, base + Int64.ofInt natCompareOffset) := by
    apply eventually_trans (step e)
      (NatCompare.Returned (callState s base) (base + 47).toBitVec (compare lhs rhs))
    · apply NatCompare.program_correct e _ hcompare (callState s base) lhs rhs _ left right
      exact Delimited.stored_return_load _ _ _
    · exact next
  codec_bound_step 16 using hc
  apply Delimited.store_cps
  · exact hm
  · simpa [callState, natCompareOffset, Effects.All, Int64.add_assoc] using body

/-- Signed JLE on Rust Ordering's byte distinguishes .gt from .eq/.lt. -/
theorem compared_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ord : Ordering)
    (result : s.regs.rax.toBitVec.setWidth 8 = NatABI.orderingByte ord)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if ord = .gt then base + 51 else base + 110)) :
    Eventually (step e) P (s, base + 47) := by
  have target := hc.targets ("codec_bounded_u110", 110) (by decide)
  codec_bound_step 17 using hc
  constructor <;> codec_bound_step 18 using hc
  all_goals cases ord <;>
    simpa [StatusFlags.from_result, result, NatABI.orderingByte, target, Effects.All] using next _

end SszX86.CodecBounded
