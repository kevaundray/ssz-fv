import SszX86.CodecDecodeOffsetsImpl
import SszX86.CodecReadOffsetExec

set_option autoImplicit false

namespace SszX86.CodecDecodeOffsets
open Kraken.X64.Parser
open SszNative UintCodec

macro "codec_offsets_step " chunk:ident " row " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member : ($chunk[$k]'(by decide)) ∈ SszX86.CodecDecodeOffsets.program := by
     have selected : ($chunk[$k]'(by decide)) ∈ $chunk := List.getElem_mem (by decide)
     simp only [SszX86.CodecDecodeOffsets.program, List.mem_append]
     simp only [selected, true_or, or_true]
   have fetched := SszX86.CodecDecodeOffsets.step_at _ _ $hc
     ($chunk[$k]'(by decide)) member
   simp only [$chunk, List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.CodecDecodeOffsets.directives, SszX86.CodecDecodeOffsets.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

/-- The four actual bounds guards execute before the next offset's first byte is
loaded. Their register inequalities are the current loop invariant, not promised
future execution or an assumed successful child. -/
theorem loop_bounds (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (h8 : s.regs.r8.toBitVec ≠ s.regs.r12.toBitVec)
    (h9 : s.regs.r9.toBitVec ≠ s.regs.r12.toBitVec)
    (h10 : s.regs.r10.toBitVec ≠ s.regs.r12.toBitVec)
    (h11 : s.regs.r11.toBitVec ≠ s.regs.r12.toBitVec)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 260)) :
    Eventually (step e) P (s, base + 224) := by
  codec_offsets_step programChunk0 row 59 using hc
  codec_offsets_step programChunk0 row 60 using hc
  simp [StatusFlags.from_result, NatCompare.zf_sub, h8, Effects.All]
  codec_offsets_step programChunk0 row 61 using hc
  codec_offsets_step programChunk0 row 62 using hc
  simp [StatusFlags.from_result, NatCompare.zf_sub, h9, Effects.All]
  codec_offsets_step programChunk0 row 63 using hc
  codec_offsets_step programChunk1 row 0 using hc
  simp [StatusFlags.from_result, NatCompare.zf_sub, h10, Effects.All]
  codec_offsets_step programChunk1 row 1 using hc
  codec_offsets_step programChunk1 row 2 using hc
  simpa [StatusFlags.from_result, NatCompare.zf_sub, h11, Effects.All] using next _

def wordState (s : MachineData) (a b c d : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec a, rbp := UInt64.ofBitVec b,
    rcx := UInt64.ofBitVec c, rdx := UInt64.ofBitVec d}, status := flags}

def wordArithmetic (pc : Nat) (s : MachineData) (flags : StatusFlags) : MachineData :=
  let a := s.regs.rax.toBitVec
  let b := s.regs.rbp.toBitVec
  let c := s.regs.rcx.toBitVec
  let d := s.regs.rdx.toBitVec
  match pc with
  | 284 => wordState s a b c ((d.setWidth 32 <<< 24).setWidth 64) flags
  | 287 => wordState s a b ((c.setWidth 32 <<< 16).setWidth 64) d flags
  | 290 => wordState s a ((b.setWidth 32 <<< 8).setWidth 64) c d flags
  | 293 => wordState s a (b ||| a) c d flags
  | 296 => wordState s a (b ||| c) c d flags
  | _ => wordState s a (b ||| d) c d flags

theorem word_arithmetic_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (pc : Nat) (hpc : pc ∈ [284, 287, 290, 293, 296, 299]) (s : MachineData)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (wordArithmetic pc s flags, base + Int64.ofNat (pc + 3))) :
    Eventually (step e) P (s, base + Int64.ofNat pc) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [wordArithmetic, wordState] at next
  · codec_offsets_step programChunk1 row 7 using hc
    simp [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      Effects.All, BitVec.take, BitVec.signed]
    repeat' first | apply And.intro | intro
    all_goals exact next _
  · codec_offsets_step programChunk1 row 8 using hc
    simp [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      Effects.All, BitVec.take, BitVec.signed]
    repeat' first | apply And.intro | intro
    all_goals exact next _
  · codec_offsets_step programChunk1 row 9 using hc
    simp [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      Effects.All, BitVec.take, BitVec.signed]
    repeat' first | apply And.intro | intro
    all_goals exact next _
  · codec_offsets_step programChunk1 row 10 using hc
    constructor <;> exact next _
  · codec_offsets_step programChunk1 row 11 using hc
    constructor <;> exact next _
  · codec_offsets_step programChunk1 row 12 using hc
    constructor <;> exact next _

private theorem pack (b0 b1 b2 b3 : BitVec 8) :
    (((b1.setWidth 32 <<< 8).setWidth 64 ||| b0.setWidth 64) |||
      (b2.setWidth 32 <<< 16).setWidth 64) |||
      (b3.setWidth 32 <<< 24).setWidth 64 = CodecReadOffset.value b0 b1 b2 b3 := by
  unfold CodecReadOffset.value
  bv_normalize

/-- This is the real bytewise next-offset load, not a modeled four-byte oracle.
The input byte addresses, including the scaled array index, are exact. -/
theorem loop_word (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (b0 b1 b2 b3 : BitVec 8)
    (input : CodecReadOffset.BytesAt s.dmem
      (s.regs.r13.toBitVec + s.regs.r12.toBitVec * 4 + 4) b0 b1 b2 b3)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (wordState s (b0.setWidth 64) (CodecReadOffset.value b0 b1 b2 b3)
        ((b2.setWidth 32 <<< 16).setWidth 64)
        ((b3.setWidth 32 <<< 24).setWidth 64) flags, base + 302)) :
    Eventually (step e) P (s, base + 260) := by
  have h0 := input.1
  have h1 := input.2.1
  have h2 := input.2.2.1
  have h3 := input.2.2.2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3
  codec_offsets_step programChunk1 row 3 using hc
  codec_offset_load h0
  codec_offsets_step programChunk1 row 4 using hc
  codec_offset_load h1
  codec_offsets_step programChunk1 row 5 using hc
  codec_offset_load h2
  codec_offsets_step programChunk1 row 6 using hc
  codec_offset_load h3
  apply word_arithmetic_cps e base hc 284 (by decide)
  intro f1
  apply word_arithmetic_cps e base hc 287 (by decide)
  intro f2
  apply word_arithmetic_cps e base hc 290 (by decide)
  intro f3
  apply word_arithmetic_cps e base hc 293 (by decide)
  intro f4
  apply word_arithmetic_cps e base hc 296 (by decide)
  intro f5
  apply word_arithmetic_cps e base hc 299 (by decide)
  intro f6
  simpa [wordArithmetic, wordState, BitVec.setWidth_setWidth_of_le, pack] using next f6

/-- The descending-pair check is reached before any typed reservation or child
call. Failure immediately selects the concrete OffsetUnordered publisher. -/
theorem ordered_pair (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags},
      if s.regs.rbp.toNat < s.regs.rsi.toNat then base + 501 else base + 311)) :
    Eventually (step e) P (s, base + 302) := by
  have target := hc.targets ("codec_decode_offsets_u501", 501) (by decide)
  codec_offsets_step programChunk1 row 13 using hc
  codec_offsets_step programChunk1 row 14 using hc
  simpa [NatCompare.cf_sub, UInt64.toNat_toBitVec, target, Effects.All] using next _

/-- The last-offset scope test occurs only after all adjacent pairs were checked;
its real failure code is nine and allocation starts only at the success edge. -/
theorem final_scope (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rax := 9}, status := flags},
        if s.regs.r15.toNat < s.regs.rbp.toNat then base + 506 else base + 336)) :
    Eventually (step e) P (s, base + 322) := by
  have target := hc.targets ("codec_decode_offsets_u506", 506) (by decide)
  codec_offsets_step programChunk1 row 19 using hc
  codec_offsets_step programChunk1 row 20 using hc
  codec_offsets_step programChunk1 row 21 using hc
  have ordering : (!decide (s.regs.rbp.toNat < s.regs.r15.toNat) &&
      !decide (s.regs.rbp.toBitVec = s.regs.r15.toBitVec)) =
      decide (s.regs.r15.toNat < s.regs.rbp.toNat) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq]
    bv_omega
  simpa [StatusFlags.from_result, NatCompare.cf_sub, NatCompare.zf_sub,
    UInt64.toNat_toBitVec, ordering, target, Effects.All] using next _

end SszX86.CodecDecodeOffsets
