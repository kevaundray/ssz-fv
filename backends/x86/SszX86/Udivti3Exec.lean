import SszX86.Udivti3Math
import SszX86.Bytes

namespace SszX86.Udivti3

open Kraken.X64.Parser

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

macro "udiv_fetch" : tactic => `(tactic|
  (dsimp (config := {instances := true})
     [executable, layout, program, Kraken.Layout.apply]
   simp [Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses, Int64.add_assoc]))

macro "udiv_label" : tactic => `(tactic|
  (dsimp (config := {instances := true})
     [Executable.labels, executable, layout, program, Kraken.Layout.apply]
   simp [Kraken.Executable.withAddresses, Int64.add_assoc]))

private theorem fetch0 (base : Int64) : (executable base).directivesAtAddress base =
    (parse("cmpq %rcx, %rsi")).zip [3] := by udiv_fetch
private theorem fetch3 (base : Int64) : (executable base).directivesAtAddress (base + 3) =
    (parse("jb udiv_zero")).zip [6] := by udiv_fetch
private theorem fetch9 (base : Int64) : (executable base).directivesAtAddress (base + 9) =
    (parse("ja udiv_dispatch")).zip [2] := by udiv_fetch
private theorem fetch11 (base : Int64) : (executable base).directivesAtAddress (base + 11) =
    (parse("cmpq %rdx, %rdi")).zip [3] := by udiv_fetch
private theorem fetch14 (base : Int64) : (executable base).directivesAtAddress (base + 14) =
    (parse("jb udiv_zero")).zip [6] := by udiv_fetch
private theorem fetch20 (base : Int64) : (executable base).directivesAtAddress (base + 20) =
    (parse("udiv_dispatch: testq %rcx, %rcx")).zip [0, 3] := by udiv_fetch
private theorem fetch23 (base : Int64) : (executable base).directivesAtAddress (base + 23) =
    (parse("jnz udiv_wide")).zip [2] := by udiv_fetch
private theorem fetch25 (base : Int64) : (executable base).directivesAtAddress (base + 25) =
    (parse("cmpq $1, %rdx")).zip [4] := by udiv_fetch
private theorem fetch29 (base : Int64) : (executable base).directivesAtAddress (base + 29) =
    (parse("je udiv_one")).zip [6] := by udiv_fetch
private theorem fetch35 (base : Int64) : (executable base).directivesAtAddress (base + 35) =
    (parse("xorl %eax, %eax")).zip [2] := by udiv_fetch
private theorem fetch37 (base : Int64) : (executable base).directivesAtAddress (base + 37) =
    (parse("xorl %r8d, %r8d")).zip [3] := by udiv_fetch
private theorem fetch40 (base : Int64) : (executable base).directivesAtAddress (base + 40) =
    (parse("movl $64, %r11d")).zip [6] := by udiv_fetch
private theorem fetch46 (base : Int64) : (executable base).directivesAtAddress (base + 46) =
    (parse("cmpq %rdx, %rsi")).zip [3] := by udiv_fetch
private theorem fetch49 (base : Int64) : (executable base).directivesAtAddress (base + 49) =
    (parse("jae udiv_high")).zip [2] := by udiv_fetch
private theorem fetch51 (base : Int64) : (executable base).directivesAtAddress (base + 51) =
    (parse("movq %rsi, %r9")).zip [3] := by udiv_fetch
private theorem fetch54 (base : Int64) : (executable base).directivesAtAddress (base + 54) =
    (parse("movq %rdi, %rsi")).zip [3] := by udiv_fetch
private theorem fetch57 (base : Int64) : (executable base).directivesAtAddress (base + 57) =
    (parse("xorl %r10d, %r10d")).zip [3] := by udiv_fetch
private theorem fetch60 (base : Int64) : (executable base).directivesAtAddress (base + 60) =
    (parse("jmp udiv_word_loop")).zip [2] := by udiv_fetch
private theorem fetch62 (base : Int64) : (executable base).directivesAtAddress (base + 62) =
    (parse("udiv_high: xorl %r9d, %r9d")).zip [0, 3] := by udiv_fetch
private theorem fetch65 (base : Int64) : (executable base).directivesAtAddress (base + 65) =
    (parse("movl $1, %r10d")).zip [6] := by udiv_fetch
private theorem fetch71 (base : Int64) : (executable base).directivesAtAddress (base + 71) =
    (parse("udiv_word_loop: addq %rax, %rax")).zip [0, 3] := by udiv_fetch
private theorem fetch74 (base : Int64) : (executable base).directivesAtAddress (base + 74) =
    (parse("addq %rsi, %rsi")).zip [3] := by udiv_fetch
private theorem fetch77 (base : Int64) : (executable base).directivesAtAddress (base + 77) =
    (parse("adcq %r9, %r9")).zip [3] := by udiv_fetch
private theorem fetch80 (base : Int64) : (executable base).directivesAtAddress (base + 80) =
    (parse("jb udiv_word_subtract")).zip [2] := by udiv_fetch
private theorem fetch82 (base : Int64) : (executable base).directivesAtAddress (base + 82) =
    (parse("cmpq %rdx, %r9")).zip [3] := by udiv_fetch
private theorem fetch85 (base : Int64) : (executable base).directivesAtAddress (base + 85) =
    (parse("jb udiv_word_next")).zip [2] := by udiv_fetch
private theorem fetch87 (base : Int64) : (executable base).directivesAtAddress (base + 87) =
    (parse("udiv_word_subtract: subq %rdx, %r9")).zip [0, 3] := by udiv_fetch
private theorem fetch90 (base : Int64) : (executable base).directivesAtAddress (base + 90) =
    (parse("addq $1, %rax")).zip [4] := by udiv_fetch
private theorem fetch94 (base : Int64) : (executable base).directivesAtAddress (base + 94) =
    (parse("udiv_word_next: subq $1, %r11")).zip [0, 4] := by udiv_fetch
private theorem fetch98 (base : Int64) : (executable base).directivesAtAddress (base + 98) =
    (parse("jnz udiv_word_loop")).zip [2] := by udiv_fetch
private theorem fetch100 (base : Int64) : (executable base).directivesAtAddress (base + 100) =
    (parse("testq %r10, %r10")).zip [3] := by udiv_fetch
private theorem fetch103 (base : Int64) : (executable base).directivesAtAddress (base + 103) =
    (parse("jnz udiv_second")).zip [2] := by udiv_fetch
private theorem fetch105 (base : Int64) : (executable base).directivesAtAddress (base + 105) =
    (parse("movq %r8, %rdx")).zip [3] := by udiv_fetch
private theorem fetch108 (base : Int64) : (executable base).directivesAtAddress (base + 108) =
    (parse("ret")).zip [1] := by udiv_fetch
private theorem fetch109 (base : Int64) : (executable base).directivesAtAddress (base + 109) =
    (parse("udiv_second: movq %rax, %r8")).zip [0, 3] := by udiv_fetch
private theorem fetch112 (base : Int64) : (executable base).directivesAtAddress (base + 112) =
    (parse("movq %rdi, %rsi")).zip [3] := by udiv_fetch
private theorem fetch115 (base : Int64) : (executable base).directivesAtAddress (base + 115) =
    (parse("xorl %eax, %eax")).zip [2] := by udiv_fetch
private theorem fetch117 (base : Int64) : (executable base).directivesAtAddress (base + 117) =
    (parse("movl $64, %r11d")).zip [6] := by udiv_fetch
private theorem fetch123 (base : Int64) : (executable base).directivesAtAddress (base + 123) =
    (parse("xorl %r10d, %r10d")).zip [3] := by udiv_fetch
private theorem fetch126 (base : Int64) : (executable base).directivesAtAddress (base + 126) =
    (parse("jmp udiv_word_loop")).zip [2] := by udiv_fetch
private theorem fetch128 (base : Int64) : (executable base).directivesAtAddress (base + 128) =
    (parse("udiv_wide: movq %rsi, %r9")).zip [0, 3] := by udiv_fetch
private theorem fetch131 (base : Int64) : (executable base).directivesAtAddress (base + 131) =
    (parse("xorl %r10d, %r10d")).zip [3] := by udiv_fetch
private theorem fetch134 (base : Int64) : (executable base).directivesAtAddress (base + 134) =
    (parse("xorl %eax, %eax")).zip [2] := by udiv_fetch
private theorem fetch136 (base : Int64) : (executable base).directivesAtAddress (base + 136) =
    (parse("movl $64, %r11d")).zip [6] := by udiv_fetch
private theorem fetch142 (base : Int64) : (executable base).directivesAtAddress (base + 142) =
    (parse("udiv_wide_loop: addq %rax, %rax")).zip [0, 3] := by udiv_fetch
private theorem fetch145 (base : Int64) : (executable base).directivesAtAddress (base + 145) =
    (parse("addq %rdi, %rdi")).zip [3] := by udiv_fetch
private theorem fetch148 (base : Int64) : (executable base).directivesAtAddress (base + 148) =
    (parse("adcq %r9, %r9")).zip [3] := by udiv_fetch
private theorem fetch151 (base : Int64) : (executable base).directivesAtAddress (base + 151) =
    (parse("adcq %r10, %r10")).zip [3] := by udiv_fetch
private theorem fetch154 (base : Int64) : (executable base).directivesAtAddress (base + 154) =
    (parse("cmpq %rcx, %r10")).zip [3] := by udiv_fetch
private theorem fetch157 (base : Int64) : (executable base).directivesAtAddress (base + 157) =
    (parse("ja udiv_wide_subtract")).zip [2] := by udiv_fetch
private theorem fetch159 (base : Int64) : (executable base).directivesAtAddress (base + 159) =
    (parse("jb udiv_wide_next")).zip [2] := by udiv_fetch
private theorem fetch161 (base : Int64) : (executable base).directivesAtAddress (base + 161) =
    (parse("cmpq %rdx, %r9")).zip [3] := by udiv_fetch
private theorem fetch164 (base : Int64) : (executable base).directivesAtAddress (base + 164) =
    (parse("jb udiv_wide_next")).zip [2] := by udiv_fetch
private theorem fetch166 (base : Int64) : (executable base).directivesAtAddress (base + 166) =
    (parse("udiv_wide_subtract: subq %rdx, %r9")).zip [0, 3] := by udiv_fetch
private theorem fetch169 (base : Int64) : (executable base).directivesAtAddress (base + 169) =
    (parse("sbbq %rcx, %r10")).zip [3] := by udiv_fetch
private theorem fetch172 (base : Int64) : (executable base).directivesAtAddress (base + 172) =
    (parse("addq $1, %rax")).zip [4] := by udiv_fetch
private theorem fetch176 (base : Int64) : (executable base).directivesAtAddress (base + 176) =
    (parse("udiv_wide_next: subq $1, %r11")).zip [0, 4] := by udiv_fetch
private theorem fetch180 (base : Int64) : (executable base).directivesAtAddress (base + 180) =
    (parse("jnz udiv_wide_loop")).zip [2] := by udiv_fetch
private theorem fetch182 (base : Int64) : (executable base).directivesAtAddress (base + 182) =
    (parse("xorl %edx, %edx")).zip [2] := by udiv_fetch
private theorem fetch184 (base : Int64) : (executable base).directivesAtAddress (base + 184) =
    (parse("ret")).zip [1] := by udiv_fetch
private theorem fetch185 (base : Int64) : (executable base).directivesAtAddress (base + 185) =
    (parse("udiv_one: movq %rdi, %rax")).zip [0, 3] := by udiv_fetch
private theorem fetch188 (base : Int64) : (executable base).directivesAtAddress (base + 188) =
    (parse("movq %rsi, %rdx")).zip [3] := by udiv_fetch
private theorem fetch191 (base : Int64) : (executable base).directivesAtAddress (base + 191) =
    (parse("ret")).zip [1] := by udiv_fetch
private theorem fetch192 (base : Int64) : (executable base).directivesAtAddress (base + 192) =
    (parse("udiv_zero: xorl %eax, %eax")).zip [0, 2] := by udiv_fetch
private theorem fetch194 (base : Int64) : (executable base).directivesAtAddress (base + 194) =
    (parse("xorl %edx, %edx")).zip [2] := by udiv_fetch
private theorem fetch196 (base : Int64) : (executable base).directivesAtAddress (base + 196) =
    (parse("ret")).zip [1] := by udiv_fetch

private theorem label20 (base : Int64) :
    (Executable.labels (executable base)).label "udiv_dispatch" = base + 20 := by udiv_label
private theorem label62 (base : Int64) :
    (Executable.labels (executable base)).label "udiv_high" = base + 62 := by udiv_label
private theorem label71 (base : Int64) :
    (Executable.labels (executable base)).label "udiv_word_loop" = base + 71 := by udiv_label
private theorem label87 (base : Int64) :
    (Executable.labels (executable base)).label "udiv_word_subtract" = base + 87 := by udiv_label
private theorem label94 (base : Int64) :
    (Executable.labels (executable base)).label "udiv_word_next" = base + 94 := by udiv_label
private theorem label109 (base : Int64) :
    (Executable.labels (executable base)).label "udiv_second" = base + 109 := by udiv_label
private theorem label128 (base : Int64) :
    (Executable.labels (executable base)).label "udiv_wide" = base + 128 := by udiv_label
private theorem label142 (base : Int64) :
    (Executable.labels (executable base)).label "udiv_wide_loop" = base + 142 := by udiv_label
private theorem label166 (base : Int64) :
    (Executable.labels (executable base)).label "udiv_wide_subtract" = base + 166 := by udiv_label
private theorem label176 (base : Int64) :
    (Executable.labels (executable base)).label "udiv_wide_next" = base + 176 := by udiv_label
private theorem label185 (base : Int64) :
    (Executable.labels (executable base)).label "udiv_one" = base + 185 := by udiv_label
private theorem label192 (base : Int64) :
    (Executable.labels (executable base)).label "udiv_zero" = base + 192 := by udiv_label

@[simp] private theorem relative_pc (base a b : Int64) :
    base + (a + (base + b - (base + a))) = base + b := by
  rw [← Int64.add_assoc, Int64.add_comm (base + a), Int64.sub_add_cancel]

macro "udiv_step" : tactic => `(tactic|
  (apply step_cps
   simp (config := {instances := true}) [step, step1, Executable.step,
     fetch0, fetch3, fetch9, fetch11, fetch14, fetch20, fetch23, fetch25, fetch29, fetch35, fetch37, fetch40, fetch46, fetch49, fetch51, fetch54, fetch57, fetch60, fetch62, fetch65, fetch71, fetch74, fetch77, fetch80, fetch82, fetch85, fetch87, fetch90, fetch94, fetch98, fetch100, fetch103, fetch105, fetch108, fetch109, fetch112, fetch115, fetch117, fetch123, fetch126, fetch128, fetch131, fetch134, fetch136, fetch142, fetch145, fetch148, fetch151, fetch154, fetch157, fetch159, fetch161, fetch164, fetch166, fetch169, fetch172, fetch176, fetch180, fetch182, fetch184, fetch185, fetch188, fetch191, fetch192, fetch194, fetch196,
     List.zip, Directives.interp, Directive.interp, Instr.interp,
     Operation.interp, Operand.interp, RegOrMem.interp, RelRegOrMem.interp, Reg.interp,
     AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize,
     MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
     Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
     BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
     BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
     label20, label62, label71, label87, label94, label109, label128, label142, label166, label176, label185, label192, Int64.add_assoc]))

private theorem register_eq (a b : BitVec 64) :
    a = b ↔ UInt64.ofBitVec a = UInt64.ofBitVec b :=
  ⟨congrArg UInt64.ofBitVec, congrArg UInt64.toBitVec⟩

@[simp] private theorem unsigned_zero (w : Nat) : (0#w).unsigned = 0 := by
  simp [BitVec.unsigned]

macro "udiv_finish" : tactic => `(tactic|
  simp_all (config := {instances := true})
    [step, radix, BitVec.signed, BitVec.take, UInt64.instOfNat,
     UInt64.add_comm, UInt64.add_assoc, value_le_iff, register_eq, ← Nat.not_lt,
     subFlags, addFlags, adcFlags, StatusFlags.from_result, Effects.All])

/-- No loop instruction touches memory, SIMD, RSP or a callee-saved register. -/
structure Frame (s t : MachineData) : Prop where
  memory : t.dmem = s.dmem
  vectors : t.zmms = s.zmms
  stack : t.regs.rsp = s.regs.rsp
  saved : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi →
    r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → t.regs.get64 r = s.regs.get64 r

theorem Frame.refl (s : MachineData) : Frame s s :=
  ⟨rfl, rfl, rfl, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩

theorem Frame.trans {s t u : MachineData} (h : Frame s t) (h' : Frame t u) : Frame s u :=
  ⟨h'.memory.trans h.memory, h'.vectors.trans h.vectors, h'.stack.trans h.stack,
    fun r a b c d e f g i j => (h'.saved r a b c d e f g i j).trans (h.saved r a b c d e f g i j)⟩

def wordBody (s : MachineData) : MachineData :=
  let x := s.regs.rsi.toBitVec
  let r := s.regs.r9.toBitVec
  let d := s.regs.rdx.toBitVec
  let take := SszNative.DivisionBits.stepTake r d (bit x)
  { s with
    regs := { s.regs with
      rax := UInt64.ofBitVec (s.regs.rax.toBitVec + s.regs.rax.toBitVec +
        BitVec.ofNat 64 take.toNat)
      rsi := UInt64.ofBitVec (x + x)
      r9 := UInt64.ofBitVec (SszNative.DivisionBits.remainderStep r d (bit x))
      r11 := UInt64.ofBitVec (s.regs.r11.toBitVec - 1) }
    status := subFlags s.regs.r11.toBitVec 1 }

def wideLow (s : MachineData) : BitVec 64 :=
  s.regs.r9.toBitVec + s.regs.r9.toBitVec +
    BitVec.ofNat 64 (addFlags s.regs.rdi.toBitVec s.regs.rdi.toBitVec).cf.toNat

def wideHigh (s : MachineData) : BitVec 64 :=
  s.regs.r10.toBitVec + s.regs.r10.toBitVec +
    BitVec.ofNat 64 (adcFlags s.regs.r9.toBitVec s.regs.r9.toBitVec
      (addFlags s.regs.rdi.toBitVec s.regs.rdi.toBitVec).cf).cf.toNat

def wideTake (s : MachineData) : Bool :=
  decide (s.regs.rcx.toBitVec.toNat ≤ (wideHigh s).toNat ∧
    (wideHigh s = s.regs.rcx.toBitVec → s.regs.rdx.toBitVec.toNat ≤ (wideLow s).toNat))

theorem wideTake_eq (s : MachineData) :
    wideTake s =
      decide (value s.regs.rdx.toBitVec s.regs.rcx.toBitVec ≤ value (wideLow s) (wideHigh s)) := by
  simp only [wideTake, value_le_iff]

def wideBody (s : MachineData) : MachineData :=
  let lo := wideLow s
  let hi := wideHigh s
  let take := wideTake s
  { s with
    regs := { s.regs with
      rax := UInt64.ofBitVec (s.regs.rax.toBitVec + s.regs.rax.toBitVec +
        BitVec.ofNat 64 take.toNat)
      rdi := UInt64.ofBitVec (s.regs.rdi.toBitVec + s.regs.rdi.toBitVec)
      r9 := UInt64.ofBitVec (if take then lo - s.regs.rdx.toBitVec else lo)
      r10 := UInt64.ofBitVec (if take then hi - s.regs.rcx.toBitVec -
        BitVec.ofNat 64 (subFlags lo s.regs.rdx.toBitVec).cf.toNat else hi)
      r11 := UInt64.ofBitVec (s.regs.r11.toBitVec - 1) }
    status := subFlags s.regs.r11.toBitVec 1 }

theorem wordBody_frame (s : MachineData) : Frame s (wordBody s) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
  cases r <;> first | contradiction | rfl

theorem wideBody_frame (s : MachineData) : Frame s (wideBody s) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
  cases r <;> first | contradiction | rfl

/-- A complete word iteration, with both overflow and ordinary subtraction paths. -/
theorem word_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (step base) P (wordBody s,
      if (wordBody s).status.zf then base + 100 else base + 71)) :
    Eventually (step base) P (s, base + 71) := by
  have hadd := addFlags_cf s.regs.rsi.toBitVec s.regs.rsi.toBitVec
  have hadc := adcFlags_cf s.regs.r9.toBitVec s.regs.r9.toBitVec
    (addFlags s.regs.rsi.toBitVec s.regs.rsi.toBitVec).cf
  have hbit := double_carry s.regs.rsi.toBitVec
  have hlo := (word_adc s.regs.rsi.toBitVec s.regs.r9.toBitVec).1
  have hcarry := (word_adc s.regs.rsi.toBitVec s.regs.r9.toBitVec).2
  have hcmp := subFlags_cf
    (SszNative.DivisionBits.stepLo s.regs.r9.toBitVec (bit s.regs.rsi.toBitVec))
    s.regs.rdx.toBitVec
  simp only [addFlags, adcFlags, subFlags] at hadd hadc hbit hcmp hlo hcarry
  udiv_step
  udiv_step
  udiv_step
  udiv_step
  split
  · udiv_step
    udiv_step
    udiv_step
    udiv_step
    split <;>
      (simp only [wordBody, SszNative.DivisionBits.remainderStep,
         SszNative.DivisionBits.stepTake, SszNative.DivisionBits.stepCarry,
         SszNative.DivisionBits.stepLo, SszNative.DivisionBits.stepNat, Nat.two_mul] at hp
       udiv_finish)
  · udiv_step
    udiv_step
    split
    · udiv_step
      udiv_step
      split <;>
        (simp only [wordBody, SszNative.DivisionBits.remainderStep,
           SszNative.DivisionBits.stepTake, SszNative.DivisionBits.stepCarry,
           SszNative.DivisionBits.stepLo, SszNative.DivisionBits.stepNat, Nat.two_mul] at hp
         udiv_finish)
    · udiv_step
      udiv_step
      udiv_step
      udiv_step
      split <;>
        (simp only [wordBody, SszNative.DivisionBits.remainderStep,
           SszNative.DivisionBits.stepTake, SszNative.DivisionBits.stepCarry,
           SszNative.DivisionBits.stepLo, SszNative.DivisionBits.stepNat, Nat.two_mul] at hp
         udiv_finish)

/-- A complete wide iteration, including the real low-word borrow into SBB. -/
theorem wide_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (step base) P (wideBody s,
      if (wideBody s).status.zf then base + 182 else base + 142)) :
    Eventually (step base) P (s, base + 142) := by
  have hhi := subFlags_cf (wideHigh s) s.regs.rcx.toBitVec
  have hhz := subFlags_zf (wideHigh s) s.regs.rcx.toBitVec
  have hlo := subFlags_cf (wideLow s) s.regs.rdx.toBitVec
  have horder := value_lt_iff (wideLow s) (wideHigh s)
    s.regs.rdx.toBitVec s.regs.rcx.toBitVec
  simp only [subFlags, wideHigh, wideLow, adcFlags, addFlags] at hhi hhz hlo horder
  udiv_step
  udiv_step
  udiv_step
  udiv_step
  udiv_step
  udiv_step
  split
  · udiv_step
    udiv_step
    udiv_step
    udiv_step
    udiv_step
    split <;>
      (simp only [wideBody, wideTake, wideLow, wideHigh] at hp
       udiv_finish)
  · udiv_step
    split
    · udiv_step
      udiv_step
      split <;>
        (simp only [wideBody, wideTake, wideLow, wideHigh] at hp
         udiv_finish)
    · udiv_step
      udiv_step
      split
      · udiv_step
        udiv_step
        split <;>
          (simp only [wideBody, wideTake, wideLow, wideHigh] at hp
           udiv_finish)
      · udiv_step
        udiv_step
        udiv_step
        udiv_step
        udiv_step
        split <;>
          (simp only [wideBody, wideTake, wideLow, wideHigh] at hp
           udiv_finish)

/-- Each actual RET consumes the mapped eight-byte slot and nothing else. -/
theorem ret_runs (base : Int64) (s : MachineData) (ra : BitVec 64)
    (off : Nat) (hoff : off = 108 ∨ off = 184 ∨ off = 191 ∨ off = 196)
    (P : MachineState → Prop)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hp : P ({ s with regs := { s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8) } }, Int64.ofBitVec ra)) :
    Eventually (step base) P (s, base + Int64.ofNat off) := by
  rcases hoff with rfl | rfl | rfl | rfl
  all_goals
    udiv_step
    simp only [MachineData.load, Effects.All, hr, ofBytes_wordBytes]
    exact Eventually.done _ hp

end SszX86.Udivti3
