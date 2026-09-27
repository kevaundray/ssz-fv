import SszX86.NatCompareImpl
import SszX86.UintWidthMemory
import SszX86.Udivti3Math
import SszNatABI
import SszLimbOrder

namespace SszX86.NatCompare
open Kraken.X64.Parser
open SszNative.Limbs SszNative.NatABI

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

/-- The only integer registers written before RET are RAX, RDI, R8 and R9. -/
def state (s : MachineData) (a d x y : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec a
      rdi := UInt64.ofBitVec d
      r8 := UInt64.ofBitVec x
      r9 := UInt64.ofBitVec y}
    status := flags}

@[simp] theorem state_initial (s : MachineData) :
    state s s.regs.rax.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec
      s.regs.r9.toBitVec s.status = s := by
  cases s with | mk regs zmms status dmem => cases regs <;> rfl

def Frame (s t : MachineData) : Prop :=
  t.dmem = s.dmem ∧ t.zmms = s.zmms ∧ t.regs.rsp = s.regs.rsp ∧
  ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 →
    t.regs.get64 r = s.regs.get64 r

theorem state_frame (s : MachineData) (a d x y : BitVec 64) (flags : StatusFlags) :
    Frame s (state s a d x y flags) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4
  cases r <;> simp_all [state, Reg64s.get64]

macro "natcmp_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.NatCompare.step_at _ _ $hc
     (SszX86.NatCompare.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.NatCompare.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.NatCompare.program, SszX86.NatCompare.directives,
      SszX86.NatCompare.labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits, state]))

theorem word_cast (v : BitVec 64) : BitVec.ofInt 64 (v.toNat : Int) = v := by bv_omega

macro "natcmp_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), word_cast])

theorem cf_sub (a b : BitVec 64) :
    ((a - b).unsigned != a.unsigned - b.unsigned) = decide (a.toNat < b.toNat) :=
  Udivti3.cf_sub a b

theorem zf_sub (a b : BitVec 64) : (a - b == 0#64) = decide (a = b) :=
  Udivti3.zf_sub a b

/-- Rust's one-byte Ordering is produced by SETA followed by SBB AL,0. -/
theorem ordering_byte (a b : BitVec 64) :
    (BitVec.ofNat 8 ((!decide (a.toNat < b.toNat) && !decide (a = b)).toNat) -
      BitVec.ofNat 8 (decide (a.toNat < b.toNat)).toNat) =
      orderingByte (compare a.toNat b.toNat) := by
  by_cases h : a.toNat < b.toNat
  · have hn : a ≠ b := by intro he; subst b; omega
    simp [h, hn, Nat.compare_eq_ite_lt, orderingByte]
  · by_cases he : a = b
    · subst b
      simp [orderingByte]
    · have hg : b.toNat < a.toNat := by
        have hn : a.toNat ≠ b.toNat := by
          intro hh
          exact he (BitVec.eq_of_toNat_eq hh)
        omega
      simp [h, he, hg, Nat.compare_eq_ite_lt, orderingByte]

/-- Both encoded return sites execute the actual RET and pop its mapped slot. -/
theorem ret_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hp : P ({s with regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8)}}, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 234) ∧
    Eventually (step e) P (s, base + 372) := by
  constructor
  · natcmp_step 66 using hc
    simp only [MachineData.load, Effects.All, hr, ofBytes_wordBytes]
    exact Eventually.done _ hp
  · natcmp_step 106 using hc
    simp only [MachineData.load, Effects.All, hr, ofBytes_wordBytes]
    exact Eventually.done _ hp

/-- The equality exit clears EAX, with every permitted undefined AF quantified. -/
theorem zero_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d x y : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (state s 0 d x y flags, base + 372)) :
    Eventually (step e) P (state s a d x y flags, base + 370) := by
  natcmp_step 105 using hc
  constructor <;> simpa [state] using hp _

theorem byte_append (hi : BitVec 56) (lo : BitVec 8) :
    (hi ++ lo).setWidth 8 = lo := BitVec.setWidth_append_eq_right

theorem byte_extract (hi : BitVec 56) (lo : BitVec 8) :
    (hi ++ lo).extractLsb' 0 8 = lo := BitVec.extractLsb'_append_eq_right

/-- Compare already loaded limbs, retaining only the specified low result byte. -/
theorem encode_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d x y : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (hp : ∀ a' flags, a'.setWidth 8 = orderingByte (compare a.toNat y.toNat) →
      Eventually (step e) P (state s a' d x y flags, base + 234)) :
    Eventually (step e) P (state s a d x y flags, base + 226) := by
  natcmp_step 63 using hc
  natcmp_step 64 using hc
  simp only [StatusFlags.from_result]
  natcmp_step 65 using hc
  apply hp
  simpa only [byte_append, byte_extract] using ordering_byte a y

/-- Length comparison exits immediately when significant lengths differ. -/
theorem lengths_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d x y : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (heq : x = y → ∀ a' flags,
      Eventually (step e) P (state s a' d x y flags, base + 127))
    (hne : x ≠ y → ∀ a' flags,
      a'.setWidth 8 = orderingByte (compare x.toNat y.toNat) →
      Eventually (step e) P (state s a' d x y flags, base + 372)) :
    Eventually (step e) P (state s a d x y flags, base + 110) := by
  have target := hc.targets ("natCompare_u372", 372) (by decide)
  natcmp_step 33 using hc
  natcmp_step 34 using hc
  simp only [StatusFlags.from_result]
  natcmp_step 35 using hc
  natcmp_step 36 using hc
  natcmp_step 37 using hc
  by_cases h : x = y
  · simpa [StatusFlags.from_result, h, state, Effects.All] using heq h _ _
  · simp [StatusFlags.from_result, h, target, Effects.All]
    apply hne h
    simpa only [byte_append, byte_extract, h, decide_false, Bool.not_false, Bool.and_true]
      using ordering_byte x y

end SszX86.NatCompare
