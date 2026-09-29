import SszX86.CodecNatCmpUsizeImpl
import SszX86.NatCompareProofs
import SszX86.MeasureUintWidthSteps
import SszNatNarrow

namespace SszX86.CodecNatCmpUsize
open Kraken.X64.Parser
open SszNative.Limbs SszNative.NatABI

def state (s : MachineData) (a c v : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec a
      rcx := UInt64.ofBitVec c
      rsi := UInt64.ofBitVec v}
    status := flags}

macro "codec_usize_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.CodecNatCmpUsize.step_at _ _ $hc
     (SszX86.CodecNatCmpUsize.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.CodecNatCmpUsize.program,
     SszX86.CodecNatCmpUsize.programChunk0, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.CodecNatCmpUsize.directives, SszX86.CodecNatCmpUsize.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits, SszX86.CodecNatCmpUsize.state]))

macro "codec_usize_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), NatCompare.word_cast])

@[simp] theorem state_initial (s : MachineData) :
    state s s.regs.rax.toBitVec s.regs.rcx.toBitVec s.regs.rsi.toBitVec s.status = s := by
  cases s with | mk regs zmms status dmem => cases regs <;> rfl

/-- The two actual RET sites both pop precisely the original return slot. -/
theorem ret_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (next : P ({s with regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8)}}, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 45) ∧
    Eventually (step e) P (s, base + 101) := by
  constructor
  · codec_usize_step 13 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next
  · codec_usize_step 35 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next

private theorem compare_pair (lo hi rhs : BitVec 64) :
    BitVec.ofNat 8 (decide (0 < hi.toNat + (decide (rhs.toNat < lo.toNat)).toNat)).toNat -
      BitVec.ofNat 8 (decide (hi.toNat < (decide (lo.toNat < rhs.toNat)).toNat)).toNat =
      orderingByte (compare (lo.toNat + 2^64 * hi.toNat) rhs.toNat) := by
  have hlo := lo.isLt
  have hhi := hi.isLt
  have hr := rhs.isLt
  by_cases hz : hi.toNat = 0
  · by_cases hl : lo.toNat < rhs.toNat
    · simp [hz, hl, show ¬rhs.toNat < lo.toNat by omega,
        Nat.compare_eq_ite_lt, orderingByte]
    · by_cases he : lo.toNat = rhs.toNat
      · simp [hz, he, orderingByte]
      · have hg : rhs.toNat < lo.toNat := by omega
        simp [hz, hl, hg, Nat.compare_eq_ite_lt, orderingByte]
  · have hp : 0 < hi.toNat := by omega
    have hn : ¬lo.toNat + 2^64 * hi.toNat < rhs.toNat := by omega
    have hg : rhs.toNat < lo.toNat + 2^64 * hi.toNat := by omega
    have first : 0 < hi.toNat + (decide (rhs.toNat < lo.toNat)).toNat := by omega
    have second : ¬hi.toNat < (decide (lo.toNat < rhs.toNat)).toNat := by
      by_cases h : lo.toNat < rhs.toNat <;> simp [h] <;> omega
    simp [first, second, hn, hg, Nat.compare_eq_ite_lt, orderingByte]

private theorem zero_borrow (hi : BitVec 64) (borrow : Bool) :
    ((-hi - BitVec.ofNat 64 borrow.toNat).unsigned !=
      (0#64).unsigned - hi.unsigned - (borrow.toNat : Int)) =
      decide (0 < hi.toNat + borrow.toNat) := by
  simpa only [BitVec.zero_sub, BitVec.toNat_zero] using Measure.Uint.cf_sbb 0 hi borrow

private theorem high_borrow (hi : BitVec 64) (borrow : Bool) :
    ((hi - BitVec.ofNat 64 borrow.toNat).unsigned !=
      hi.unsigned - (0#64).unsigned - (borrow.toNat : Int)) =
      decide (hi.toNat < borrow.toNat) := by
  simpa only [BitVec.sub_zero, BitVec.toNat_zero, Nat.zero_add] using
    Measure.Uint.cf_sbb hi 0 borrow

/-- Both CMP/SBB pairs retain the high limb. This is not a truncating usize
comparison: a nonzero high limb compares greater than every usize. -/
theorem encode_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a hi lo : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ a' c' flags,
      a'.setWidth 8 = orderingByte (compare (lo.toNat + 2^64 * hi.toNat) s.regs.rdx.toNat) →
      Eventually (step e) P (state s a' c' lo flags, base + 101)) :
    Eventually (step e) P (state s a hi lo flags, base + 81) := by
  codec_usize_step 28 using hc
  constructor <;> codec_usize_step 29 using hc
  all_goals codec_usize_step 30 using hc
  all_goals simp only [StatusFlags.from_result, NatCompare.cf_sub, zero_borrow]
  all_goals codec_usize_step 31 using hc
  all_goals codec_usize_step 32 using hc
  all_goals codec_usize_step 33 using hc
  all_goals simp only [StatusFlags.from_result, NatCompare.cf_sub, high_borrow]
  all_goals codec_usize_step 34 using hc
  all_goals apply next
  all_goals simpa only [state, NatCompare.byte_append, NatCompare.byte_extract,
    BitVec.toNat_zero, Nat.zero_add, zero_borrow, high_borrow] using
      compare_pair lo hi s.regs.rdx.toBitVec

/-- A native countdown iteration. Only original physical limb loads are used. -/
theorem scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (c limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n + 2 < 2^64)
    (hl : Mem.loadInt s.dmem (s.regs.rdi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0 → ∀ flags, Eventually (step e) P
      (state s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) s.regs.rsi.toBitVec flags,
        base + 16))
    (nonzero : limb ≠ 0 → ∀ flags, Eventually (step e) P
      (state s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) s.regs.rsi.toBitVec flags,
        base + 37)) :
    Eventually (step e) P
      (state s (BitVec.ofNat 64 (n+2)) c s.regs.rsi.toBitVec flags, base + 16) := by
  have target := hc.targets ("codec_nat_cmp_usize_u16", 16) (by decide)
  have ne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have dec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  have addr : BitVec.ofInt 64 (s.regs.rdi.toBitVec.toInt +
      (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      s.regs.rdi.toBitVec + BitVec.ofNat 64 (8*n) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    bv_omega
  codec_usize_step 4 using hc
  codec_usize_step 5 using hc
  simp [state, StatusFlags.from_result, ne, Effects.All]
  codec_usize_step 6 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, dec]
  codec_usize_step 7 using hc
  rw [addr]
  codec_usize_load hl
  codec_usize_step 8 using hc
  codec_usize_step 9 using hc
  by_cases hz : limb = 0#64
  · simpa [state, StatusFlags.from_result, hz, target, Effects.All] using zero hz _
  · simpa [state, StatusFlags.from_result, hz, Effects.All] using nonzero hz _

theorem scan_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64)) (bound : words.length + 1 < 2^64)
    (loads : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rdi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ c flags,
      (significantCount words n = 0 → ∀ c flags, Eventually (step e) P
        (state s 1 c s.regs.rsi.toBitVec flags, base + 50)) →
      (0 < significantCount words n → ∀ flags, Eventually (step e) P
        (state s (BitVec.ofNat 64 (significantCount words n))
          (BitVec.ofNat 64 (significantCount words n)) s.regs.rsi.toBitVec flags, base + 37)) →
      Eventually (step e) P
        (state s (BitVec.ofNat 64 (n+1)) c s.regs.rsi.toBitVec flags, base + 16) := by
  intro n
  induction n with
  | zero =>
    intro hn c flags zero nonzero
    have target := hc.targets ("codec_nat_cmp_usize_u50", 50) (by decide)
    codec_usize_step 4 using hc
    codec_usize_step 5 using hc
    simpa [state, StatusFlags.from_result, target, Effects.All] using zero rfl c _
  | succ n ih =>
    intro hn c flags zero nonzero
    have hl : Mem.loadInt s.dmem (s.regs.rdi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using loads ⟨n, by omega⟩
    apply scan_step e base hc s c _ flags n (by omega) hl P
    · intro hz fl
      apply ih (by omega) _ fl
      · simpa [significantCount, hz] using zero
      · simpa [significantCount, hz] using nonzero
    · intro hz fl
      simpa [significantCount, hz] using nonzero (by simp [significantCount, hz]) fl

end SszX86.CodecNatCmpUsize
