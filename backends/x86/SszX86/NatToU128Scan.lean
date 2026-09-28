import SszX86.NatToU128Impl
import SszX86.NatDivisionCore

namespace SszX86.NatToU128
open SszNative.Limbs
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

macro "natu128_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.NatToU128.step_at _ _ $hc
     (SszX86.NatToU128.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.NatToU128.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.NatToU128.program, SszX86.NatToU128.directives,
      SszX86.NatToU128.labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "natu128_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), Delimited.word_cast])

def scanState (s : MachineData) (a x : BitVec 64) (flags : StatusFlags) : MachineData :=
  { s with
    regs := { s.regs with rax := UInt64.ofBitVec a, r8 := UInt64.ofBitVec x }
    status := flags }

/-- One genuine countdown iteration reads the original stored limb. -/
theorem scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (x limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (hb : n + 2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (hz : limb = 0#64 → ∀ flags, Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 16))
    (hn : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 37)) :
    Eventually (step e) P (scanState s (BitVec.ofNat 64 (n+2)) x flags, base + 16) := by
  have target := hc.targets ("natToU128_u16", 16) (by decide)
  have hne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have hdec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  have haddr : BitVec.ofInt 64 (s.regs.rsi.toBitVec.toInt +
      (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    rw [show BitVec.ofInt 64 8 = 8#64 by decide,
      show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
    bv_omega
  simp only [scanState]
  natu128_step 4 using hc
  natu128_step 5 using hc
  simp [StatusFlags.from_result, hne, Effects.All]
  natu128_step 6 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, hdec]
  natu128_step 7 using hc
  rw [haddr]
  natu128_load hm
  natu128_step 8 using hc
  natu128_step 9 using hc
  by_cases hl : limb = 0#64
  · simpa [StatusFlags.from_result, hl, target, scanState, Effects.All] using hz hl _
  · simpa [StatusFlags.from_result, hl, scanState, Effects.All] using hn hl _

/-- The scan accepts empty and noncanonical storage without trimming memory. -/
theorem scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (hb : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ x flags,
    (significantCount words n = 0 → ∀ x flags, Eventually (step e) P
      (scanState s 1#64 x flags, base + 62)) →
    (0 < significantCount words n → ∀ flags, Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 37)) →
    Eventually (step e) P (scanState s (BitVec.ofNat 64 (n+1)) x flags, base + 16) := by
  intro n
  induction n with
  | zero =>
    intro hn x flags hz hp
    have target := hc.targets ("natToU128_u62", 62) (by decide)
    simp only [scanState]
    natu128_step 4 using hc
    natu128_step 5 using hc
    simpa [StatusFlags.from_result, target, Effects.All, scanState] using
      hz (by simp [significantCount]) x _
  | succ n ih =>
    intro hn x flags hz hp
    have hread : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply scan_step e base hc s x _ flags n (by omega) hread P
    · intro hl fl
      apply ih (by omega) _ fl
      · intro hs x fl
        apply hz (by simpa [significantCount, hl] using hs)
      · intro hs fl
        simpa [significantCount, hl] using hp (by simpa [significantCount, hl] using hs) fl
    · intro hl fl
      simpa [significantCount, hl] using hp (by simp [significantCount, hl]) fl

end SszX86.NatToU128
