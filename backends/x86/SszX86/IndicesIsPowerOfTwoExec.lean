import SszX86.IndicesIsPowerOfTwoImpl
import SszX86.CodecNatCmpUsizeExec
import SszIndicesArithmeticPower

namespace SszX86.IndicesIsPowerOfTwo
open Kraken.X64.Parser
open SszNative.Limbs SszNative.NatABI

macro "indices_power_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.IndicesIsPowerOfTwo.step_at _ _ $hc
     (SszX86.IndicesIsPowerOfTwo.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.IndicesIsPowerOfTwo.program,
     SszX86.IndicesIsPowerOfTwo.programChunk0,
     List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.IndicesIsPowerOfTwo.directives, SszX86.IndicesIsPowerOfTwo.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp,
      ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "indices_power_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), NatCompare.word_cast])

def scanState (s : MachineData) (a c : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec a, rcx := UInt64.ofBitVec c},
    status := flags}

theorem scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (c limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n + 2 < 2 ^ 64)
    (loaded : Mem.loadInt s.dmem (s.regs.rdi.toBitVec + BitVec.ofNat 64 (8 * n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0 → ∀ flags, Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (n + 1)) (BitVec.ofNat 64 (n + 1)) flags, base + 16))
    (nonzero : limb ≠ 0 → ∀ flags, Eventually (step e) P
      (scanState s (BitVec.ofNat 64 (n + 1)) (BitVec.ofNat 64 (n + 1)) flags, base + 37)) :
    Eventually (step e) P (scanState s (BitVec.ofNat 64 (n + 2)) c flags, base + 16) := by
  have target := hc.targets ("indices_is_power_of_two_u16", 16) (by decide)
  have different : BitVec.ofNat 64 (n + 2) ≠ 1#64 := by
    intro same
    have numbers := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at numbers
    omega
  have decrement : BitVec.ofNat 64 (n + 2) + BitVec.ofInt 64 (-1) =
      BitVec.ofNat 64 (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, BitVec.ofNat_add]
    change (BitVec.ofNat 64 (n + 1) + 1) + (-1) = _
    simp only [BitVec.add_assoc, BitVec.add_neg_cancel, BitVec.add_zero]
  have address : BitVec.ofInt 64 (s.regs.rdi.toBitVec.toInt +
      (BitVec.ofNat 64 (n + 2)).toInt * 8 + (-16)) =
      s.regs.rdi.toBitVec + BitVec.ofNat 64 (8 * n) := by
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
    change (s.regs.rdi.toBitVec + BitVec.ofNat 64 (n + 2) * BitVec.ofNat 64 8) +
      (-16#64) = _
    rw [← BitVec.ofNat_mul, show (n + 2) * 8 = 8 * n + 16 by omega, BitVec.ofNat_add]
    simp only [BitVec.add_assoc, BitVec.add_neg_cancel, BitVec.add_zero]
  indices_power_step 4 using hc
  indices_power_step 5 using hc
  simp [scanState, StatusFlags.from_result, different, Effects.All]
  indices_power_step 6 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, decrement]
  indices_power_step 7 using hc
  rw [address]
  indices_power_load loaded
  indices_power_step 8 using hc
  indices_power_step 9 using hc
  by_cases empty : limb = 0#64
  · simpa [scanState, StatusFlags.from_result, empty, target, Effects.All] using zero empty _
  · simpa [scanState, StatusFlags.from_result, empty, Effects.All] using nonzero empty _

theorem scan_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64)) (bound : words.length + 1 < 2 ^ 64)
    (loads : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rdi.toBitVec + BitVec.ofNat 64 (8 * i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ c flags,
      (significantCount words n = 0 → ∀ c flags, Eventually (step e) P
        (scanState s 1 c flags, base + 109)) →
      (0 < significantCount words n → ∀ flags, Eventually (step e) P
        (scanState s (BitVec.ofNat 64 (significantCount words n))
          (BitVec.ofNat 64 (significantCount words n)) flags, base + 37)) →
      Eventually (step e) P (scanState s (BitVec.ofNat 64 (n + 1)) c flags, base + 16) := by
  intro n
  induction n with
  | zero =>
      intro inside c flags zero nonzero
      have target := hc.targets ("indices_is_power_of_two_u109", 109) (by decide)
      indices_power_step 4 using hc
      indices_power_step 5 using hc
      simpa [scanState, StatusFlags.from_result, target, Effects.All] using zero rfl c _
  | succ n ih =>
      intro inside c flags zero nonzero
      have loaded : Mem.loadInt s.dmem (s.regs.rdi.toBitVec + BitVec.ofNat 64 (8 * n)) 8 =
          some ((words[n]?.getD 0#64).toNat : Int) := by
        simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using loads ⟨n, by omega⟩
      apply scan_step e base hc s c _ flags n (by omega) loaded P
      · intro empty nextFlags
        apply ih (by omega) _ nextFlags
        · simpa [significantCount, empty] using zero
        · simpa [significantCount, empty] using nonzero
      · intro present nextFlags
        simpa [significantCount, present] using nonzero (by simp [significantCount, present]) nextFlags

end SszX86.IndicesIsPowerOfTwo
