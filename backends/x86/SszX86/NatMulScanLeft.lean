import SszX86.NatMulCore

namespace SszX86.NatMul
open SszNative.Limbs

def leftScanState (s : MachineData) (a d : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r10 := UInt64.ofBitVec a, r12 := UInt64.ofBitVec d}
    status := flags}

private theorem scan_address (p : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 (p.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      p + BitVec.ofNat 64 (8*n) := by
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rw [show BitVec.ofInt 64 8 = 8#64 by decide,
    show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
  bv_omega

theorem left_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n+2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (leftScanState s (BitVec.ofNat 64 (n+2)) (BitVec.ofNat 64 (n+1)) flags, base + 32))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (leftScanState s (BitVec.ofNat 64 (n+2)) (BitVec.ofNat 64 (n+1)) flags, base + 53)) :
    Eventually (step e) P (leftScanState s a (BitVec.ofNat 64 (n+2)) flags, base + 32) := by
  have target := hc.targets ("natMul_u32", 32) (by decide)
  have ne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have dec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  unfold leftScanState
  natmul_step 0 row 11 using hc
  natmul_step 0 row 12 using hc
  natmul_step 0 row 13 using hc
  simp [StatusFlags.from_result, ne, Effects.All]
  natmul_step 0 row 14 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, dec]
  natmul_step 0 row 15 using hc
  rw [scan_address]
  natmul_load hm
  natmul_step 0 row 16 using hc
  by_cases hz : limb = 0#64
  · simpa [StatusFlags.from_result, hz, target, leftScanState, Effects.All] using zero hz _
  · simpa [StatusFlags.from_result, hz, leftScanState, Effects.All] using nonzero hz _

theorem left_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length+1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ a flags,
    (∀ flags, significantCount words n = 0 → Eventually (step e) P
      (leftScanState s 1 1 flags, base + 89)) →
    (significantCount words n ≠ 0 → ∀ flags, Eventually (step e) P
      (leftScanState s (BitVec.ofNat 64 (significantCount words n + 1))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 53)) →
    Eventually (step e) P (leftScanState s a (BitVec.ofNat 64 (n+1)) flags, base + 32) := by
  intro n
  induction n with
  | zero =>
    intro hn a flags zero nonzero
    have target := hc.targets ("natMul_u89", 89) (by decide)
    unfold leftScanState
    natmul_step 0 row 11 using hc
    natmul_step 0 row 12 using hc
    natmul_step 0 row 13 using hc
    simpa [StatusFlags.from_result, target, leftScanState, significantCount, Effects.All]
      using zero _ rfl
  | succ n ih =>
    intro hn a flags zero nonzero
    have loaded : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply left_scan_step e base hc s a _ flags n (by omega) loaded P
    · intro hz flags
      apply ih (by omega) _ flags
      · intro flags empty
        apply zero flags
        simpa [significantCount, hz] using empty
      · intro positive flags
        have positive' : significantCount words (n+1) ≠ 0 := by
          simpa [significantCount, hz] using positive
        simpa [significantCount, hz] using nonzero positive' flags
    · intro hz flags
      have positive : significantCount words (n+1) ≠ 0 := by simp [significantCount, hz]
      simpa [significantCount, hz] using nonzero positive flags

end SszX86.NatMul
