import SszX86.NatMulCore

namespace SszX86.NatMul
open SszNative.Limbs

def rightScanState (s : MachineData) (a b c : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r10 := UInt64.ofBitVec a
      r11 := UInt64.ofBitVec b
      r13 := UInt64.ofBitVec c}
    status := flags}

private theorem scan_address (p : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 (p.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      p + BitVec.ofNat 64 (8*n) := by
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rw [show BitVec.ofInt 64 8 = 8#64 by decide,
    show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
  bv_omega

theorem right_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (c limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n+2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (rightScanState s (-BitVec.ofNat 64 n) (BitVec.ofNat 64 (n+1))
        (BitVec.ofNat 64 (n+1)) flags, base + 144))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (rightScanState s (-BitVec.ofNat 64 n) (BitVec.ofNat 64 (n+1))
        (BitVec.ofNat 64 (n+1)) flags, base + 167)) :
    Eventually (step e) P
      (rightScanState s (-BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+2)) c flags, base + 144) := by
  have target := hc.targets ("natMul_u144", 144) (by decide)
  have ne : -BitVec.ofNat 64 (n+1) ≠ 0#64 := by bv_omega
  have inc : -BitVec.ofNat 64 (n+1) + 1#64 = -BitVec.ofNat 64 n := by bv_omega
  have incReg : -(OfNat.ofNat (n+1) : UInt64) + OfNat.ofNat 1 = -OfNat.ofNat n := by
    apply UInt64.toBitVec_inj.1
    change -BitVec.ofNat 64 (n+1) + 1#64 = -BitVec.ofNat 64 n
    exact inc
  have dec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  unfold rightScanState
  natmul_step 1 row 17 using hc
  constructor <;> natmul_step 1 row 18 using hc
  all_goals
    simp [StatusFlags.from_result, ne, Effects.All]
    natmul_step 1 row 19 using hc
    simp only [inc, incReg]
    natmul_step 1 row 20 using hc
    simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, dec]
    natmul_step 1 row 21 using hc
    rw [scan_address]
    natmul_load hm
    natmul_step 1 row 22 using hc
    natmul_step 1 row 23 using hc
    by_cases hz : limb = 0#64
    · simpa [StatusFlags.from_result, hz, target, rightScanState, Effects.All, incReg] using zero hz _
    · simpa [StatusFlags.from_result, hz, rightScanState, Effects.All, incReg] using nonzero hz _

theorem right_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length+1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ c flags,
    (∀ c flags, significantCount words n = 0 → Eventually (step e) P
      (rightScanState s 0 1 c flags, base + 206)) →
    (significantCount words n ≠ 0 → ∀ flags, Eventually (step e) P
      (rightScanState s (1 - BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 167)) →
    Eventually (step e) P
      (rightScanState s (-BitVec.ofNat 64 n) (BitVec.ofNat 64 (n+1)) c flags, base + 144) := by
  intro n
  induction n with
  | zero =>
    intro hn c flags zero nonzero
    have target := hc.targets ("natMul_u206", 206) (by decide)
    unfold rightScanState
    natmul_step 1 row 17 using hc
    constructor <;> natmul_step 1 row 18 using hc
    all_goals
      simpa [StatusFlags.from_result, target, rightScanState, significantCount, Effects.All]
        using zero c _ rfl
  | succ n ih =>
    intro hn c flags zero nonzero
    have loaded : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply right_scan_step e base hc s c _ flags n (by omega) loaded P
    · intro hz flags
      apply ih (by omega) _ flags
      · intro c flags empty
        apply zero c flags
        simpa [significantCount, hz] using empty
      · intro positive flags
        have positive' : significantCount words (n+1) ≠ 0 := by
          simpa [significantCount, hz] using positive
        simpa [significantCount, hz] using nonzero positive' flags
    · intro hz flags
      have positive : significantCount words (n+1) ≠ 0 := by simp [significantCount, hz]
      have neg : 1 - BitVec.ofNat 64 (n+1) = -BitVec.ofNat 64 n := by bv_omega
      have count : significantCount words (n+1) = n+1 := by simp [significantCount, hz]
      simpa only [count, neg] using nonzero positive flags

end SszX86.NatMul
