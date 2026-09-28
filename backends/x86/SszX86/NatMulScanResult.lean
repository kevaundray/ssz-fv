import SszX86.NatMulCore

namespace SszX86.NatMul
open SszNative.Limbs

def resultScanState (s : MachineData) (a c : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rbp := UInt64.ofBitVec a, rcx := UInt64.ofBitVec c}
    status := flags}

private theorem scan_address (p : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 (p.toInt + (BitVec.ofNat 64 n).toInt * 8) =
      p + BitVec.ofNat 64 (8*n) := by
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rw [show BitVec.ofInt 64 8 = 8#64 by decide]
  bv_omega

theorem result_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (c limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n+1 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (resultScanState s (BitVec.ofNat 64 n - 1) (BitVec.ofNat 64 n) flags, base + 674))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (resultScanState s (BitVec.ofNat 64 n - 1) (BitVec.ofNat 64 n) flags, base + 693)) :
    Eventually (step e) P (resultScanState s (BitVec.ofNat 64 n) c flags, base + 674) := by
  have target := hc.targets ("natMul_u674", 674) (by decide)
  have ne : BitVec.ofNat 64 n ≠ 18446744073709551615#64 := by bv_omega
  unfold resultScanState
  natmul_step 5 row 27 using hc
  natmul_step 5 row 28 using hc
  simp [StatusFlags.from_result, ne, Effects.All]
  natmul_step 5 row 29 using hc
  natmul_step 5 row 30 using hc
  natmul_step 5 row 31 using hc
  rw [scan_address]
  natmul_load hm
  natmul_step 6 row 0 using hc
  by_cases hz : limb = 0#64
  · simpa [StatusFlags.from_result, hz, target, resultScanState, Effects.All] using zero hz _
  · simpa [StatusFlags.from_result, hz, resultScanState, Effects.All] using nonzero hz _

theorem result_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ c flags,
    (∀ c flags, significantCount words n = 0 → Eventually (step e) P
      (resultScanState s 18446744073709551615#64 c flags, base + 723)) →
    (significantCount words n ≠ 0 → ∀ flags, Eventually (step e) P
      (resultScanState s (BitVec.ofNat 64 (significantCount words n) - 2)
        (BitVec.ofNat 64 (significantCount words n) - 1) flags, base + 693)) →
    Eventually (step e) P
      (resultScanState s (BitVec.ofNat 64 n - 1) c flags, base + 674) := by
  intro n
  induction n with
  | zero =>
    intro hn c flags zero nonzero
    have target := hc.targets ("natMul_u723", 723) (by decide)
    unfold resultScanState
    natmul_step 5 row 27 using hc
    natmul_step 5 row 28 using hc
    simpa [StatusFlags.from_result, target, resultScanState, significantCount, Effects.All]
      using zero c _ rfl
  | succ n ih =>
    intro hn c flags zero nonzero
    have loaded : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    have nextIndex : BitVec.ofNat 64 (n+1) - 1 = BitVec.ofNat 64 n := by bv_omega
    rw [nextIndex]
    apply result_scan_step e base hc s c _ flags n (by omega) loaded P
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
      have previous : BitVec.ofNat 64 (n+1) - 2 = BitVec.ofNat 64 n - 1 := by bv_omega
      have count : significantCount words (n+1) = n+1 := by simp [significantCount, hz]
      simpa only [count, previous, nextIndex] using nonzero positive flags

end SszX86.NatMul
