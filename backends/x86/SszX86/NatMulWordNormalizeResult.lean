import SszX86.NatMulWordCore

namespace SszX86.NatMulWord
open SszNative.Limbs


def resultNormalizeState (s : MachineData) (a d : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rbx := UInt64.ofBitVec a, rcx := UInt64.ofBitVec d}
    status := flags}

private theorem scan_address (p : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 (p.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      p + BitVec.ofNat 64 (8*n) := by
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rw [show BitVec.ofInt 64 8 = 8#64 by decide,
    show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
  bv_omega

/-- The final scan reads the entire allocated buffer, including the final carry
slot even when zero; it never shortens the recorded allocation or written list. -/
theorem result_normalize_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (d limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n+2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.r14.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (resultNormalizeState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 752))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (resultNormalizeState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 773)) :
    Eventually (step e) P (resultNormalizeState s (BitVec.ofNat 64 (n+2)) d flags, base + 752) := by
  have target := hc.targets ("natMulWord_u752", 752) (by decide)
  have ne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have dec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  unfold resultNormalizeState
  natmulword_step 6:4 using hc
  natmulword_step 6:5 using hc
  simp [StatusFlags.from_result, ne, Effects.All]
  natmulword_step 6:6 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, dec]
  natmulword_step 6:7 using hc
  rw [scan_address]
  natmulword_load hm
  natmulword_step 6:8 using hc
  natmulword_step 6:9 using hc
  by_cases hz : limb = 0#64
  · simpa [StatusFlags.from_result, hz, target, resultNormalizeState, Effects.All] using zero hz _
  · simpa [StatusFlags.from_result, hz, resultNormalizeState, Effects.All] using nonzero hz _

theorem result_normalize_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length+1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.r14.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ d flags,
    (∀ d flags, significantCount words n = 0 → Eventually (step e) P
      (resultNormalizeState s 1 d flags, base + 796)) →
    (significantCount words n ≠ 0 → ∀ flags, Eventually (step e) P
      (resultNormalizeState s (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 773)) →
    Eventually (step e) P (resultNormalizeState s (BitVec.ofNat 64 (n+1)) d flags, base + 752) := by
  intro n
  induction n with
  | zero =>
    intro hn d flags zero nonzero
    have target := hc.targets ("natMulWord_u796", 796) (by decide)
    unfold resultNormalizeState
    natmulword_step 6:4 using hc
    natmulword_step 6:5 using hc
    simpa [StatusFlags.from_result, target, resultNormalizeState, significantCount, Effects.All]
      using zero d _ rfl
  | succ n ih =>
    intro hn d flags zero nonzero
    have loaded : Mem.loadInt s.dmem (s.regs.r14.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply result_normalize_step e base hc s d _ flags n (by omega) loaded P
    · intro hz flags
      apply ih (by omega) _ flags
      · intro d flags empty
        apply zero d flags
        simpa [significantCount, hz] using empty
      · intro positive flags
        have positive' : significantCount words (n+1) ≠ 0 := by
          simpa [significantCount, hz] using positive
        simpa [significantCount, hz] using nonzero positive' flags
    · intro hz flags
      have positive : significantCount words (n+1) ≠ 0 := by simp [significantCount, hz]
      simpa [significantCount, hz] using nonzero positive flags

end SszX86.NatMulWord
