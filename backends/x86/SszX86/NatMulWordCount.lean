import SszX86.NatMulWordCore

namespace SszX86.NatMulWord
open SszNative.Limbs

def countState (s : MachineData) (b skipped saved : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rbx := UInt64.ofBitVec b
      r11 := UInt64.ofBitVec skipped
      r15 := UInt64.ofBitVec saved}
    status := flags}

private theorem count_address (p : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 (p.toInt + (BitVec.ofNat 64 (n+4)).toInt * 8 + (-32)) =
      p + BitVec.ofNat 64 (8*n) := by
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rw [show BitVec.ofInt 64 8 = 8#64 by decide,
    show BitVec.ofInt 64 (-32) = 18446744073709551584#64 by decide]
  bv_omega

theorem count_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (skipped saved limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n+4 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (countState s (BitVec.ofNat 64 (n+3)) (skipped+1) (BitVec.ofNat 64 (n+4)) flags, base + 144))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (countState s (BitVec.ofNat 64 (n+3)) (skipped+1) (BitVec.ofNat 64 (n+4)) flags, base + 171)) :
    Eventually (step e) P
      (countState s (BitVec.ofNat 64 (n+4)) skipped saved flags, base + 144) := by
  have target := hc.targets ("natMulWord_u144", 144) (by decide)
  have ne : BitVec.ofNat 64 (n+4) ≠ 3#64 := by bv_omega
  have decReg : (OfNat.ofNat (n+4) : UInt64) - 1 = OfNat.ofNat (n+3) := by
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  unfold countState
  natmulword_step 1:8 using hc
  natmulword_step 1:9 using hc
  simp [StatusFlags.from_result, ne, Effects.All]
  natmulword_step 1:10 using hc
  natmulword_step 1:11 using hc
  natmulword_step 1:12 using hc
  natmulword_step 1:13 using hc
  rw [count_address]
  natmulword_load hm
  natmulword_step 1:14 using hc
  by_cases hz : limb = 0#64
  · simpa [StatusFlags.from_result, hz, target, countState, decReg, Effects.All] using zero hz _
  · simpa [StatusFlags.from_result, hz, countState, decReg, Effects.All] using nonzero hz _

/-- Each inspected physical word advances the skipped-word counter. The count
and counter required by the unrolled multiply loop follow from this induction. -/
theorem count_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64)) (bound : words.length+3 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ skipped saved flags,
    (∀ saved flags, significantCount words n = 0 → Eventually (step e) P
      (countState s 3 (skipped + BitVec.ofNat 64 n) saved flags, base + 388)) →
    (significantCount words n ≠ 0 → ∀ flags, Eventually (step e) P
      (countState s (BitVec.ofNat 64 (significantCount words n+2))
        (skipped + BitVec.ofNat 64 (n-significantCount words n+1))
        (BitVec.ofNat 64 (significantCount words n+3)) flags, base + 171)) →
    Eventually (step e) P (countState s (BitVec.ofNat 64 (n+3)) skipped saved flags, base + 144) := by
  intro n
  induction n with
  | zero =>
    intro hn skipped saved flags zero nonzero
    have target := hc.targets ("natMulWord_u388", 388) (by decide)
    unfold countState
    natmulword_step 1:8 using hc
    natmulword_step 1:9 using hc
    simpa [StatusFlags.from_result, target, countState, significantCount, Effects.All]
      using zero saved _ rfl
  | succ n ih =>
    intro hn skipped saved flags zero nonzero
    have loaded : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply count_step e base hc s skipped saved _ flags n (by omega) loaded P
    · intro hz flags
      apply ih (by omega) (skipped+1) _ flags
      · intro saved flags empty
        have isZero : significantCount words (n+1) = 0 := by
          simpa [significantCount, hz] using empty
        have add : skipped + 1 + BitVec.ofNat 64 n = skipped + BitVec.ofNat 64 (n+1) := by
          bv_omega
        simpa only [add] using zero saved flags isZero
      · intro positive flags
        have positive' : significantCount words (n+1) ≠ 0 := by
          simpa [significantCount, hz] using positive
        have smaller := significantCount_le words n
        have add : skipped + 1#64 + BitVec.ofNat 64 (n-significantCount words n+1) =
            skipped + BitVec.ofNat 64 (n+1-significantCount words n+1) := by bv_omega
        simpa [significantCount, hz, add] using nonzero positive' flags
    · intro hz flags
      have positive : significantCount words (n+1) ≠ 0 := by simp [significantCount, hz]
      simpa [significantCount, hz] using nonzero positive flags

theorem count_entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with
        rbx := UInt64.ofBitVec (s.regs.r9.toBitVec + 3)
        r11 := UInt64.ofBitVec (BitVec.ofInt 64 (-1))}}, base + 144)) :
    Eventually (step e) P (s, base + 122) := by
  natmulword_step 1:4 using hc
  natmulword_step 1:5 using hc
  natmulword_step 1:6 using hc
  natmulword_step 1:7 using hc
  simpa only [BitVec.ofInt_add, BitVec.ofInt_toInt,
    show BitVec.ofInt 64 3 = (3 : BitVec 64) by decide,
    show UInt64.ofBitVec (BitVec.ofInt 64 (-1)) = (18446744073709551615 : UInt64) by decide] using next

end SszX86.NatMulWord
