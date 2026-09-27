import SszX86.NatDivisionCore

namespace SszX86.NatDivision
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Only the scan cursor, temporary count, and flags change. In particular the
entire quotient buffer, rather than just its significant prefix, is retained. -/
def normalizeScanState (s : MachineData) (count temporary : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r13 := UInt64.ofBitVec count
      rax := UInt64.ofBitVec temporary}
    status := flags}

@[simp] theorem normalizeScanState_initial (s : MachineData) :
    normalizeScanState s s.regs.r13.toBitVec s.regs.rax.toBitVec s.status = s := by
  cases s with | mk regs zmms status dmem => cases regs <;> rfl

private theorem normalize_scan_address (p : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 (p.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      p + BitVec.ofNat 64 (8*n) := by
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rw [show BitVec.ofInt 64 8 = 8#64 by decide,
    show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
  bv_omega

theorem normalize_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (temporary limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n+2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.r14.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (normalizeScanState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 496))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (normalizeScanState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 517)) :
    Eventually (step e) P
      (normalizeScanState s (BitVec.ofNat 64 (n+2)) temporary flags, base + 496) := by
  have target := hc.targets ("natDivision_u496", 496) (by decide)
  have ne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have dec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  unfold normalizeScanState
  natdiv_step 127 using hc
  natdiv_step 128 using hc
  simp [StatusFlags.from_result, ne, Effects.All]
  natdiv_step 129 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, dec]
  natdiv_step 130 using hc
  rw [normalize_scan_address]
  natdiv_load hm
  natdiv_step 131 using hc
  natdiv_step 132 using hc
  by_cases hz : limb = 0#64
  · simpa [StatusFlags.from_result, hz, target, normalizeScanState, Effects.All] using zero hz _
  · simpa [StatusFlags.from_result, hz, normalizeScanState, Effects.All] using nonzero hz _

/-- The real backward loop exits with exactly significantCount, also when every
stored quotient limb is zero. It does not mutate or shrink the stored list. -/
theorem normalize_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length+1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.r14.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ temporary flags,
    (∀ temporary flags, significantCount words n = 0 → Eventually (step e) P
      (normalizeScanState s 1 temporary flags, base + 528)) →
    (significantCount words n ≠ 0 → ∀ flags, Eventually (step e) P
      (normalizeScanState s (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 517)) →
    Eventually (step e) P
      (normalizeScanState s (BitVec.ofNat 64 (n+1)) temporary flags, base + 496) := by
  intro n
  induction n with
  | zero =>
    intro hn temporary flags zero nonzero
    have target := hc.targets ("natDivision_u528", 528) (by decide)
    unfold normalizeScanState
    natdiv_step 127 using hc
    natdiv_step 128 using hc
    simpa [StatusFlags.from_result, target, normalizeScanState, significantCount, Effects.All]
      using zero temporary _ rfl
  | succ n ih =>
    intro hn temporary flags zero nonzero
    have loaded : Mem.loadInt s.dmem (s.regs.r14.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply normalize_scan_step e base hc s temporary _ flags n (by omega) loaded P
    · intro hz flags
      apply ih (by omega) _ flags
      · intro temporary flags empty
        apply zero temporary flags
        simpa [significantCount, hz] using empty
      · intro positive flags
        have positive' : significantCount words (n+1) ≠ 0 := by
          simpa [significantCount, hz] using positive
        simpa [significantCount, hz] using nonzero positive' flags
    · intro hz flags
      have positive : significantCount words (n+1) ≠ 0 := by simp [significantCount, hz]
      simpa [significantCount, hz] using nonzero positive flags

end SszX86.NatDivision
