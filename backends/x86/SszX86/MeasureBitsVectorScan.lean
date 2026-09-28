import SszX86.MeasureOwned
import SszX86.NatFromU128Core

namespace SszX86.Measure.Bits
open SszNative.Limbs


/-- Only the scan cursor, temporary count, and flags change. In particular the
entire descriptor buffer, rather than just its significant prefix, is retained. -/
def normalizeScanState (s : MachineData) (count temporary : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r9 := UInt64.ofBitVec count
      r10 := UInt64.ofBitVec temporary}
    status := flags}

@[simp] theorem normalizeScanState_initial (s : MachineData) :
    normalizeScanState s s.regs.r9.toBitVec s.regs.r10.toBitVec s.status = s := by
  cases s with | mk regs zmms status dmem => cases regs <;> rfl

private theorem normalize_scan_address (p : BitVec 64) (n : Nat) :
    p + BitVec.ofNat 64 (n+2) * 8#64 + 18446744073709551600#64 =
      p + BitVec.ofNat 64 (8*n) := by
  bv_omega

/-- Keep the memory comparison and its two successor states opaque to the
count/LEA prefix, so flag construction is simplified only once per phase. -/
private theorem normalize_scan_limb_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (P : MachineState → Prop)
    (loaded : Mem.loadInt s.dmem
      (s.regs.r8.toBitVec + s.regs.r9.toBitVec * 8#64 + 18446744073709551600#64) 8 =
        some (limb.toNat : Int))
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r9 := s.regs.r10}, status := flags}, base + 128))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r9 := s.regs.r10}, status := flags}, base + 153)) :
    Eventually (step e) P (s, base + 142) := by
  have target := hc.targets ("measure_u128", 128) (by decide)
  measure_step 32 using hc
  natfrom_load loaded
  measure_step 33 using hc
  measure_step 34 using hc
  by_cases zeroLimb : limb = 0#64
  · simpa [StatusFlags.from_result, zeroLimb, target, Effects.All] using zero zeroLimb _
  · simpa [StatusFlags.from_result, zeroLimb, Effects.All] using nonzero zeroLimb _

private theorem normalize_scan_count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (ne : s.regs.r9.toBitVec ≠ 1#64)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 138)) :
    Eventually (step e) P (s, base + 128) := by
  measure_step 29 using hc
  measure_step 30 using hc
  simpa [StatusFlags.from_result, ne, Effects.All] using next _

private theorem normalize_scan_lea_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with
        r10 := UInt64.ofBitVec (s.regs.r9.toBitVec + BitVec.ofInt 64 (-1))}}, base + 142)) :
    Eventually (step e) P (s, base + 138) := by
  measure_step 31 using hc
  exact next

theorem normalize_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (temporary limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n+2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (normalizeScanState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 128))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (normalizeScanState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 153)) :
    Eventually (step e) P
      (normalizeScanState s (BitVec.ofNat 64 (n+2)) temporary flags, base + 128) := by
  have ne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have dec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  apply normalize_scan_count_cps e base hc _ P (by exact ne)
  intro countFlags
  apply normalize_scan_lea_cps e base hc _ P
  apply normalize_scan_limb_cps e base hc _ limb P
  · change Mem.loadInt s.dmem
      (s.regs.r8.toBitVec + BitVec.ofNat 64 (n+2) * 8#64 + 18446744073709551600#64) 8 =
        some (limb.toNat : Int)
    rw [normalize_scan_address s.regs.r8.toBitVec n]
    exact hm
  · intro zeroLimb finalFlags
    simpa only [normalizeScanState, dec] using zero zeroLimb finalFlags
  · intro nonzeroLimb finalFlags
    simpa only [normalizeScanState, dec] using nonzero nonzeroLimb finalFlags

/-- The real backward loop exits with exactly significantCount, also when every
stored descriptor limb is zero. It does not mutate or shrink the stored list. -/
theorem normalize_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length+1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ temporary flags,
    (∀ temporary flags, significantCount words n = 0 → Eventually (step e) P
      (normalizeScanState s 1 temporary flags, base + 1854)) →
    (significantCount words n ≠ 0 → ∀ flags, Eventually (step e) P
      (normalizeScanState s (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 153)) →
    Eventually (step e) P
      (normalizeScanState s (BitVec.ofNat 64 (n+1)) temporary flags, base + 128) := by
  intro n
  induction n with
  | zero =>
    intro hn temporary flags zero nonzero
    have target := hc.targets ("measure_u1854", 1854) (by decide)
    unfold normalizeScanState
    measure_step 29 using hc
    measure_step 30 using hc
    simpa [StatusFlags.from_result, target, normalizeScanState, significantCount, Effects.All]
      using zero temporary _ rfl
  | succ n ih =>
    intro hn temporary flags zero nonzero
    have loaded : Mem.loadInt s.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
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

end SszX86.Measure.Bits
