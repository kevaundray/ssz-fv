import SszX86.NatAddCore

namespace SszX86.NatAdd
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Only the count temporaries are changed by the two leading-zero scans. -/
def countState (s : MachineData) (a x y : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec a
      r10 := UInt64.ofBitVec x
      r11 := UInt64.ofBitVec y}
    status := flags}

private theorem scan_address (p : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 (p.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      p + BitVec.ofNat 64 (8*n) := by
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rw [show BitVec.ofInt 64 8 = 8#64 by decide,
    show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
  bv_omega

/-- One left countdown iteration, including the MOV which retains count+1. -/
theorem left_count_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (x y limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n + 2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (countState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+2)) y flags, base + 32))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (countState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+2)) y flags, base + 53)) :
    Eventually (step e) P
      (countState s (BitVec.ofNat 64 (n+2)) x y flags, base + 32) := by
  have target := hc.targets ("natAdd_u32", 32) (by decide)
  have ne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have dec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  unfold countState
  natadd_step 11 using hc
  natadd_step 12 using hc
  natadd_step 13 using hc
  simp [StatusFlags.from_result, ne, Effects.All]
  natadd_step 14 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, dec]
  natadd_step 15 using hc
  rw [scan_address]
  natadd_load hm
  natadd_step 16 using hc
  by_cases hz : limb = 0#64
  · simpa [StatusFlags.from_result, hz, target, countState, Effects.All] using zero hz _
  · simpa [StatusFlags.from_result, hz, countState, Effects.All] using nonzero hz _

/-- The complete original left list is scanned; no canonical-limb assumption. -/
theorem left_count (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (y : BitVec 64) (words : List (BitVec 64))
    (bound : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ x flags,
    (∀ flags, Eventually (step e) P
      (countState s (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n + 1)) y flags,
        if significantCount words n = 0 then base + 91 else base + 53)) →
    Eventually (step e) P (countState s (BitVec.ofNat 64 (n+1)) x y flags, base + 32) := by
  intro n
  induction n with
  | zero =>
    intro hn x flags next
    have target := hc.targets ("natAdd_u89", 89) (by decide)
    unfold countState
    natadd_step 11 using hc
    natadd_step 12 using hc
    natadd_step 13 using hc
    simp [StatusFlags.from_result, target, Effects.All]
    natadd_step 28 using hc
    constructor <;> simpa [countState, significantCount] using next _
  | succ n ih =>
    intro hn x flags next
    have loaded : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply left_count_step e base hc s x y _ flags n (by omega) loaded P
    · intro hz flags
      apply ih (by omega) _ flags
      intro flags
      simpa [significantCount, hz] using next flags
    · intro hz flags
      simpa [significantCount, hz] using next flags

/-- One right countdown iteration. The descending count is in R10, while R11
retains the new count and RAX keeps the independently established left count. -/
theorem right_count_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a y limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n + 2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (countState s a (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 160))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (countState s a (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 181)) :
    Eventually (step e) P (countState s a (BitVec.ofNat 64 (n+2)) y flags, base + 160) := by
  have target := hc.targets ("natAdd_u160", 160) (by decide)
  have ne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have dec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  unfold countState
  natadd_step 46 using hc
  natadd_step 47 using hc
  simp [StatusFlags.from_result, ne, Effects.All]
  natadd_step 48 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, dec]
  natadd_step 49 using hc
  rw [scan_address]
  natadd_load hm
  natadd_step 50 using hc
  natadd_step 51 using hc
  by_cases hz : limb = 0#64
  · simpa [StatusFlags.from_result, hz, target, countState, Effects.All] using zero hz _
  · simpa [StatusFlags.from_result, hz, countState, Effects.All] using nonzero hz _

/-- A zero significant length exits at the actual empty-right branch; the
positive result exits before the low-byte representation marker is written. -/
theorem right_count (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a : BitVec 64) (words : List (BitVec 64))
    (bound : words.length + 1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ y flags,
    (∀ y flags, significantCount words n = 0 → Eventually (step e) P
      (countState s a 1 y flags, base + 266)) →
    (significantCount words n ≠ 0 → ∀ flags, Eventually (step e) P
      (countState s a (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 181)) →
    Eventually (step e) P (countState s a (BitVec.ofNat 64 (n+1)) y flags, base + 160) := by
  intro n
  induction n with
  | zero =>
    intro hn y flags zero nonzero
    have target := hc.targets ("natAdd_u266", 266) (by decide)
    unfold countState
    natadd_step 46 using hc
    natadd_step 47 using hc
    simpa [StatusFlags.from_result, target, countState, significantCount, Effects.All] using zero y _ rfl
  | succ n ih =>
    intro hn y flags zero nonzero
    have loaded : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply right_count_step e base hc s a y _ flags n (by omega) loaded P
    · intro hz flags
      apply ih (by omega) _ flags
      · intro y flags empty
        apply zero y flags
        simpa [significantCount, hz] using empty
      · intro positive flags
        have positive' : significantCount words (n+1) ≠ 0 := by
          simpa [significantCount, hz] using positive
        simpa [significantCount, hz] using nonzero positive' flags
    · intro hz flags
      have positive : significantCount words (n+1) ≠ 0 := by simp [significantCount, hz]
      simpa [significantCount, hz] using nonzero positive flags

end SszX86.NatAdd
