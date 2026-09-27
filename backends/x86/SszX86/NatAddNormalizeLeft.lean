import SszX86.NatAddCore

namespace SszX86.NatAdd
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def leftNormalizeState (s : MachineData) (a d : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec a
      rdx := UInt64.ofBitVec d}
    status := flags}

private theorem scan_address (p : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 (p.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      p + BitVec.ofNat 64 (8*n) := by
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rw [show BitVec.ofInt 64 8 = 8#64 by decide,
    show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
  bv_omega

theorem left_normalize_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (d limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n+2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (leftNormalizeState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 288))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (leftNormalizeState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 313)) :
    Eventually (step e) P (leftNormalizeState s (BitVec.ofNat 64 (n+2)) d flags, base + 288) := by
  have target := hc.targets ("natAdd_u288", 288) (by decide)
  have ne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have dec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  unfold leftNormalizeState
  natadd_step 80 using hc
  natadd_step 81 using hc
  simp [StatusFlags.from_result, ne, Effects.All]
  natadd_step 82 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, dec]
  natadd_step 83 using hc
  rw [scan_address]
  natadd_load hm
  natadd_step 84 using hc
  natadd_step 85 using hc
  by_cases hz : limb = 0#64
  · simpa [StatusFlags.from_result, hz, target, leftNormalizeState, Effects.All] using zero hz _
  · simpa [StatusFlags.from_result, hz, leftNormalizeState, Effects.All] using nonzero hz _

/-- Rescanning the borrowed left input is required on the zero-right branch. -/
theorem left_normalize_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length+1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ d flags,
    (∀ d flags, significantCount words n = 0 → Eventually (step e) P
      (leftNormalizeState s 1 d flags, base + 594)) →
    (significantCount words n ≠ 0 → ∀ flags, Eventually (step e) P
      (leftNormalizeState s (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 313)) →
    Eventually (step e) P (leftNormalizeState s (BitVec.ofNat 64 (n+1)) d flags, base + 288) := by
  intro n
  induction n with
  | zero =>
    intro hn d flags zero nonzero
    have target := hc.targets ("natAdd_u594", 594) (by decide)
    unfold leftNormalizeState
    natadd_step 80 using hc
    natadd_step 81 using hc
    simpa [StatusFlags.from_result, target, leftNormalizeState, significantCount, Effects.All]
      using zero d _ rfl
  | succ n ih =>
    intro hn d flags zero nonzero
    have loaded : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply left_normalize_step e base hc s d _ flags n (by omega) loaded P
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

/-- Canonical left pair formed by the post-scan one-word and multiword cases. -/
def leftPairState (s : MachineData) (a p d : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec a
      rsi := UInt64.ofBitVec p
      rdx := UInt64.ofBitVec d}
    status := flags}

theorem left_normalize_publish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a : BitVec 64) (limbs : List (BitVec 64)) (flags : StatusFlags)
    (count : Nat) (positive : 0 < count) (bound : count < 2^64)
    (hm : count = 1 → Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 =
      some ((limbs[0]?.getD 0#64).toNat : Int)) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (leftPairState s a (if count = 1 then 0 else s.regs.rsi.toBitVec)
        (if count = 1 then limbs[0]?.getD 0 else BitVec.ofNat 64 count) flags, base + 598)) :
    Eventually (step e) P (leftNormalizeState s a (BitVec.ofNat 64 count) flags, base + 313) := by
  have target := hc.targets ("natAdd_u598", 598) (by decide)
  unfold leftNormalizeState
  natadd_step 86 using hc
  natadd_step 87 using hc
  by_cases one : count = 1
  · have oneWord : BitVec.ofNat 64 count = 1#64 := by simp [one]
    simp [StatusFlags.from_result, oneWord, Effects.All]
    natadd_step 88 using hc
    natadd_load (hm one)
    natadd_step 89 using hc
    constructor <;> natadd_step 90 using hc
    all_goals simpa [leftPairState, one] using next _
  · have notOne : BitVec.ofNat 64 count ≠ 1#64 := by bv_omega
    simpa [StatusFlags.from_result, notOne, target, leftPairState, one, Effects.All] using next _

theorem left_normalize_zero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (leftPairState s s.regs.rax.toBitVec 0 0 flags, base + 598)) :
    Eventually (step e) P (s, base + 594) := by
  natadd_step 153 using hc
  constructor <;> natadd_step 154 using hc
  all_goals constructor <;> simpa [leftPairState] using next _

end SszX86.NatAdd
