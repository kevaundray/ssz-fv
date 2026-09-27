import SszX86.NatAddCore

namespace SszX86.NatAdd
open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def rightNormalizeState (s : MachineData) (a v : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec a
      r8 := UInt64.ofBitVec v}
    status := flags}

private theorem scan_address (p : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 (p.toInt + (BitVec.ofNat 64 (n+2)).toInt * 8 + (-16)) =
      p + BitVec.ofNat 64 (8*n) := by
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rw [show BitVec.ofInt 64 8 = 8#64 by decide,
    show BitVec.ofInt 64 (-16) = 18446744073709551600#64 by decide]
  bv_omega

theorem right_normalize_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (v limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n+2 < 2^64)
    (hm : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
      some (limb.toNat : Int)) (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (rightNormalizeState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 352))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (rightNormalizeState s (BitVec.ofNat 64 (n+1)) (BitVec.ofNat 64 (n+1)) flags, base + 377)) :
    Eventually (step e) P (rightNormalizeState s (BitVec.ofNat 64 (n+2)) v flags, base + 352) := by
  have target := hc.targets ("natAdd_u352", 352) (by decide)
  have ne : BitVec.ofNat 64 (n+2) ≠ 1#64 := by bv_omega
  have dec : BitVec.ofNat 64 (n+2) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n+1) := by bv_omega
  unfold rightNormalizeState
  natadd_step 95 using hc
  natadd_step 96 using hc
  simp [StatusFlags.from_result, ne, Effects.All]
  natadd_step 97 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, dec]
  natadd_step 98 using hc
  rw [scan_address]
  natadd_load hm
  natadd_step 99 using hc
  natadd_step 100 using hc
  by_cases hz : limb = 0#64
  · simpa [StatusFlags.from_result, hz, target, rightNormalizeState, Effects.All] using zero hz _
  · simpa [StatusFlags.from_result, hz, rightNormalizeState, Effects.All] using nonzero hz _

/-- The actual borrowed-right rescan includes empty Large and all-zero lists. -/
theorem right_normalize_scan (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length+1 < 2^64)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int)) (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ v flags,
    (∀ v flags, significantCount words n = 0 → Eventually (step e) P
      (rightNormalizeState s 1 v flags, base + 562)) →
    (significantCount words n ≠ 0 → ∀ flags, Eventually (step e) P
      (rightNormalizeState s (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 377)) →
    Eventually (step e) P (rightNormalizeState s (BitVec.ofNat 64 (n+1)) v flags, base + 352) := by
  intro n
  induction n with
  | zero =>
    intro hn v flags zero nonzero
    have target := hc.targets ("natAdd_u562", 562) (by decide)
    unfold rightNormalizeState
    natadd_step 95 using hc
    natadd_step 96 using hc
    simpa [StatusFlags.from_result, target, rightNormalizeState, significantCount, Effects.All]
      using zero v _ rfl
  | succ n ih =>
    intro hn v flags zero nonzero
    have loaded : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using hm ⟨n, by omega⟩
    apply right_normalize_step e base hc s v _ flags n (by omega) loaded P
    · intro hz flags
      apply ih (by omega) _ flags
      · intro v flags empty
        apply zero v flags
        simpa [significantCount, hz] using empty
      · intro positive flags
        have positive' : significantCount words (n+1) ≠ 0 := by
          simpa [significantCount, hz] using positive
        simpa [significantCount, hz] using nonzero positive' flags
    · intro hz flags
      have positive : significantCount words (n+1) ≠ 0 := by simp [significantCount, hz]
      simpa [significantCount, hz] using nonzero positive flags

def rightPairState (s : MachineData) (a p v : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec a
      rcx := UInt64.ofBitVec p
      r8 := UInt64.ofBitVec v}
    status := flags}

theorem right_normalize_publish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a : BitVec 64) (limbs : List (BitVec 64)) (flags : StatusFlags)
    (count : Nat) (positive : 0 < count) (bound : count < 2^64)
    (hm : count = 1 → Mem.loadInt s.dmem s.regs.rcx.toBitVec 8 =
      some ((limbs[0]?.getD 0#64).toNat : Int)) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (rightPairState s a (if count = 1 then 0 else s.regs.rcx.toBitVec)
        (if count = 1 then limbs[0]?.getD 0 else BitVec.ofNat 64 count) flags, base + 585)) :
    Eventually (step e) P (rightNormalizeState s a (BitVec.ofNat 64 count) flags, base + 377) := by
  have target := hc.targets ("natAdd_u585", 585) (by decide)
  unfold rightNormalizeState
  natadd_step 101 using hc
  natadd_step 102 using hc
  by_cases one : count = 1
  · have oneWord : BitVec.ofNat 64 count = 1#64 := by simp [one]
    simp [StatusFlags.from_result, oneWord, Effects.All]
    natadd_step 103 using hc
    natadd_load (hm one)
    natadd_step 104 using hc
    constructor <;> natadd_step 105 using hc
    all_goals simpa [rightPairState, one] using next _
  · have notOne : BitVec.ofNat 64 count ≠ 1#64 := by bv_omega
    simpa [StatusFlags.from_result, notOne, target, rightPairState, one, Effects.All] using next _

theorem right_normalize_zero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (rightPairState s s.regs.rax.toBitVec 0 0 flags, base + 585)) :
    Eventually (step e) P (s, base + 562) := by
  natadd_step 144 using hc
  constructor <;> natadd_step 145 using hc
  all_goals constructor <;> natadd_step 146 using hc
  all_goals simpa [rightPairState] using next _

end SszX86.NatAdd
